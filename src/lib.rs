pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr};
use slang::Span;
use slang_ui::prelude::*;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Iterate methods
        for m in file.methods() {
            // Get method's preconditions;
            let pres = m.requires();
            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression
            let spre = pre.smt(cx.smt_st())?;
            // Assert precondition
            solver.assert(spre.as_bool()?)?;

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd, file);

            let post0 = m
                .ensures()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));

            let post = if let Some((_, ret_ty)) = &m.return_ty {
                let ret_ty = ret_ty.clone();
                let ret_expr = Expr::ident("ret", &ret_ty);
                post0.subst_result(&ret_expr)
                } else {
                    post0
                };

            // Use the original command without adding an explicit postcondition check
            // The postcondition is checked through the wp calculation
            let ivl_with_postcheck = ivl;

            let (oblig, msg, err_span) = wp(&ivl_with_postcheck, &post);
            
            // If there's no error message, it means the postcondition failed
            // In that case, use the ensures clause span
            let (final_msg, final_span) = if msg.is_empty() && m.ensures().count() > 0 {
                ("Postcondition might not hold".to_string(), m.ensures().next().unwrap().span)
            } else {
                (msg, err_span)
            };
            
            // Convert obligation to SMT expression
            let soblig = oblig.smt(cx.smt_st())?;

            // Run the following solver-related statements in a closed scope.
            // That is, after exiting the scope, all assertions are forgotten
            // from subsequent executions of the solver
            solver.scope(|solver| {
                // Check validity of obligation
                solver.assert(!soblig.as_bool()?)?;
                // Run SMT solver on all current assertions
                match solver.check_sat()? {
                    // If the obligations result not valid, report the error (on
                    // the span in which the error happens)
                    smtlib::SatResult::Sat => {
                        cx.error(final_span, final_msg.to_string());
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(final_span, format!("{final_msg}: unknown sat result"));
                    }
                    smtlib::SatResult::Unsat => (),
                }
                Ok(())
            })?;
        }

        Ok(())
    }
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd, file: &slang::SourceFile) -> IVLCmd {
    match &cmd.kind {
        CmdKind::Assert { condition, .. } => IVLCmd::assert(condition, "Assert might fail!"),
        CmdKind::Seq(first, second) => {
            IVLCmd::seq(&cmd_to_ivlcmd(first, file), &cmd_to_ivlcmd(second, file))
        },
        CmdKind::Assume { condition } => IVLCmd::assume(condition),
        CmdKind::Assignment { name, expr } => IVLCmd::assign(name, expr),
        CmdKind::VarDefinition { name, ty, expr } => {
            let ty = &ty.1;

            let decl = IVLCmd::havoc(name, ty);

            if let Some(init_expr) = expr {
                let assign = IVLCmd::assign(name, init_expr);
                IVLCmd::seq(&decl, &assign)
            } else {
                decl
            }
        },
        CmdKind::Match { body } => {
            let mut branches: Vec<IVLCmd> = Vec::new();

            for case in &body.cases {
                let assume  = IVLCmd::assume(&case.condition);
                let lowered = cmd_to_ivlcmd(&case.cmd, file);
                let branch  = IVLCmd::seq(&assume, &lowered);
                branches.push(branch);
            }

            IVLCmd::nondets(&branches)
        },
        CmdKind::Return { expr } => {
            match expr {
                Some(init_expression) => {
                    let ret_name = slang::ast::Name { ident: "ret".to_string(), span: init_expression.span };
                    let assign: IVLCmd   = IVLCmd::assign(&ret_name, init_expression);
                    IVLCmd::nondet(&assign, &IVLCmd::unreachable())
                }
                None => IVLCmd::unreachable(),
            }
        },
        CmdKind::Loop { invariants, body, .. } => {
            // Merge all invariants into a single expression
            let inv = invariants
                .iter()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));

            // Step 1: Assert invariant holds initially
            let mut assert_inv_init = IVLCmd::assert(&inv, "Loop invariant may not hold on entry");
            // Set span to first user-provided invariant if available
            if let Some(first_inv) = invariants.first() {
                assert_inv_init.span = first_inv.span;
            }

            // Step 2: Verify invariant is preserved by checking each branch
            // Start by assuming the invariant holds
            let assume_inv_for_body = IVLCmd::assume(&inv);
            
            // Build nondeterministic choice for all branches
            let mut preservation_branches: Vec<IVLCmd> = Vec::new();
            for case in &body.cases {
                // For each branch: assume guard, execute body, assert invariant
                let assume_guard = IVLCmd::assume(&case.condition);
                let body_encoded = cmd_to_ivlcmd(&case.cmd, file);
                let mut assert_inv_after = IVLCmd::assert(&inv, "Loop invariant may not be preserved");
                // Set span to first user-provided invariant if available
                if let Some(first_inv) = invariants.first() {
                    assert_inv_after.span = first_inv.span;
                }
                
                let branch = IVLCmd::seq(&assume_guard,
                    &IVLCmd::seq(&body_encoded, &assert_inv_after));
                preservation_branches.push(branch);
            }
            let preservation_check = IVLCmd::nondets(&preservation_branches);
            let verify_preservation = IVLCmd::seq(&assume_inv_for_body, &preservation_check);

            // Step 3: After loop - assume invariant and all guards are false
            let all_guards_false = body.cases
                .iter()
                .map(|case| !case.condition.clone())
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            let after_loop = IVLCmd::seq(&IVLCmd::assume(&inv), &IVLCmd::assume(&all_guards_false));

            // Final encoding: assert I; (assume I; check preservation); assume I ∧ ¬guards
            IVLCmd::seq(&assert_inv_init, &IVLCmd::seq(&verify_preservation, &after_loop))
        },
        CmdKind::For { name, range, invariants, body, .. } => {
            // Bounded for-loop: for name in range { body }
            // For Extension Feature 1, we unroll the loop completely
            // For Extension Feature 4, we use invariant-based encoding when bounds are not literals
            
            // Extract start and end from range
            let (start, end) = match range {
                slang::ast::Range::FromTo(s, e) => (s, e),
            };
            
            // Get the type of the loop variable (should be Int)
            let ty = slang::ast::Type::Int;
            
            // Try to determine if we can unroll (both bounds are numeric literals)
            let start_val_opt = match &start.kind {
                slang::ast::ExprKind::Num(n) => Some(*n),
                _ => None,
            };
            
            let end_val_opt = match &end.kind {
                slang::ast::ExprKind::Num(n) => Some(*n),
                _ => None,
            };
            
            // If either bound is not a literal, use invariant-based encoding
            if start_val_opt.is_none() || end_val_opt.is_none() {
                // Extension Feature 4: unbounded for-loops with invariant-based verification
                // Initialize loop variable: name := start
                let init = IVLCmd::assign(name, start);
                
                // Build the loop invariants with implicit bounds
                let loop_var = Expr::ident(&name.ident, &ty);
                let lower_bound = loop_var.clone().ge(start);
                let upper_bound = loop_var.clone().le(end);
                let implicit_inv = lower_bound & upper_bound;
                
                let user_inv = invariants
                    .iter()
                    .cloned()
                    .reduce(|a, b| a & b)
                    .unwrap_or(Expr::bool(true));
                let inv = implicit_inv & user_inv;
                
                // Build loop body with guard and increment
                // Guard: i < end (continue looping)
                let guard = loop_var.clone().lt(end);
                let one = Expr::new_typed(slang::ast::ExprKind::Num(1), ty.clone());
                let body_encoded = cmd_to_ivlcmd(&body.cmd, file);
                let increment = IVLCmd::assign(name, &(loop_var.clone() + one));
                let loop_body_with_increment = IVLCmd::seq(&body_encoded, &increment);
                
                // Standard loop encoding (similar to unbounded loop)
                // 1. Assert invariant holds initially
                let mut assert_inv_init = IVLCmd::assert(&inv, "For-loop invariant may not hold on entry");
                // Set span to first user-provided invariant if available
                if let Some(first_inv) = invariants.first() {
                    assert_inv_init.span = first_inv.span;
                }
                
                // 2. Verify preservation: assume I, assume guard, execute body+increment, assert I
                let assume_inv = IVLCmd::assume(&inv);
                let assume_guard = IVLCmd::assume(&guard);
                let body_with_assumption = IVLCmd::seq(&assume_guard, &loop_body_with_increment);
                let mut assert_inv_after = IVLCmd::assert(&inv, "For-loop invariant may not be preserved");
                // Set span to first user-provided invariant if available
                if let Some(first_inv) = invariants.first() {
                    assert_inv_after.span = first_inv.span;
                }
                let preservation_check = IVLCmd::seq(&body_with_assumption, &assert_inv_after);
                let verify_preservation = IVLCmd::seq(&assume_inv, &preservation_check);
                
                // 3. After loop: assume invariant and guard is false (i >= end)
                let neg_guard = !guard;
                let after_loop = IVLCmd::seq(&IVLCmd::assume(&inv), &IVLCmd::assume(&neg_guard));
                
                // Combine: init; assert I; (assume I; verify preservation); (assume I ∧ ¬guard)
                let loop_encoding = IVLCmd::seq(&assert_inv_init, &IVLCmd::seq(&verify_preservation, &after_loop));
                return IVLCmd::seq(&init, &loop_encoding);
            }
            
            // Extension Feature 1: bounded for-loops (unrolling)
            let start_val = start_val_opt.unwrap();
            let end_val = end_val_opt.unwrap();
            
            // Unroll the loop: for i = start_val; i < end_val; i++ { body }
            let mut result = IVLCmd::nop();
            
            for i in start_val..end_val {
                // Create literal expression for current iteration value
                let i_expr = Expr::new_typed(slang::ast::ExprKind::Num(i), ty.clone());
                
                // Assign loop variable: name := i
                let assign_i = IVLCmd::assign(name, &i_expr);
                
                // Execute body
                let body_encoded = cmd_to_ivlcmd(&body.cmd, file);
                
                // Sequence: name := i; body
                let iteration = IVLCmd::seq(&assign_i, &body_encoded);
                
                // Chain iterations together
                result = IVLCmd::seq(&result, &iteration);
            }
            
            // After all iterations, set loop variable to end_val
            let final_expr = Expr::new_typed(slang::ast::ExprKind::Num(end_val), ty.clone());
            let final_assign = IVLCmd::assign(name, &final_expr);
            IVLCmd::seq(&result, &final_assign)
        },
        CmdKind::MethodCall { name, fun_name, args, method: _ } => {
            // Handle method calls by:
            // 1. Assert preconditions hold (with arguments substituted)
            // 2. Havoc return variable (if any)
            // 3. Assume postconditions hold (with arguments and result substituted)
            
            // Find the called method in the source file
            let methods = file.methods();
            let called_method = methods
                .iter()
                .find(|m| m.name.ident == fun_name.ident)
                .expect("Method not found");
            
            // Get parameters from the called method
            let params: Vec<_> = called_method.args.iter().collect();
            
            // Build precondition checks
            // Substitute formal parameters with actual arguments
            let mut precond_cmd = IVLCmd::nop();
            
            for pre_cond in called_method.requires() {
                let mut substituted_pre = pre_cond.clone();
                
                // Substitute each parameter with its corresponding argument
                for (param, arg) in params.iter().zip(args.iter()) {
                    substituted_pre = substituted_pre.subst_ident(&param.name.ident, arg);
                }
                
                // Assert the precondition holds
                // Use the span of the method call (fun_name) for error reporting
                let mut assert_pre = IVLCmd::assert(&substituted_pre, "Method precondition might not hold");
                assert_pre.span = fun_name.span;
                precond_cmd = IVLCmd::seq(&precond_cmd, &assert_pre);
            }
            
            // Handle return value if present
            let ret_cmd = if let Some(ret_name) = name {
                // Get return type from method signature
                let ret_ty = if let Some((_, ty)) = &called_method.return_ty {
                    ty.clone()
                } else {
                    panic!("Method call assigned to variable but method has no return type");
                };
                
                // Havoc the return variable
                let havoc_ret = IVLCmd::havoc(ret_name, &ret_ty);
                
                // Build postcondition assumptions
                // Substitute formal parameters with actual arguments AND result with return variable
                let mut postcond_cmd = havoc_ret;
                
                for post_cond in called_method.ensures() {
                    let mut substituted_post = post_cond.clone();
                    
                    // Substitute each parameter with its corresponding argument
                    for (param, arg) in params.iter().zip(args.iter()) {
                        substituted_post = substituted_post.subst_ident(&param.name.ident, arg);
                    }
                    
                    // Substitute 'result' with the return variable
                    let ret_expr = Expr::ident(&ret_name.ident, &ret_ty);
                    substituted_post = substituted_post.subst_result(&ret_expr);
                    
                    // Assume the postcondition holds
                    let assume_post = IVLCmd::assume(&substituted_post);
                    postcond_cmd = IVLCmd::seq(&postcond_cmd, &assume_post);
                }
                
                postcond_cmd
            } else {
                // No return value - just assume postconditions
                let mut postcond_cmd = IVLCmd::nop();
                
                for post_cond in called_method.ensures() {
                    let mut substituted_post = post_cond.clone();
                    
                    // Substitute each parameter with its corresponding argument
                    for (param, arg) in params.iter().zip(args.iter()) {
                        substituted_post = substituted_post.subst_ident(&param.name.ident, arg);
                    }
                    
                    // Assume the postcondition holds
                    let assume_post = IVLCmd::assume(&substituted_post);
                    postcond_cmd = IVLCmd::seq(&postcond_cmd, &assume_post);
                }
                
                postcond_cmd
            };
            
            // Sequence: assert preconditions, then havoc+assume postconditions
            IVLCmd::seq(&precond_cmd, &ret_cmd)
        },
        _ => {
            eprintln!("Unsupported command kind: {:?}", cmd.kind);
            todo!("Not supported (yet).")
        },
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion. Returns (obligation, error_message, error_span)
fn wp(ivl: &IVLCmd, post: &Expr) -> (Expr, String, Span) {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => {
            (condition.clone() & post.clone(), message.clone(), ivl.span)
        },
        IVLCmdKind::Seq(c1, c2) => {
            let (new_post, msg2, span2) = wp(c2, post);
            let (result, msg1, span1) = wp(c1, &new_post);
            // Prefer c2's error message if it exists (it's later in execution)
            // Otherwise use c1's error message
            if !msg2.is_empty() {
                (result, msg2, span2)
            } else {
                (result, msg1, span1)
            }
        },
        IVLCmdKind::Assume { condition } => {
            (!condition.clone() | post.clone(), String::new(), Span::default())
        },
        IVLCmdKind::Assignment { name, expr } => {
            (post.clone().subst_ident(&name.ident, expr), String::new(), Span::default())
        },
        IVLCmdKind::Havoc { name, ty } => {
            let ident_name = name.as_str();
            let ident_e = Expr::ident(&ident_name, ty);
            let q = post.subst_ident(&name.ident, &ident_e);
            (q, String::new(), Span::default())
        }
        IVLCmdKind::NonDet(cmd1, cmd2) => {
            let (expr1, msg1, span1) = wp(&cmd1, post);
            let (expr2, msg2, span2) = wp(&cmd2, post);

            // For nondeterministic choice, use the first error message/span if available
            let (msg, span) = if !msg1.is_empty() {
                (msg1, span1)
            } else {
                (msg2, span2)
            };
            
            (expr1 & expr2, msg, span)
        },
    }
}
