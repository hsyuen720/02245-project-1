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
            let ivl = cmd_to_ivlcmd(cmd);

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

            // Add an explicit postcondition check at the end
            // This ensures errors point to the ensures clause
            let postcond_check = if m.ensures().count() > 0 {
                let first_ensure = m.ensures().next().unwrap();
                let mut check = IVLCmd::assert(&post, "Postcondition might not hold");
                check.span = first_ensure.span;
                IVLCmd::seq(&ivl, &check)
            } else {
                ivl
            };

            let (oblig, msg, err_span) = wp(&postcond_check, &Expr::bool(true));
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
                        cx.error(err_span, msg.to_string());
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(err_span, format!("{msg}: unknown sat result"));
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
fn cmd_to_ivlcmd(cmd: &Cmd) -> IVLCmd {
    match &cmd.kind {
        CmdKind::Assert { condition, .. } => IVLCmd::assert(condition, "Assert might fail!"),
        CmdKind::Seq(first, second) => {
            IVLCmd::seq(&cmd_to_ivlcmd(first), &cmd_to_ivlcmd(second))
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
                let lowered = cmd_to_ivlcmd(&case.cmd);
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
            let assert_inv_init = IVLCmd::assert(&inv, "Loop invariant may not hold on entry");

            // Step 2: Verify invariant is preserved by checking each branch
            // Start by assuming the invariant holds
            let assume_inv_for_body = IVLCmd::assume(&inv);
            
            // Build nondeterministic choice for all branches
            let mut preservation_branches: Vec<IVLCmd> = Vec::new();
            for case in &body.cases {
                // For each branch: assume guard, execute body, assert invariant
                let assume_guard = IVLCmd::assume(&case.condition);
                let body_encoded = cmd_to_ivlcmd(&case.cmd);
                let assert_inv_after = IVLCmd::assert(&inv, "Loop invariant may not be preserved");
                
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
        _ => todo!("Not supported (yet)."),
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
            // If c1 has an error message, use it; otherwise use c2's
            if !msg1.is_empty() {
                (result, msg1, span1)
            } else {
                (result, msg2, span2)
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
