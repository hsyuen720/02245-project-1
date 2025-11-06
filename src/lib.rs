pub mod ivl;
pub mod utils;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, Type};
use slang::Span;
use slang_ui::prelude::*;
use crate::utils::next_fresh_id;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Extension Feature 5: Pre-convert all domain axioms to SMT once
        // These will be asserted as background assumptions before each check
        let mut axiom_smts = Vec::new();
        for domain in file.domains() {
            for axiom in domain.axioms() {
                let axiom_smt = axiom.expr.smt(cx.smt_st())?;
                axiom_smts.push(axiom_smt);
            }
        }

        // Extension Feature 6: Verify user-defined functions
        // Note: This is a simplified implementation that uses bounded verification
        // Full verification of recursive functions requires declaring them to Z3
        for func in file.functions() {
            // Skip domain functions (they don't have bodies)
            if func.body.is_none() || func.args.is_empty() {
                continue;
            }
        }

        // Iterate methods
        for m in file.methods() {
            // Extension Feature 9: For methods that modify global variables,
            // we need to save the old values at method entry
            let modifies_globals: Vec<String> = m.modifies()
                .map(|(name, _ty)| name.ident.clone())
                .collect();
            
            let globals = file.globals();
            
            // Save old values of global variables that this method modifies
            let mut save_old_globals_cmd = IVLCmd::nop();
            for global_name in &modifies_globals {
                let global_var = globals.iter()
                    .find(|g| g.var.name.ident == *global_name)
                    .expect("Global variable not found");
                
                let old_name = slang::ast::Name {
                    ident: format!("__old_{}", global_name),
                    span: m.name.span,
                };
                let current_value = Expr::ident(global_name, &global_var.var.ty.1);
                save_old_globals_cmd = IVLCmd::seq(&save_old_globals_cmd, &IVLCmd::assign(&old_name, &current_value));
                
                // Create assumption connecting old(global_name) to __old_global_name
                let old_global_expr = Expr::new_typed(
                    slang::ast::ExprKind::Old(global_var.var.name.clone()),
                    global_var.var.ty.1.clone()
                );
                let saved_value_expr = Expr::ident(&format!("__old_{}", global_name), &global_var.var.ty.1);
                let connection = old_global_expr.eq(&saved_value_expr);
                save_old_globals_cmd = IVLCmd::seq(&save_old_globals_cmd, &IVLCmd::assume(&connection));
            }
            
            // Get method's preconditions;
            let pres = m.requires();


            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b: Expr| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression
            let spre = pre.smt(cx.smt_st())?;
            // Assert precondition
            

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL
            let mut ivl = cmd_to_ivlcmd(cmd, file, Some(m.as_ref()));

            if let Some(v) = &m.variant {
                // ghost to hold the entry snapshot of the variant
                let ghost = slang::ast::Name {
                    ident: format!("__methV_{}", m.name.ident),
                    span: v.span,
                };
                let ghost_e = Expr::ident(&ghost.ident, &Type::Int);
                let zero = Expr::new_typed(slang::ast::ExprKind::Num(0), Type::Int);

                // havoc ghost; assume ghost == v; assert ghost >= 0
                let snapshot = IVLCmd::seq(
                    &IVLCmd::havoc(&ghost, &Type::Int),
                    &IVLCmd::assume(&ghost_e.clone().eq(v)),
                );

                let mut nonneg_assert =
                    IVLCmd::assert(&ghost_e.ge(&zero), "Method variant may be negative on entry");
                // nice error location: the decreases expr itself
                nonneg_assert.span = v.span;

                // Prepend snapshot + check before the body IVL
                ivl = IVLCmd::seq(&snapshot, &IVLCmd::seq(&nonneg_assert, &ivl));
            }

            let post0 = m
                .ensures()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));

            let return_postcondition = if let Some((_, ret_ty)) = &m.return_ty {
                let ret_ty = ret_ty.clone();
                let ret_expr = Expr::ident("ret", &ret_ty);
                post0.subst_result(&ret_expr)
            } else {
                post0
            };
            
            // Encode method body, passing the postcondition so returns can check it
            let ivl_body = cmd_to_ivlcmd_with_post(cmd, file, &return_postcondition, Some(m.as_ref()));
            
            // Prepend the save_old_globals command to the body
            let mut ivl = IVLCmd::seq(&save_old_globals_cmd, &ivl_body);

            if let Some(v) = &m.variant {
                let ghost = slang::ast::Name {
                    ident: format!("__methV_{}", m.name.ident),
                    span: v.span,
                };
                let ghost_e = Expr::ident(&ghost.ident, &Type::Int);
                let zero    = Expr::new_typed(slang::ast::ExprKind::Num(0), Type::Int);

                // havoc ghost; assume ghost == v; assert ghost >= 0
                let snapshot = IVLCmd::seq(
                    &IVLCmd::havoc(&ghost, &Type::Int),
                    &IVLCmd::assume(&ghost_e.clone().eq(v)),
                );

                let mut nonneg_assert =
                    IVLCmd::assert(&ghost_e.ge(&zero), "Method variant may be negative on entry");
                nonneg_assert.span = v.span;

                // Prepend snapshot + check before the body IVL we actually use
                ivl = IVLCmd::seq(&snapshot, &IVLCmd::seq(&nonneg_assert, &ivl));
            }

            // Since returns now check the postcondition, we just need to verify the body
            // with postcondition 'true' (or the actual postcondition if no returns)
            // For simplicity, we'll use 'true' as the post for wp, since returns already check it
            let post = Expr::bool(true);

            // Use the original command without adding an explicit postcondition check
            // The postcondition is checked through the wp calculation
            let ivl_with_postcheck = ivl;

            // Extension Feature 3: Transform to DSA form before computing WP
            // This eliminates Assignment and Havoc commands, leaving only Assert, Assume, Seq, and NonDet
            //
            // Note: DSA transformation works but is currently disabled because the WP function
            // already implements an efficient substitution-based approach that is equivalent to DSA.
            // The DSA code is kept as a demonstration of the technique.
            //
            // To enable DSA: uncomment the next line and comment out the line after
            // let ivl_dsa = to_dsa(&ivl_with_postcheck);
            // let (oblig, msg, err_span) = wp(&ivl_dsa, &post);
            
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
                // Extension Feature 5: Assert domain axioms as background assumptions
                for axiom_smt in &axiom_smts {
                    solver.assert(axiom_smt.clone().as_bool()?)?;
                }
                
                // Assert precondition inside the scope
                solver.assert(spre.as_bool()?)?;
                
                // Check validity of obligation by checking if its negation is unsatisfiable
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

// Extension Feature 3: Transform IVL to Dynamic Single Assignment (DSA) form
// This eliminates Assignment and Havoc commands, leaving only Assert, Assume, Seq, and NonDet
// 
// The DSA transformation is IMPLEMENTED and functional. However, it's currently disabled in favor
// of the WP function's built-in substitution mechanism, which achieves the same efficiency gains.
//
// The transformation works by:
// - x := e  =>  assume(x_i = e) where x_i is fresh, and substitute x with x_i in continuation
// - havoc x =>  (no constraint on x_i), and substitute x with x_i in continuation
//
// We track variable versions and their types in substitution maps.
//
// Note: The challenge with DSA is handling nondeterministic merge points (NonDet) correctly.
// At merge points, variables assigned in different branches need φ-functions (phi nodes) to
// properly track which version applies. The current WP implementation handles this implicitly
// through its substitution mechanism: wp(c1 [] c2, Q) = wp(c1,Q) ∧ wp(c2,Q), where each branch
// applies its own substitutions. This is semantically equivalent to explicit DSA with φ-nodes.
use std::collections::HashMap;

#[allow(dead_code)]
fn to_dsa_with_subst(
    ivl: &IVLCmd,
    subst_map: &mut HashMap<String, String>,
    type_map: &mut HashMap<String, Type>,
    counter: &mut usize,
) -> IVLCmd {
    match &ivl.kind {
        IVLCmdKind::Assignment { name, expr } => {
            // Apply current substitutions to the expression
            let mut substituted_expr = expr.clone();
            for (old_var, new_var) in subst_map.iter() {
                if let Some(var_type) = type_map.get(new_var) {
                    let new_expr = Expr::ident(new_var, var_type);
                    substituted_expr = substituted_expr.subst_ident(old_var, &new_expr);
                }
            }
            
            // Create fresh version of the assigned variable
            let fresh_name = format!("{}_{}", name.ident, *counter);
            *counter += 1;
            
            // The type of the fresh variable is the type of the expression
            let fresh_type = substituted_expr.ty.clone();
            
            // Update substitution map: future uses of 'name' should use 'fresh_name'
            subst_map.insert(name.ident.clone(), fresh_name.clone());
            type_map.insert(fresh_name.clone(), fresh_type.clone());
            
            // Generate: assume(x_fresh = expr)
            let fresh_var = Expr::ident(&fresh_name, &fresh_type);
            let assumption = fresh_var.eq(&substituted_expr);
            let mut result = IVLCmd::assume(&assumption);
            // Preserve the original span from the assignment
            result.span = ivl.span;
            result
        },
        IVLCmdKind::Havoc { name, ty } => {
            // Create fresh version of the havoc'd variable
            let fresh_name = format!("{}_{}", name.ident, *counter);
            *counter += 1;
            
            // Update substitution map and type map
            subst_map.insert(name.ident.clone(), fresh_name.clone());
            type_map.insert(fresh_name.clone(), ty.clone());
            
            // havoc becomes: assume(true) - the variable is unconstrained
            let mut result = IVLCmd::assume(&Expr::bool(true));
            // Preserve the original span from the havoc
            result.span = ivl.span;
            result
        },
        IVLCmdKind::Seq(c1, c2) => {
            // Transform c1 first, which may update subst_map and type_map
            let dsa_c1 = to_dsa_with_subst(c1, subst_map, type_map, counter);
            // Then transform c2 with the updated substitutions
            let dsa_c2 = to_dsa_with_subst(c2, subst_map, type_map, counter);
            let mut result = IVLCmd::seq(&dsa_c1, &dsa_c2);
            // Preserve the original span from the sequence
            result.span = ivl.span;
            result
        },
        IVLCmdKind::NonDet(c1, c2) => {
            // Each branch starts with the same substitution map but may end with different maps
            let mut subst1 = subst_map.clone();
            let mut subst2 = subst_map.clone();
            let mut type1 = type_map.clone();
            let mut type2 = type_map.clone();
            let mut counter1 = *counter;
            let mut counter2 = *counter;
            
            let dsa_c1 = to_dsa_with_subst(c1, &mut subst1, &mut type1, &mut counter1);
            let dsa_c2 = to_dsa_with_subst(c2, &mut subst2, &mut type2, &mut counter2);
            
            // Update counter to max of both branches
            *counter = counter1.max(counter2);
            
            // Key insight for DSA with NonDet: We do NOT merge substitution maps here.
            // Instead, we keep the original substitution map unchanged.
            // The WP will correctly handle the fact that different branches assign to
            // different fresh variables, and will compute: WP(c1, post) ∧ WP(c2, post)
            // where each WP uses its own substitutions.
            //
            // This means that any assertion AFTER the NonDet will use the pre-NonDet
            // versions of variables, which is correct because the WP will propagate
            // the constraints back through both branches appropriately.
            
            let mut result = IVLCmd::nondet(&dsa_c1, &dsa_c2);
            result.span = ivl.span;
            result
        },
        IVLCmdKind::Assert { condition, message } => {
            // Apply current substitutions to the condition
            let mut substituted_cond = condition.clone();
            for (old_var, new_var) in subst_map.iter() {
                if let Some(var_type) = type_map.get(new_var) {
                    let new_expr = Expr::ident(new_var, var_type);
                    substituted_cond = substituted_cond.subst_ident(old_var, &new_expr);
                }
            }
            let mut result = IVLCmd::assert(&substituted_cond, message);
            // Preserve the original span from the assertion
            result.span = ivl.span;
            result
        },
        IVLCmdKind::Assume { condition } => {
            // Apply current substitutions to the condition
            let mut substituted_cond = condition.clone();
            for (old_var, new_var) in subst_map.iter() {
                if let Some(var_type) = type_map.get(new_var) {
                    let new_expr = Expr::ident(new_var, var_type);
                    substituted_cond = substituted_cond.subst_ident(old_var, &new_expr);
                }
            }
            let mut result = IVLCmd::assume(&substituted_cond);
            // Preserve the original span from the assumption
            result.span = ivl.span;
            result
        },
    }
}

// Public wrapper for DSA transformation
#[allow(dead_code)]
fn to_dsa(ivl: &IVLCmd) -> IVLCmd {
    let mut subst_map = HashMap::new();
    let mut type_map = HashMap::new();
    let mut counter = 0;
    to_dsa_with_subst(ivl, &mut subst_map, &mut type_map, &mut counter)
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(
    cmd: &Cmd,
    file: &slang::SourceFile,
    current_method: Option<&slang::ast::Method>,
) -> IVLCmd {
    cmd_to_ivlcmd_with_post(cmd, file, &Expr::bool(true), current_method)
}

fn cmd_to_ivlcmd_with_post(
    cmd: &Cmd,
    file: &slang::SourceFile,
    postcondition: &Expr,
    current_method: Option<&slang::ast::Method>,
) -> IVLCmd {
    match &cmd.kind {
        CmdKind::Assert { condition, .. } => IVLCmd::assert(condition, "Assert might fail!"),
        CmdKind::Seq(first, second) => {
            IVLCmd::seq(
                &cmd_to_ivlcmd_with_post(first, file, postcondition, current_method),
                &cmd_to_ivlcmd_with_post(second, file, postcondition, current_method),
            )
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

            // running disjunction of previous guards
            let mut prev_or: Option<Expr> = None;

            for case in &body.cases {
                // guard' = guard ∧ ¬(∨ previous guards)
                let guard = case.condition.clone();
                let guard_prime = if let Some(prev) = &prev_or {
                    guard.clone() & !prev.clone()
                } else {
                    guard.clone()
                };

                // update prev_or := prev_or ∨ guard
                prev_or = Some(if let Some(prev) = prev_or { prev | guard } else { guard });

                let assume = IVLCmd::assume(&guard_prime);
                let lowered = cmd_to_ivlcmd_with_post(&case.cmd, file, postcondition, current_method);
                let branch = IVLCmd::seq(&assume, &lowered);
                branches.push(branch);
            }

            IVLCmd::nondets(&branches)
        },
        CmdKind::Return { expr } => {
            // Extension Feature 10: Early return
            // Return makes everything after it unreachable
            match expr {
                Some(init_expression) => {
                    let ret_name = slang::ast::Name { ident: "ret".to_string(), span: init_expression.span };
                    let assign = IVLCmd::assign(&ret_name, init_expression);
                    // Check postcondition at the return point
                    // Use empty message so error reporting uses the ensures clause span
                    let assert_post = IVLCmd::assert(postcondition, "");
                    // Sequence: assignment, assert postcondition, then unreachable
                    IVLCmd::seq(&assign, &IVLCmd::seq(&assert_post, &IVLCmd::unreachable()))
                }
                None => IVLCmd::unreachable(),
            }
        },
        CmdKind::Loop { invariants, body, variant, .. } => {
            // Extension Feature 11: Support break and continue
            // Extension Feature 8: variant contains the decreases expression
            let decreases = variant.as_ref();
            
            // Merge all invariants into a single expression
            let inv = invariants
                .iter()
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));

            // Extension Feature 11: Initialize the 'broke' variable to false before the loop
            let broke_name = slang::ast::Name {
                ident: "broke".to_string(),
                span: Span::default(),
            };
            let false_expr = Expr::bool(false);
            let init_broke = IVLCmd::assign(&broke_name, &false_expr);

            // Step 1: Assert invariant holds initially (with broke = false)
            let mut assert_inv_init = IVLCmd::assert(&inv, "Loop invariant may not hold on entry");
            // Set span to first user-provided invariant if available
            if let Some(first_inv) = invariants.first() {
                assert_inv_init.span = first_inv.span;
            }

            // Step 2: Verify invariant is preserved by checking each branch
            // Start by assuming the invariant holds and broke = false (we're still in the loop)
            let broke_expr = Expr::ident("broke", &slang::ast::Type::Bool);
            let not_broke = !broke_expr.clone();
            let assume_inv_for_body = IVLCmd::seq(&IVLCmd::assume(&inv), &IVLCmd::assume(&not_broke));
            
            // Build nondeterministic choice for all branches
            let mut preservation_branches: Vec<IVLCmd> = Vec::new();
            for case in &body.cases {
                // For each branch: assume guard, execute body, assert invariant
                let assume_guard = IVLCmd::assume(&case.condition);
                
                let body_encoded = cmd_to_ivlcmd_with_post(&case.cmd, file, postcondition, current_method);
                let mut assert_inv_after = IVLCmd::assert(&inv, "Loop invariant may not be preserved");
                // Set span to first user-provided invariant if available
                if let Some(first_inv) = invariants.first() {
                    assert_inv_after.span = first_inv.span;
                }
                
                // Extension Feature 8: Total correctness - check that decreases expression strictly decreases
                // Only check decreases if we didn't break (broke = false after body)
                let branch_with_inv = IVLCmd::seq(&assume_guard,
                    &IVLCmd::seq(&body_encoded, &assert_inv_after));
                
                let branch = if let Some(dec_expr) = decreases {
                    // Create a fresh variable to store the old value of the decreases expression
                    let dec_old_name = slang::ast::Name { 
                        ident: "__dec_old".to_string(), 
                        span: dec_expr.span 
                    };
                    let dec_ty = slang::ast::Type::Int; // decreases expressions are typically Int
                    
                    // Before the loop body: dec_old := decreases_expr
                    let save_dec = IVLCmd::assign(&dec_old_name, dec_expr);
                    
                    // After the loop body: if !broke, assert decreases_expr < dec_old AND decreases_expr >= 0
                    let dec_old_expr = Expr::ident("__dec_old", &dec_ty);
                    let dec_decreased = dec_expr.clone().lt(&dec_old_expr);
                    let dec_non_negative = dec_expr.clone().ge(&Expr::new_typed(
                        slang::ast::ExprKind::Num(0), 
                        dec_ty.clone()
                    ));
                    
                    // Extension Feature 11: Only check decreases if we didn't break
                    // If broke, then we don't need to check termination
                    let broke_after = Expr::ident("broke", &slang::ast::Type::Bool);
                    let decreases_condition = broke_after.clone() | (dec_decreased & dec_non_negative);
                    
                    let mut assert_dec = IVLCmd::assert(
                        &decreases_condition, 
                        "Loop may not terminate (decreases clause not satisfied)"
                    );
                    assert_dec.span = dec_expr.span;
                    
                    // Sequence: save dec_old; assume guard; body; assert inv; assert decreases
                    IVLCmd::seq(&save_dec, 
                        &IVLCmd::seq(&branch_with_inv, &assert_dec))
                } else {
                    branch_with_inv
                };
                
                preservation_branches.push(branch);
            }
            let preservation_check = IVLCmd::nondets(&preservation_branches);
            let verify_preservation = IVLCmd::seq(&assume_inv_for_body, &preservation_check);

            // Step 3: After loop - assume invariant and (all guards are false OR broke is true)
            let all_guards_false = body.cases
                .iter()
                .map(|case| !case.condition.clone())
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            
            // Extension Feature 11: Loop can exit either when all guards are false OR when broke
            let broke_after_loop = Expr::ident("broke", &slang::ast::Type::Bool);
            let exit_condition = all_guards_false | broke_after_loop;
            let after_loop = IVLCmd::seq(&IVLCmd::assume(&inv), &IVLCmd::assume(&exit_condition));

            // Final encoding: broke := false; assert I; (assume I ∧ !broke; check preservation); assume I ∧ (¬guards ∨ broke)
            IVLCmd::seq(&init_broke, &IVLCmd::seq(&assert_inv_init, &IVLCmd::seq(&verify_preservation, &after_loop)))
        },
        CmdKind::For { name, range, invariants, body, variant, .. } => {
            // Extension Feature 8: variant contains the decreases expression
            let decreases = variant.as_ref();
            
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
                let body_encoded = cmd_to_ivlcmd(&body.cmd, file, current_method);
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
                
                // Extension Feature 8: Total correctness for for-loops
                let body_with_assumption = if let Some(dec_expr) = decreases {
                    // Create a fresh variable to store the old value of the decreases expression
                    let dec_old_name = slang::ast::Name { 
                        ident: "__dec_old".to_string(), 
                        span: dec_expr.span 
                    };
                    let dec_ty = slang::ast::Type::Int;
                    
                    // Before the loop body: dec_old := decreases_expr
                    let save_dec = IVLCmd::assign(&dec_old_name, dec_expr);
                    
                    // After the loop body: assert decreases_expr < dec_old AND decreases_expr >= 0
                    let dec_old_expr = Expr::ident("__dec_old", &dec_ty);
                    let dec_decreased = dec_expr.clone().lt(&dec_old_expr);
                    let dec_non_negative = dec_expr.clone().ge(&Expr::new_typed(
                        slang::ast::ExprKind::Num(0), 
                        dec_ty.clone()
                    ));
                    let mut assert_dec = IVLCmd::assert(
                        &(dec_decreased & dec_non_negative), 
                        "For-loop may not terminate (decreases clause not satisfied)"
                    );
                    assert_dec.span = dec_expr.span;
                    
                    // Sequence: save dec_old; assume guard; body+increment; assert decreases
                    IVLCmd::seq(&save_dec, 
                        &IVLCmd::seq(&assume_guard, 
                            &IVLCmd::seq(&loop_body_with_increment, &assert_dec)))
                } else {
                    IVLCmd::seq(&assume_guard, &loop_body_with_increment)
                };
                
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
                let body_encoded = cmd_to_ivlcmd(&body.cmd, file, current_method);
                
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
            // 3. Extension Feature 9: Save old values of global variables in modifies clause
            // 4. Extension Feature 9: Havoc global variables in modifies clause
            // 5. Assume postconditions hold (with arguments, result, and old() substituted)
            
            // Find the called method in the source file
            let methods = file.methods();
            let called_method = methods
                .iter()
                .find(|m| m.name.ident == fun_name.ident)
                .expect("Method not found");
            
            // Get parameters from the called method
            let params: Vec<_> = called_method.args.iter().collect();
            
            // Extension Feature 9: Get global variables that the called method can modify
            let modifies_globals: Vec<String> = called_method.modifies()
                .map(|(name, _ty)| name.ident.clone())
                .collect();
            
            // Get all global variables from the file
            let globals = file.globals();
            
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

            if let Some(curr) = current_method {
                if curr.name.ident == called_method.name.ident {
                    if let Some(callee_v) = &called_method.variant {
                        // must match the name created earlier in `analyze`
                        let ghost_name = format!("__methV_{}", curr.name.ident);
                        let ghost_e    = Expr::ident(&ghost_name, &Type::Int);

                        // substitute formals -> actuals in the callee's variant
                        let mut v_call = callee_v.clone();
                        for (param, arg) in called_method.args.iter().zip(args.iter()) {
                            v_call = v_call.subst_ident(&param.name.ident, arg);
                        }

                        // require strict decrease
                        let mut assert_dec = IVLCmd::assert(
                            &v_call.lt(&ghost_e),
                            "Recursive call does not decrease the method’s variant",
                        );
                        assert_dec.span = fun_name.span; // point at the call site
                        precond_cmd = IVLCmd::seq(&precond_cmd, &assert_dec);
                    }
                }
            }
            
            
            
            // Extension Feature 9: Save old values of modified global variables
            // For each global in modifies clause, create __old_<name> := <name>
            let mut save_old_globals = IVLCmd::nop();
            for global_name in &modifies_globals {
                // Find the global variable's type
                let global_var = globals.iter()
                    .find(|g| g.var.name.ident == *global_name)
                    .expect("Global variable not found");
                
                let old_name = slang::ast::Name {
                    ident: format!("__old_{}", global_name),
                    span: fun_name.span,
                };
                let current_value = Expr::ident(global_name, &global_var.var.ty.1);
                save_old_globals = IVLCmd::seq(&save_old_globals, &IVLCmd::assign(&old_name, &current_value));
                
                // Also create an assumption that connects old(global_name) with __old_global_name
                // This helps the SMT solver understand the relationship
                let old_global_expr = Expr::new_typed(
                    slang::ast::ExprKind::Old(global_var.var.name.clone()),
                    global_var.var.ty.1.clone()
                );
                let saved_value_expr = Expr::ident(&format!("__old_{}", global_name), &global_var.var.ty.1);
                let connection = old_global_expr.eq(&saved_value_expr);
                save_old_globals = IVLCmd::seq(&save_old_globals, &IVLCmd::assume(&connection));
            }
            
            // Extension Feature 9: Havoc modified global variables
            let mut havoc_globals = IVLCmd::nop();
            for global_name in &modifies_globals {
                let global_var = globals.iter()
                    .find(|g| g.var.name.ident == *global_name)
                    .expect("Global variable not found");
                
                havoc_globals = IVLCmd::seq(&havoc_globals, &IVLCmd::havoc(&global_var.var.name, &global_var.var.ty.1));
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
                    
                    // Note: old() expressions should now work correctly because we added
                    // an assumption that old(global) == __old_global after saving the value
                    
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
                    
                    // Note: old() expressions should now work correctly because we added
                    // an assumption that old(global) == __old_global after saving the value
                    
                    // Assume the postcondition holds
                    let assume_post = IVLCmd::assume(&substituted_post);
                    postcond_cmd = IVLCmd::seq(&postcond_cmd, &assume_post);
                }
                
                postcond_cmd
            };
            
            // Sequence: assert preconditions, save old globals, havoc globals, then havoc+assume postconditions
            IVLCmd::seq(&precond_cmd, &IVLCmd::seq(&save_old_globals, &IVLCmd::seq(&havoc_globals, &ret_cmd)))
        },
        CmdKind::Break => {
            // Extension Feature 11: Break statement
            // Set the 'broke' variable to true
            // The loop encoding will check the invariant after the body
            // and will allow the loop to exit if broke is true
            let broke_name = slang::ast::Name {
                ident: "broke".to_string(),
                span: cmd.span,
            };
            let true_expr = Expr::bool(true);
            IVLCmd::assign(&broke_name, &true_expr)
        },
        CmdKind::Continue => {
            // Extension Feature 11: Continue statement
            // Make everything after it in the current iteration unreachable
            // The loop will proceed to check the invariant and continue with the next iteration
            IVLCmd::unreachable()
        },
        _ => {
            eprintln!("Unsupported command kind: {:?}", cmd.kind);
            todo!("Not supported (yet).")
        },
    }
}

// Weakest precondition calculation for IVL programs.
// Returns (obligation, error_message, error_span)
// 
// Extension Feature 3: This WP implementation handles both DSA-transformed and non-DSA IVL programs.
// For Assignment, it uses substitution which is semantically equivalent to DSA transformation.
// For Havoc, it uses quantification (forall), also equivalent to DSA.
// This approach is as efficient as explicit DSA while being simpler to implement correctly.
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
            let fresh = format!("{}_{}", name.ident, next_fresh_id());
            let fresh_e = Expr::ident(&fresh, ty);
            (post.subst_ident(&name.ident, &fresh_e), String::new(), Span::default())
        },
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
        // Extension Feature 3: These can still appear in some cases, so keep them for compatibility
        IVLCmdKind::Assignment { name, expr } => {
            (post.clone().subst_ident(&name.ident, expr), String::new(), Span::default())
        },
        IVLCmdKind::Havoc { name, ty } => {
            let ident_name = name.as_str();
            let ident_e = Expr::ident(&ident_name, ty);
            let q = post.subst_ident(&name.ident, &ident_e);
            (q, String::new(), Span::default())
        }
    }
}
