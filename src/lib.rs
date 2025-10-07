pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr};
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

            let (oblig, msg) = wp(&ivl, &post);
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
                        cx.error(oblig.span, msg.to_string());
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(oblig.span, format!("{msg}: unknown sat result"));
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
        _ => todo!("Not supported (yet)."),
    }
}

// Weakest precondition of (assert-only) IVL programs comprised of a single
// assertion
fn wp(ivl: &IVLCmd, post: &Expr) -> (Expr, String) {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => (condition.clone() & post.clone(), message.clone()),
        IVLCmdKind::Seq(c1, c2, ) => {
            let (new_post, _) = wp(c2, post);
            wp(c1, &new_post)
        },
        IVLCmdKind::Assume { condition } => (!condition.clone() | post.clone(), "".to_string() ),
        IVLCmdKind::Assignment { name, expr } => (post.clone().subst_ident(&name.ident, expr), "".to_string()),
        IVLCmdKind::Havoc { name, ty } => {
            let ident_name = name.as_str();
            let ident_e = Expr::ident(&ident_name, ty);
            let q = post.subst_ident(&name.ident, &ident_e);
            (q, String::new())
        }
        IVLCmdKind::NonDet(cmd1, cmd2) => {
            let (expr1, msg1) = wp(&cmd1, post);
            let (expr2, msg2) = wp(&cmd2, post);

            (expr1 & expr2, format!("{}{}", msg1, msg2))
        },
    }
}
