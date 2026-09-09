//! Substituting an expression for a name, throughout a statement tree.
//!
//! This is how the two compile-time replications bind their variable: an
//! `unroll` body is re-emitted per integer with the counter substituted as a
//! literal, and a `Const` parameter is substituted into the monomorphised copy.
//! Both happen BEFORE lowering, so the result is ordinary source that no longer
//! mentions the name.
//!
//! Every arm has to be exhaustive over [`StmtKind`] and carry its fields
//! through: a field silently dropped here is a construct that loses its meaning
//! only inside an unrolled loop or a specialisation, which is the hardest place
//! to notice it.

use super::*;

/// Substitute `Var(name)` → `to` through a statement list, stopping at a
/// statement that rebinds `name` (later uses refer to the new binding).
/// Nested blocks recurse independently, since their bindings are branch-local,
/// matching the lowering's scoping. Used by `Const`-parameter specialization.
pub(crate) fn subst_stmts(stmts: &[Stmt], name: &str, to: &Expr) -> Vec<Stmt> {
    let mut out = Vec::with_capacity(stmts.len());
    let mut active = true;
    for s in stmts {
        if !active {
            out.push(s.clone());
            continue;
        }
        let (kind, rebinds) = subst_kind(&s.kind, name, to);
        out.push(s.at(kind));
        active = !rebinds;
    }
    out
}

/// Substitute one statement kind; the flag says whether it rebinds `name`.
fn subst_kind(s: &StmtKind, name: &str, to: &Expr) -> (StmtKind, bool) {
    let e = |x: &Expr| subst_var(x, name, to);
    match s {
        StmtKind::Let(n, x) => (StmtKind::Let(n.clone(), e(x)), n == name),
        StmtKind::LetTuple(ns, f, args) => (
            StmtKind::LetTuple(ns.clone(), f.clone(), args.iter().map(e).collect()),
            ns.iter().any(|n| n == name),
        ),
        StmtKind::AssertEq(a, b) => (StmtKind::AssertEq(e(a), e(b)), false),
        StmtKind::AssertNe(a, b) => (StmtKind::AssertNe(e(a), e(b)), false),
        StmtKind::AssertLt(a, bound) => (
            StmtKind::AssertLt(
                e(a),
                match bound {
                    LtBound::Const(k) => LtBound::Const(*k),
                    LtBound::Runtime(b) => LtBound::Runtime(e(b)),
                },
            ),
            false,
        ),
        StmtKind::Call(f, args) => (StmtKind::Call(f.clone(), args.iter().map(e).collect()), false),
        StmtKind::Print { label, value } => (
            StmtKind::Print {
                label: label.clone(),
                value: e(value),
            },
            false,
        ),
        // Binds `name` and mentions no expression, so a substitution stops at it
        // exactly as it does at any other binder.
        StmtKind::LetHintWitness { name: n, stream } => (
            StmtKind::LetHintWitness {
                name: n.clone(),
                stream: stream.clone(),
            },
            n == name,
        ),
        StmtKind::HintWitness { dest, name: n } => (
            StmtKind::HintWitness {
                dest: e(dest),
                name: n.clone(),
            },
            false,
        ),
        StmtKind::Store(a, i, v) => (StmtKind::Store(e(a), e(i), e(v)), false),
        StmtKind::Return(es) => (StmtKind::Return(es.iter().map(e).collect()), false),
        StmtKind::CallIfNe(a, b, f, args) => (
            StmtKind::CallIfNe(e(a), e(b), f.clone(), args.iter().map(e).collect()),
            false,
        ),
        StmtKind::For { var, lo, hi, body } => {
            let hi = match hi {
                ForBound::Const(k) => ForBound::Const(*k),
                ForBound::Runtime(b) => ForBound::Runtime(e(b)),
            };
            // The counter shadows `name` inside the body only.
            let body = if var == name {
                body.clone()
            } else {
                subst_stmts(body, name, to)
            };
            (
                StmtKind::For {
                    var: var.clone(),
                    lo: *lo,
                    hi,
                    body,
                },
                false,
            )
        }
        StmtKind::Unroll { var, lo, hi, body } => {
            let body = if var == name {
                body.clone()
            } else {
                subst_stmts(body, name, to)
            };
            (
                StmtKind::Unroll {
                    var: var.clone(),
                    lo: e(lo),
                    hi: e(hi),
                    body,
                },
                false,
            )
        }
        StmtKind::If {
            eq,
            lhs,
            rhs,
            then,
            els,
            force_const,
        } => (
            StmtKind::If {
                eq: *eq,
                lhs: e(lhs),
                rhs: e(rhs),
                then: subst_stmts(then, name, to),
                els: subst_stmts(els, name, to),
                force_const: *force_const,
            },
            false,
        ),
        StmtKind::Match { targets, x, arms } => (
            StmtKind::Match {
                // A name target is a BINDER, so it is never substituted: the
                // `shadow` flag below already stops substitution past this
                // statement, and rewriting the binder itself turned `k, e = …`
                // under a `Const k` into a literal target. An INDEX target is a
                // use (`sb[k]` needs `k`), so it is substituted.
                targets: targets
                    .iter()
                    .map(|t| if matches!(t, Expr::Var(_)) { t.clone() } else { e(t) })
                    .collect(),
                x: e(x),
                arms: arms.iter().map(e).collect(),
            },
            targets.iter().any(|t| matches!(t, Expr::Var(n) if n == name)),
        ),
    }
}

/// `e` with every `Var(name)` replaced by `to`: the `match` arm
/// expansion, where the lambda parameter becomes the arm's integer literal.
pub(super) fn subst_var(e: &Expr, name: &str, to: &Expr) -> Expr {
    let s = |b: &Expr| Box::new(subst_var(b, name, to));
    match e {
        Expr::Var(v) if v == name => to.clone(),
        Expr::Add(a, b) => Expr::Add(s(a), s(b)),
        Expr::Mul(a, b) => Expr::Mul(s(a), s(b)),
        Expr::Sub(a, b) => Expr::Sub(s(a), s(b)),
        Expr::Div(a, b) => Expr::Div(s(a), s(b)),
        Expr::FieldDiv(a, b) => Expr::FieldDiv(s(a), s(b)),
        Expr::Mod(a, b) => Expr::Mod(s(a), s(b)),
        Expr::Index(a, b) => Expr::Index(s(a), s(b)),
        Expr::Slice(a, lo, hi) => Expr::Slice(s(a), s(lo), s(hi)),
        Expr::GenPow(e) => Expr::GenPow(s(e)),
        Expr::Pow(a, b) => Expr::Pow(s(a), s(b)),
        Expr::HeapBufDyn(sz) => Expr::HeapBufDyn(s(sz)),
        Expr::ListLit(es) => Expr::ListLit(es.iter().map(|a| subst_var(a, name, to)).collect()),
        Expr::Call(f, args) => Expr::Call(f.clone(), args.iter().map(|a| subst_var(a, name, to)).collect()),
        other => other.clone(),
    }
}
