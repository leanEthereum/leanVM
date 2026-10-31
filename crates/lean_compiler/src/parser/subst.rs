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

/// Substitute `Var(name)` → `to` through a statement list, stopping after a
/// statement that rebinds `name` (later uses refer to the new binding). Nested
/// blocks recurse independently and never stop it: a loop counter of the same
/// name shadows it in its body, the parser rejects a rebinding inside an `if`
/// arm or an `unroll` body ([`rebinds_in_block`]), whose bindings may outlive
/// the block, and a `mul_range` body's never do.
pub(crate) fn subst_stmts(stmts: &[Stmt], name: &str, to: &Expr) -> Vec<Stmt> {
    let mut rest = stmts.iter();
    let mut out = Vec::with_capacity(stmts.len());
    for s in rest.by_ref() {
        out.push(s.at(subst_kind(&s.kind, name, to)));
        if binds(&s.kind, name) {
            break;
        }
    }
    out.extend(rest.cloned());
    out
}

fn subst_kind(s: &StmtKind, name: &str, to: &Expr) -> StmtKind {
    let e = |x: &Expr| subst_var(x, name, to);
    let es = |xs: &[Expr]| xs.iter().map(e).collect();
    // A loop counter named `name` shadows it in the body.
    let body = |var: &str, body: &[Stmt]| {
        if var == name {
            body.to_vec()
        } else {
            subst_stmts(body, name, to)
        }
    };
    match s {
        StmtKind::Let(n, x) => StmtKind::Let(n.clone(), e(x)),
        StmtKind::LetTuple(ns, f, args) => StmtKind::LetTuple(ns.clone(), f.clone(), es(args)),
        StmtKind::AssertEq(a, b) => StmtKind::AssertEq(e(a), e(b)),
        StmtKind::AssertNe(a, b) => StmtKind::AssertNe(e(a), e(b)),
        StmtKind::AssertLt(a, bound) => StmtKind::AssertLt(
            e(a),
            match bound {
                LtBound::Const(k) => LtBound::Const(*k),
                LtBound::Runtime(b) => LtBound::Runtime(e(b)),
            },
        ),
        StmtKind::Call(f, args) => StmtKind::Call(f.clone(), es(args)),
        StmtKind::Print { label, value } => StmtKind::Print {
            label: label.clone(),
            value: e(value),
        },
        StmtKind::LetHintWitness { name, stream } => StmtKind::LetHintWitness {
            name: name.clone(),
            stream: stream.clone(),
        },
        StmtKind::HintWitness { dest, name } => StmtKind::HintWitness {
            dest: e(dest),
            name: name.clone(),
        },
        StmtKind::Store(a, i, v) => StmtKind::Store(e(a), e(i), e(v)),
        StmtKind::Return(xs) => StmtKind::Return(es(xs)),
        StmtKind::CallIfNe(a, b, f, args) => StmtKind::CallIfNe(e(a), e(b), f.clone(), es(args)),
        StmtKind::For { var, lo, hi, body: b } => StmtKind::For {
            var: var.clone(),
            lo: *lo,
            hi: match hi {
                ForBound::Const(k) => ForBound::Const(*k),
                ForBound::Runtime(x) => ForBound::Runtime(e(x)),
            },
            body: body(var, b),
        },
        StmtKind::Unroll { var, lo, hi, body: b } => StmtKind::Unroll {
            var: var.clone(),
            lo: e(lo),
            hi: e(hi),
            body: body(var, b),
        },
        StmtKind::If {
            eq,
            lhs,
            rhs,
            then,
            els,
            force_const,
        } => StmtKind::If {
            eq: *eq,
            lhs: e(lhs),
            rhs: e(rhs),
            then: subst_stmts(then, name, to),
            els: subst_stmts(els, name, to),
            force_const: *force_const,
        },
        // A name target is a binder, so it is never substituted: rewriting it
        // turned `k, e = …` under a `Const k` into a literal target. An index
        // target (`sb[k]`) is a use.
        StmtKind::Match { targets, x, arms } => StmtKind::Match {
            targets: targets
                .iter()
                .map(|t| if matches!(t, Expr::Var(_)) { t.clone() } else { e(t) })
                .collect(),
            x: e(x),
            arms: es(arms),
        },
    }
}

/// `e` with every `Var(name)` replaced by `to`: the `match` arm
/// expansion, where the lambda parameter becomes the arm's integer literal.
pub(crate) fn subst_var(e: &Expr, name: &str, to: &Expr) -> Expr {
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
        Expr::ListComp(body, var, lo, hi) => Expr::ListComp(
            if var == name { body.clone() } else { s(body) },
            var.clone(),
            s(lo),
            s(hi),
        ),
        Expr::Call(f, args) => Expr::Call(f.clone(), args.iter().map(|a| subst_var(a, name, to)).collect()),
        other => other.clone(),
    }
}
