//! Substituting an expression for a name in an expression: the `match` arm expansion, where the lambda parameter
//! becomes each arm's integer literal.

use super::*;

/// `e` with every `Var(name)` replaced by `to`: the `match` arm
/// expansion, where the lambda parameter becomes the arm's integer literal.
pub(crate) fn subst_var(e: &Expr, name: &str, to: &Expr) -> Expr {
    subst_vars(e, &[(name, to)])
}

fn subst_vars(e: &Expr, subs: &[(&str, &Expr)]) -> Expr {
    subst_shared(e, subs).unwrap_or_else(|| e.clone())
}

/// `e` with the substitution applied, or `None` when no substituted name occurs free in it.
/// An untouched subtree is shared with `e` rather than copied.
fn subst_shared(e: &Expr, subs: &[(&str, &Expr)]) -> Option<Expr> {
    let s = |b: &Arc<Expr>| subst_shared(b, subs).map(Arc::new);
    let or = |new: Option<Arc<Expr>>, old: &Arc<Expr>| new.unwrap_or_else(|| Arc::clone(old));
    let pair = |a: &Arc<Expr>, b: &Arc<Expr>, node: fn(Arc<Expr>, Arc<Expr>) -> Expr| match (s(a), s(b)) {
        (None, None) => None,
        (x, y) => Some(node(or(x, a), or(y, b))),
    };
    match e {
        Expr::Var(v) => subs.iter().find(|(name, _)| name == v).map(|(_, to)| (*to).clone()),
        Expr::Add(a, b) => pair(a, b, Expr::Add),
        Expr::Mul(a, b) => pair(a, b, Expr::Mul),
        Expr::Sub(a, b) => pair(a, b, Expr::Sub),
        Expr::Div(a, b) => pair(a, b, Expr::Div),
        Expr::FieldDiv(a, b) => pair(a, b, Expr::FieldDiv),
        Expr::Mod(a, b) => pair(a, b, Expr::Mod),
        Expr::Index(a, b) => pair(a, b, Expr::Index),
        Expr::Pow(a, b) => pair(a, b, Expr::Pow),
        Expr::Slice(a, lo, hi) => match (s(a), s(lo), s(hi)) {
            (None, None, None) => None,
            (x, y, z) => Some(Expr::Slice(or(x, a), or(y, lo), or(z, hi))),
        },
        Expr::GenPow(x) => s(x).map(Expr::GenPow),
        Expr::HeapBufDyn(x) => s(x).map(Expr::HeapBufDyn),
        Expr::ListLit(es) => subst_list(es, subs).map(Expr::ListLit),
        Expr::ListComp(body, var, lo, hi) => {
            let body_new = if subs.iter().any(|(name, _)| name == var) {
                let rest: Vec<_> = subs.iter().copied().filter(|(name, _)| name != var).collect();
                subst_shared(body, &rest).map(Arc::new)
            } else {
                s(body)
            };
            match (body_new, s(lo), s(hi)) {
                (None, None, None) => None,
                (x, y, z) => Some(Expr::ListComp(or(x, body), var.clone(), or(y, lo), or(z, hi))),
            }
        }
        Expr::Call(f, args) => subst_list(args, subs).map(|args| Expr::Call(f.clone(), args)),
        Expr::Lit(_) | Expr::Gen | Expr::GPow(_) | Expr::HeapBuf(_) | Expr::StackBuf(_) => None,
    }
}

/// The list with the substitution applied, or `None` when no element changes.
fn subst_list(es: &[Expr], subs: &[(&str, &Expr)]) -> Option<Vec<Expr>> {
    let mut out: Option<Vec<Expr>> = None;
    for (i, a) in es.iter().enumerate() {
        match (subst_shared(a, subs), &mut out) {
            (Some(new), Some(v)) => v.push(new),
            (None, Some(v)) => v.push(a.clone()),
            (Some(new), None) => {
                let mut v = Vec::with_capacity(es.len());
                v.extend(es[..i].iter().cloned());
                v.push(new);
                out = Some(v);
            }
            (None, None) => {}
        }
    }
    out
}
