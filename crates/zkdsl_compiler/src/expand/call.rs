//! The call boundary: arguments in, return values out, and the two ways a callee disappears into its caller:
//! `Const` specialization monomorphises it per constant tuple, `@inline` expands its body in the caller.

use super::*;
use std::borrow::Cow;

/// How an inlined tail return binds in the caller: a `StackBuf` run and a folded g-address alias, anything else
/// takes the destination value.
pub(super) fn ret_binding(b: Option<RetBind>, dst: V) -> Binding {
    match b {
        Some(RetBind::Stack(base, size)) => Binding::Stack(base, size),
        Some(RetBind::Gaddr(ga)) => Binding::Gaddr(ga),
        _ => Binding::Scalar(dst),
    }
}

fn substitute_body<'a>(body: &'a [Stmt], substs: &[(&str, Expr)]) -> Cow<'a, [Stmt]> {
    if substs.is_empty() {
        return Cow::Borrowed(body);
    }
    let subs: Vec<(&str, &Expr)> = substs.iter().map(|(name, value)| (*name, value)).collect();
    Cow::Owned(crate::parser::subst_all(body, &subs))
}

/// A single tail return, preceded by statements that can be expanded in the caller.
fn body_inlinable(body: &[Stmt]) -> bool {
    matches!(body.split_last(), Some((last, rest)) if matches!(last.kind, StmtKind::Return(_))
        && rest.iter().all(stmt_inline_safe))
}

fn stmt_inline_safe(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Let(..)
        | StmtKind::Store(..)
        | StmtKind::HintWitness { .. }
        | StmtKind::LetHintWitness { .. }
        | StmtKind::Print { .. }
        | StmtKind::AssertEq(..)
        | StmtKind::AssertNe(..)
        | StmtKind::AssertLt(..)
        | StmtKind::Call(..)
        | StmtKind::LetTuple(..)
        | StmtKind::Match { .. } => true,
        StmtKind::If { then, els, .. } => then.iter().all(stmt_inline_safe) && els.iter().all(stmt_inline_safe),
        StmtKind::Unroll { body, .. } => body.iter().all(stmt_inline_safe),
        _ => false,
    }
}

impl FnExpand<'_> {
    /// A real call returning into `dsts`, conditional on `cond ≠ 0` when given (the call ending a loop helper).
    pub(super) fn lower_call(&mut self, callee: &str, args: &[Expr], cond: Option<V>, dsts: &[V]) {
        match self.callee_def(callee).map(|f| f.params.len()) {
            Some(want) if want != args.len() => {
                let plural = if want == 1 { "argument" } else { "arguments" };
                self.fail(format!("`{callee}` takes {want} {plural}, got {}", args.len()))
            }
            None => self.fail(format!(
                "no function named `{callee}`. A builtin that writes into a destination \
                 (`keccak`, `assert_in_k`, a `hint_*`) is a statement and returns nothing, so it \
                 cannot be called for a value"
            )),
            _ => {}
        }
        let (callee, args) = self.specialize(callee, args);
        let shapes = self
            .callee_def(&callee)
            .map(|f| f.param_shapes().collect::<Vec<_>>())
            .unwrap_or_else(|| vec![Shape::Scalar; args.len()]);
        let mut cells = Vec::new();
        for (i, a) in args.iter().enumerate() {
            match shapes.get(i).copied().unwrap_or(Shape::Scalar) {
                Shape::StackBuf(n) => {
                    let (src, len) = self.stack_of(a).unwrap_or_else(|| {
                        self.fail(format!(
                            "`{callee}` parameter {i} is a StackBuf({n}); pass one, got `{a:?}`"
                        ))
                    });
                    if len != n {
                        self.fail(format!(
                            "`{callee}` parameter {i} is a StackBuf({n}), got a StackBuf({len})"
                        ))
                    }
                    cells.extend(src..src + n);
                }
                Shape::Scalar => cells.push(self.expr(a)),
            }
        }
        match cond {
            Some(x) => self.emit(CStmt::CallIf(x, callee, cells)),
            None => self.emit(CStmt::Call(callee, cells, dsts.to_vec())),
        }
    }

    /// `names = match(log(x), …, lambda k: f(args, k))` fused: every arm calls one of `callees` with the same
    /// runtime arguments, on one shared frame.
    pub(super) fn lower_dispatched_call(&mut self, targets: &[Expr], x: &Expr, callees: &[String], rt_args: &[&Expr]) {
        if let Some(shared) = callees.iter().find_map(|c| self.callee_def(c)) {
            for c in callees {
                if let Some(def) = self.callee_def(c)
                    && !def.param_shapes().eq(shared.param_shapes())
                {
                    self.fail(format!(
                        "`{c}` does not take the same parameter shapes as the other arms of this dispatch"
                    ))
                }
            }
            if let Some(i) = shared.param_shapes().position(|s| s != Shape::Scalar) {
                self.fail(format!(
                    "a `match` arm cannot pass a `StackBuf` parameter (parameter {i} of `{}`): the \
                     fused dispatch writes one cell per argument. Give the arms `Const` arguments so each \
                     specializes into its own call instead of fusing",
                    callees.first().map(String::as_str).unwrap_or("?")
                ))
            }
        }
        for callee in callees {
            let Some(def) = self.callee_def(callee) else {
                continue;
            };
            let want = def.params.len();
            if want != rt_args.len() {
                let plural = if want == 1 { "argument" } else { "arguments" };
                self.fail(format!(
                    "`{callee}` takes {want} {plural}, dispatched call passes {}",
                    rt_args.len()
                ))
            }
            let shapes = &def.return_shapes;
            if shapes.len() != targets.len() {
                self.fail(format!(
                    "`{callee}` returns {} values, dispatched call binds {}",
                    shapes.len(),
                    targets.len()
                ))
            };
            if shapes.iter().any(|s| *s != Shape::Scalar) {
                self.fail(format!(
                    "`{callee}`: a multi-cell StackBuf return cannot cross a dispatched join"
                ))
            };
        }
        let (rcells, binds) = self.ret_targets(targets);
        let args: Vec<V> = rt_args.iter().map(|a| self.expr(a)).collect();
        let xo = self.expr(x);
        self.emit(CStmt::Dispatch(xo, callees.to_vec(), args, rcells));
        self.bind_targets(&binds);
    }

    /// Expand an `@inline` `callee(args)` here, its tail return binding into `dsts`; `false` for another callee.
    pub(super) fn try_inline(&mut self, callee: &str, args: &[Expr], dsts: &[V]) -> bool {
        let Some(def) = self.defs.get(callee).copied().filter(|d| d.inline) else {
            return false;
        };
        let substs = self
            .const_substs(def, args)
            .unwrap_or_else(|e| self.fail(format!("`@inline {callee}`: {e}")));
        let body = substitute_body(&def.body, &substs);
        let n_ret = def.return_shapes.len();
        if n_ret != dsts.len() {
            self.fail(format!(
                "`@inline {callee}` returns {n_ret} values, call binds {}",
                dsts.len()
            ))
        };
        if !body_inlinable(&body) {
            self.fail(format!(
                "`@inline {callee}` requires one tail `return`, with no nested returns or mul_range loops"
            ))
        };
        if self.inline_calls.iter().any(|f| f == callee) {
            self.fail(format!(
                "recursive @inline expansion is not supported: {} -> {callee}",
                self.inline_calls.join(" -> ")
            ))
        };
        let mut binds: Vec<(String, Binding)> = Vec::new();
        for (i, (p, a)) in def.params.iter().zip(args).enumerate() {
            if p.kind == ParamKind::Const {
                continue;
            }
            if let Shape::StackBuf(n) = p.shape() {
                match self.stack_of(a) {
                    Some((_, len)) if len == n => {}
                    Some((_, len)) => self.fail(format!(
                        "`{callee}` parameter {i} is a StackBuf({n}), got a StackBuf({len})"
                    )),
                    None => self.fail(format!(
                        "`{callee}` parameter {i} is a StackBuf({n}); pass one, got `{a:?}`"
                    )),
                }
            }
            let b = if let Some((base, size)) = self.stack_of(a) {
                Binding::Stack(base, size)
            } else if let Some(ga) = self.gaddr_of(a) {
                Binding::Gaddr(ga)
            } else {
                Binding::Scalar(self.expr(a))
            };
            binds.push((p.name.clone(), b));
        }
        // Only the name bindings reset: the body runs in the caller.
        let saved = std::mem::take(&mut self.scope.names);
        for (p, b) in binds {
            self.check_not_reserved(&p);
            self.scope.names.insert(p, Bound { val: b, int: None });
        }
        let saved_ret = self.inline_ret.replace(dsts.to_vec());
        let saved_line = self.cur_line;
        self.inline_calls.push(callee.to_string());
        for s in body.iter() {
            self.stmt(s);
        }
        self.inline_calls.pop();
        self.inline_ret = saved_ret;
        self.cur_line = saved_line;
        self.scope.names = saved;
        true
    }

    /// `return`: in an inlined body, bind each value into the caller (a run or a folded address aliases, a scalar
    /// is evaluated into its destination); in `main`, nothing; else the values into one fresh run, returned.
    pub(super) fn lower_return(&mut self, exprs: &[Expr]) {
        if let Some(dsts) = self.inline_ret.take() {
            let mut binds = Vec::with_capacity(dsts.len());
            for (e, &d) in exprs.iter().zip(&dsts) {
                binds.push(if let Some((base, size)) = self.stack_of(e) {
                    RetBind::Stack(base, size)
                } else if let Some(ga) = self.gaddr_of(e) {
                    RetBind::Gaddr(ga)
                } else {
                    self.expr_into(e, d);
                    RetBind::Scalar
                });
            }
            self.inline_stack_ret = Some(binds);
            return;
        }
        if self.is_main {
            return;
        }
        if exprs.len() != self.return_shapes.len() {
            self.fail(format!(
                "function returns {} values here, but its ABI declares {}",
                exprs.len(),
                self.return_shapes.len()
            ))
        };
        let total: u32 = self.return_shapes.iter().map(|s| s.cells()).sum();
        let rets = self.alloc_stack(total);
        let mut ret = rets;
        for (e, &shape) in exprs.iter().zip(self.return_shapes) {
            match shape {
                Shape::Scalar => self.expr_into(e, ret),
                Shape::StackBuf(size) => {
                    let (base, actual) = self
                        .stack_of(e)
                        .unwrap_or_else(|| self.fail(format!("expected a StackBuf({size}) return, got `{e:?}`")));
                    if actual != size {
                        self.fail(format!("returned StackBuf has size {actual}, expected {size}"))
                    };
                    for k in 0..size {
                        self.copy(base + k, ret + k);
                    }
                }
            }
            ret += shape.cells();
        }
        self.emit(CStmt::Ret(Self::run(rets, total)));
    }

    /// If `callee` declares `Const` parameters, its specialization at these constants (`callee__L5_G3`), queued
    /// once, and the runtime arguments.
    pub(super) fn specialize<'a>(&mut self, callee: &str, args: &'a [Expr]) -> (String, Vec<&'a Expr>) {
        if callee == "main" {
            self.fail("`main` is the entry point, so it cannot be called")
        }
        let Some(def) = self.defs.get(callee).copied() else {
            return (callee.to_string(), args.iter().collect());
        };
        if !def.has_const_params() {
            return (callee.to_string(), args.iter().collect());
        }
        let substs = self.const_substs(def, args).unwrap_or_else(|e| self.fail(e));
        let mut name = format!("{callee}_");
        for (_, c) in &substs {
            match c {
                Expr::Lit(n) => write!(name, "_L{n}"),
                Expr::GPow(k) => write!(name, "_G{k}"),
                _ => unreachable!(),
            }
            .unwrap();
        }
        let runtime = def.params.iter().zip(args).filter(|(p, _)| p.kind != ParamKind::Const);
        if !self.queue.iter().any(|f| f.name == name) {
            if self.queue.len() >= 10_000 {
                self.fail("Const specialization explosion (recursive constants?)")
            };
            self.queue.push(Func {
                name: name.clone(),
                params: runtime.clone().map(|(p, _)| p.clone()).collect(),
                return_shapes: def.return_shapes.clone(),
                body: substitute_body(&def.body, &substs).into_owned(),
                inline: false,
            });
        }
        (name, runtime.map(|(_, a)| a).collect())
    }

    /// A call; one value per source-level return value (the first of a returned `StackBuf`'s run).
    pub(super) fn call(&mut self, callee: &str, args: &[Expr], n_ret: usize) -> Vec<V> {
        if callee == "keccak" || callee == "keccak_cells" {
            self.fail(format!(
                "{callee} is a statement: it writes the state or the digest into its `out` run"
            ))
        };
        self.inline_stack_ret = None;
        if self.defs.get(callee).is_some_and(|d| d.inline) {
            let dsts: Vec<V> = (0..n_ret).map(|_| self.fresh()).collect();
            self.call_into(callee, args, &dsts);
            return dsts;
        }
        let def = self.defs.get(callee).copied();
        if let Some(def) = def
            && def.return_shapes.len() != n_ret
        {
            self.fail(format!(
                "`{callee}` returns {} values, call binds {n_ret}",
                def.return_shapes.len()
            ))
        };
        let mut logical = Vec::with_capacity(n_ret);
        let mut physical = Vec::new();
        let mut binds = Vec::with_capacity(n_ret);
        for i in 0..n_ret {
            match def.map_or(Shape::Scalar, |d| d.return_shapes[i]) {
                Shape::Scalar => {
                    let dst = self.fresh();
                    logical.push(dst);
                    physical.push(dst);
                    binds.push(RetBind::Scalar);
                }
                Shape::StackBuf(size) => {
                    if size == 0 {
                        self.fail("a returned StackBuf must not be empty")
                    };
                    let base = self.alloc_stack(size);
                    logical.push(base);
                    physical.extend(base..base + size);
                    binds.push(RetBind::Stack(base, size));
                }
            }
        }
        self.lower_call(callee, args, None, &physical);
        self.inline_stack_ret = Some(binds);
        logical
    }

    /// Evaluate `callee(args)` into `dsts`, inlined when the callee is `@inline`.
    pub(super) fn call_into(&mut self, callee: &str, args: &[Expr], dsts: &[V]) {
        if callee == "keccak" || callee == "keccak_cells" {
            self.fail(format!("{callee} is a statement, not a value-returning call"))
        };
        if !self.try_inline(callee, args, dsts) {
            if let Some(def) = self.defs.get(callee) {
                if def.return_shapes.len() != dsts.len() {
                    self.fail(format!(
                        "`{callee}` returns {} values, call binds {}",
                        def.return_shapes.len(),
                        dsts.len()
                    ))
                };
                if def.return_shapes.iter().any(|s| *s != Shape::Scalar) {
                    self.fail("a normal function's multi-cell StackBuf return needs a `let` binding")
                };
            }
            self.lower_call(callee, args, None, dsts);
        }
    }

    fn const_substs<'a>(&self, def: &'a Func, args: &[Expr]) -> Result<Vec<(&'a str, Expr)>, String> {
        if args.len() != def.params.len() {
            return Err(format!("call to `{}`: wrong arity", def.name));
        }
        let mut substs = Vec::new();
        for (p, a) in def.params.iter().zip(args) {
            if p.kind == ParamKind::Const {
                let c = self.const_arg(a).ok_or_else(|| {
                    format!(
                        "argument for Const parameter `{}` of `{}` must be a compile-time \
                         constant, got `{a:?}`",
                        p.name, def.name
                    )
                })?;
                substs.push((p.name.as_str(), c));
            }
        }
        Ok(substs)
    }

    /// Original definitions take precedence over generated functions in the queue.
    fn callee_def(&self, callee: &str) -> Option<&Func> {
        self.defs
            .get(callee)
            .copied()
            .or_else(|| self.queue.iter().find(|f| f.name == callee))
    }

    /// The value of a single-value inlined return used in expression position: a folded address materializes, a
    /// one-cell run is its value, else `dst`.
    pub(super) fn take_inline_ret_cell(&mut self, dst: V) -> V {
        match self.inline_stack_ret.take().and_then(|b| b.into_iter().next()) {
            Some(RetBind::Gaddr(ga)) => self.materialize(ga),
            Some(RetBind::Stack(base, size)) => {
                if size != 1 {
                    self.fail("a multi-cell StackBuf return needs a `let` binding, not an expression use")
                };
                base
            }
            _ => dst,
        }
    }

    /// The literal a `Const` parameter takes: a `GEN ** k` stays a g-power, anything else must fold to a
    /// compile-time integer.
    fn const_arg(&self, a: &Expr) -> Option<Expr> {
        Some(match a {
            Expr::Lit(n) => Expr::Lit(*n),
            Expr::Gen => Expr::GPow(1),
            Expr::GPow(k) => Expr::GPow(*k),
            other => Expr::Lit(self.try_const_index(other)? as u128),
        })
    }
}
