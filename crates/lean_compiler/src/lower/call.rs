//! The call boundary: arguments in, return values out, and the two ways a
//! callee can disappear into its caller.
//!
//! Every frame is laid out by [`Abi`], and CALLER AND CALLEE MUST AGREE ON THE
//! ARITY: each places the return area from its own idea of the argument count,
//! so a missing argument leaves the callee's cell unwritten and therefore
//! prover-chosen, and a surplus one overwrites the callee's first return slot.
//! Two paths need the check, the ordinary one and the fused `match`
//! dispatch.
//!
//! A callee vanishes into its caller two ways. `Const` specialization
//! monomorphises it per constant tuple; `@inline` expands the body into the
//! caller's own frame, so the caller's `one`, `self_fp` and constant cells stay
//! valid across it and only the name bindings reset.

use super::*;
use std::borrow::Cow;

/// How an inlined tail return binds in the caller: a `StackBuf` run and a folded
/// g-address alias at zero copies, while anything else (a plain scalar, or a real
/// call, which records no [`RetBind`]) takes the destination cell it wrote.
pub(super) fn ret_binding(b: Option<RetBind>, dst: Off) -> Binding {
    match b {
        Some(RetBind::Stack(base, size)) => Binding::Stack(base, size),
        Some(RetBind::Gaddr(ga)) => Binding::Gaddr(ga),
        _ => Binding::Scalar(dst),
    }
}

fn substitute_body<'a>(body: &'a [Stmt], substs: &[(&str, Expr)]) -> Cow<'a, [Stmt]> {
    substs.iter().fold(Cow::Borrowed(body), |body, (name, value)| {
        Cow::Owned(subst_stmts(&body, name, value))
    })
}

/// A single tail return, preceded by statements that can be expanded in the caller's frame.
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
        // Ordinary calls allocate their own frames.
        | StmtKind::Call(..) => true,
        StmtKind::If { then, els, .. } => then.iter().all(stmt_inline_safe) && els.iter().all(stmt_inline_safe),
        StmtKind::Unroll { body, .. } => body.iter().all(stmt_inline_safe),
        _ => false,
    }
}

impl FnLower<'_> {
    /// Lower a call into the caller's return cells. Distinct `match` arms may
    /// share these write-once destinations.
    pub(super) fn lower_call(&mut self, callee: &str, args: &[Expr], cond: Option<Off>, dsts: &[Off], tail: bool) {
        // Every parameter must be supplied. A missing argument leaves the
        // callee's argument cell unwritten, hence prover-chosen, so an `assert`
        // reading it is vacuous; a surplus one lands on the callee's first
        // return slot, because caller and callee place the return area from
        // their own idea of the argument count. Only `specialize` checked this,
        // and only for a callee declaring `Const` parameters.
        match self.callee_def(callee).map(|f| f.params.len()) {
            Some(want) if want != args.len() => {
                let plural = if want == 1 { "argument" } else { "arguments" };
                self.fail(format!("`{callee}` takes {want} {plural}, got {}", args.len()))
            }
            // Nothing by that name is going to be lowered, so the entry pc it
            // needs will not exist. Caught here, where there is a line: a typo, a
            // statement-only builtin used as a value (`x = assert_in_k(a, b)`),
            // or an `@inline` callee reached where inlining did not happen, all
            // used to die later in `resolve` as a bare `no entry found for key`.
            None => self.fail(format!(
                "no function named `{callee}`. A builtin that writes into a destination \
                 (`blake2s`, `assert_in_k`, a `hint_*`) is a statement and returns nothing, so it \
                 cannot be called for a value"
            )),
            _ => {}
        }
        let (callee, args) = self.specialize(callee, args);
        let (callee, args) = (callee.as_str(), args.as_slice());
        // Each argument goes where its SHAPE puts it: a `StackBuf(n)` parameter
        // takes n consecutive cells, exactly as a `StackBuf(n)` return value
        // does. Resolved before the frame pointer is allocated, as before.
        let shapes = self
            .callee_def(callee)
            .map(|f| f.param_shapes().collect::<Vec<_>>())
            .unwrap_or_else(|| vec![Shape::Scalar; args.len()]);
        let mut arg_offs: Vec<(Off, Off)> = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let base = Abi::arg(shapes.iter().copied(), i);
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
                    for k in 0..n {
                        let cell = src + k;
                        arg_offs.push((base + k, cell));
                    }
                }
                Shape::Scalar => {
                    let cell = self.expr(a);
                    arg_offs.push((base, cell));
                }
            }
        }
        let callee_arg_cells = Abi::arg_cells(shapes.iter().copied());
        let nfp = self.fresh();
        let entry = self.fresh();
        // Resolve the jump condition up front: `self.one()` may emit a `SET`, and
        // nothing may sit between the retpc `DEREF` and the `JUMP` (the `g²·pc`
        // return target assumes the `JUMP` is exactly one instruction later).
        let oc = cond.unwrap_or_else(|| self.one());
        self.set(entry, KVal::Entry(callee.to_string()));

        // The frame-pointer hint fires before the first DEREF that reads `nfp`.
        self.pending.push(Hint::AllocFrame {
            ptr: nfp,
            callee: callee.to_string(),
        });
        for &(off, ao) in &arg_offs {
            self.deref(nfp, off, ao, DerefMode::Cell);
        }
        if tail {
            // Tail call: hand the callee OUR return target, so it returns to our
            // caller and we are never resumed. Cells 0/1 of this frame already
            // hold that target (written by whoever called us).
            self.deref(nfp, 1, 1, DerefMode::Cell); // retfp := our retfp
            self.deref(nfp, 0, 0, DerefMode::Cell); // retpc := our retpc
        } else {
            self.deref(nfp, 1, 0, DerefMode::Fp); // retfp
            self.deref(nfp, 0, 0, DerefMode::Pc); // retpc = g²·pc
        }
        self.emit(LOp::Jump { oc, od: entry, of: nfp });

        for (i, &d) in dsts.iter().enumerate() {
            self.deref(nfp, Abi::ret(callee_arg_cells, i as u32), d, DerefMode::Cell);
        }
    }

    /// `names = match(log(x), …, lambda k: f(args, k))` fused: the arms all
    /// call one of `callees` (specializations sharing the arg/return layout) with
    /// the same runtime `args`, so build the callee frame **once** and let the
    /// dispatch jump straight into the selected entry, which returns to the join.
    /// Each taken arm is then just the trampoline's `SET entry; JUMP`: no
    /// per-arm frame setup, call, or return jump.
    pub(super) fn lower_dispatched_call(&mut self, targets: &[Expr], x: &Expr, callees: &[String], rt_args: &[&Expr]) {
        // The arms share ONE frame, so they must share one argument layout too:
        // a `StackBuf` parameter in one callee and a scalar in another at the
        // same position would put the return area in two places. The arity check
        // below is the count; this is the widths.
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
            // Fused dispatch writes one cell per argument; only scalar parameters fit.
            if let Some(i) = shared.param_shapes().position(|s| s != Shape::Scalar) {
                self.fail(format!(
                    "a `match` arm cannot pass a `StackBuf` parameter (parameter {i} of `{}`): the \
                     fused dispatch writes one cell per argument. Give the arms `Const` arguments so each \
                     specializes into its own call instead of fusing",
                    callees.first().map(String::as_str).unwrap_or("?")
                ))
            }
        }
        let n_args = rt_args.len() as u32;
        // The join below reads one return cell per bound name, so every callee has
        // to declare exactly that many. Unchecked, a name past a callee's arity
        // `DEREF`s a frame offset nothing on that path writes, and since the shared
        // frame is sized to the LARGEST callee the offset exists: the surplus name
        // binds a prover-chosen word. The non-fused path enforces this
        // ([`Self::call_into`]), so leaving it out here means one source is rejected
        // by one lowering of `match` and silently miscompiled by the other.
        for callee in callees {
            // A fused dispatch enters ONE real function per arm, so an `@inline`
            // callee has no entry pc to jump to: it is expanded at a call site
            // and never lowered on its own. This path does not consult
            // `try_inline`, so without saying so the call reached the assembler
            // and died there indexing a HashMap, with no line and no name.
            if self.defs.get(callee.as_str()).is_some_and(|d| d.inline) {
                self.fail(format!(
                    "`@inline {callee}` cannot be a `match` arm's callee: the arms dispatch to \
                     one real function, and an `@inline` body is expanded at its call site rather \
                     than lowered. Drop `@inline`, or give the arms `Const` arguments so each \
                     specializes instead of fusing"
                ))
            }
            // Arguments for the same reason as returns below: the shared frame
            // is sized to the largest callee, so a callee expecting more than
            // the arms supply reads a cell that exists and nothing writes.
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

        // Shared callee frame: args, retfp, and retpc = the join (so the callee
        // returns straight past the dispatch). Evaluated once.
        let arg_offs: Vec<Off> = rt_args.iter().map(|a| self.expr(a)).collect();
        let xo = self.expr(x);
        let one = self.one();
        let sfp = self.self_fp();

        let nfp = self.fresh();
        self.pending.push(Hint::AllocFrameMax {
            ptr: nfp,
            callees: callees.to_vec(),
        });
        for (i, &ao) in arg_offs.iter().enumerate() {
            self.deref(
                nfp,
                Abi::arg(std::iter::repeat_n(Shape::Scalar, rt_args.len()), i),
                ao,
                DerefMode::Cell,
            );
        }
        self.deref(nfp, Abi::RET_FP, 0, DerefMode::Fp);
        let join_cell = self.fresh();
        let join_set = self.code.len();
        self.set(join_cell, KVal::Local(0)); // patched: the join pc
        self.deref(nfp, Abi::RET_PC, join_cell, DerefMode::Cell); // retpc = join

        let kset = self.emit_dispatch(xo, one, sfp);

        // Trampoline: slot j enters `callees[j]` with fp = nfp; the callee's own
        // `return` jumps to retpc (the join) in the caller frame.
        self.patch_local(kset, self.code.len());
        self.emit_slots(callees.len(), one, nfp, |j| KVal::Entry(callees[j].clone()));

        // Join: read the return values (written by whichever callee ran).
        self.patch_local(join_set, self.code.len());
        for (i, &r) in rcells.iter().enumerate() {
            self.deref(nfp, Abi::ret(n_args, i as u32), r, DerefMode::Cell);
        }

        self.bind_targets(&binds);
    }

    /// Inline an `@inline` `callee(args)` into the current frame, binding its
    /// return values straight into `dsts`: no frame setup, no argument/return
    /// plumbing, no call/return jumps. Returns `false` for a non-`@inline`
    /// callee (the caller emits a real call). Panics if an `@inline` function
    /// isn't inlinable ([`body_inlinable`]) or its `Const` args don't resolve.
    pub(super) fn try_inline(&mut self, callee: &str, args: &[Expr], dsts: &[Off]) -> bool {
        let Some(def) = self.defs.get(callee).copied().filter(|d| d.inline) else {
            return false;
        };
        let substs = self
            .const_substs(def, args)
            .unwrap_or_else(|_| self.fail(format!("`@inline {callee}`: bad arity or unresolved Const argument")));
        let body = substitute_body(&def.body, &substs);
        let n_ret = def.return_shapes.len();
        if n_ret != dsts.len() {
            self.fail(format!(
                "`@inline {callee}` returns {n_ret} values, call binds {}",
                dsts.len()
            ))
        };
        if !body_inlinable(&body) {
            self.fail(format!("`@inline {callee}` requires one tail `return`, with no nested returns, tuple assignments, mul_range loops, or match"))
        };
        if self.inline_calls.iter().any(|f| f == callee) {
            self.fail(format!(
                "recursive @inline expansion is not supported: {} -> {callee}",
                self.inline_calls.join(" -> ")
            ))
        };
        // Bind the params from the caller-scope arguments (symbolically where we
        // can, so a shifted-pointer arg keeps folding into `β`; a `StackBuf` arg
        // aliases its cell run), then lower the body in a fresh variable
        // environment, since a function sees only its params. The frame, `one`,
        // `self_fp`, and range-check bounds stay the caller's: the inlined code
        // runs in the caller's frame, so they fit.
        let mut binds: Vec<(String, Binding)> = Vec::new();
        for (p, a) in def.params.iter().zip(args) {
            if p.kind == ParamKind::Const {
                continue;
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
        // Only the name bindings reset: the inlined body runs in the caller's
        // frame, so the caller's `one`, `self_fp`, constant and bound cells all
        // still name valid cells and stay live.
        let saved = std::mem::take(&mut self.scope.names);
        for (p, b) in binds {
            self.check_not_reserved(&p);
            self.scope.names.insert(p, Bound { val: b, int: None });
        }
        let saved_ret = self.inline_ret.replace(dsts.to_vec());
        // The body lowers through the CALLER's `FnLower`, so its statements move
        // `cur_line` into the callee. Restoring it is what keeps the rest of the
        // caller's expression attributed to the call site rather than to whatever
        // line the callee happened to end on.
        let saved_line = self.cur_line;
        self.inline_calls.push(callee.to_string());
        for s in body.iter() {
            self.stmt(s);
        }
        let popped = self.inline_calls.pop();
        debug_assert_eq!(popped.as_deref(), Some(callee));
        self.inline_ret = saved_ret;
        self.cur_line = saved_line;
        self.scope.names = saved;
        true
    }

    pub(super) fn lower_return(&mut self, exprs: &[Expr]) {
        // Inlined (`@inline`): bind the return values into the caller's cells
        // and fall through: this is the body's tail return, so no jump is needed.
        if let Some(dsts) = self.inline_ret.take() {
            // Each returned value is bound into the caller independently, exactly
            // as a `let name = <that expr>` would: a `StackBuf` or a folded
            // g-address hands over its run/pointer (alias, not copies: allocated
            // in the caller's frame, so it outlives the inline scope), a scalar is
            // copied into its dst cell. The per-slot record lets the caller's
            // `let`/tuple pick the right binding, so a fused
            // `fs, x, cur = fs_next(fs, cur)` returns a StackBuf, a scalar, and an
            // advanced cursor together.
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
            return; // a `return` in main is a no-op; main halts via the trailing sentinel jump (lower_func).
        }
        let ret_base = Abi::ret(self.arg_cells, 0);
        if exprs.len() != self.return_shapes.len() {
            self.fail(format!(
                "function returns {} values here, but its ABI declares {}",
                exprs.len(),
                self.return_shapes.len()
            ))
        };
        // Each logical value lands straight in its flattened return area. A
        // StackBuf is copied cell-by-cell because its callee-frame offsets are
        // not meaningful after control returns to the caller.
        let mut ret = ret_base;
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
                        let src = base + k;
                        self.copy(src, ret + k);
                    }
                }
            }
            ret += shape.cells();
        }
        let one = self.one();
        self.emit(LOp::Jump { oc: one, od: 0, of: 1 });
    }

    /// If `callee` declares `Const` parameters, monomorphize: the constant
    /// arguments (literals, `GEN ** k`, or literal-bound names) substitute into a
    /// copy of the callee, queued once per distinct constant tuple and named
    /// `callee__L5_G3`-style, and only the runtime arguments remain.
    pub(super) fn specialize<'a>(&mut self, callee: &str, args: &'a [Expr]) -> (String, Vec<&'a Expr>) {
        let Some(def) = self.defs.get(callee).copied() else {
            return (callee.to_string(), args.iter().collect()); // loop helpers, unknown names
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

    /// Lower a call; returns one caller offset per source-level return value.
    /// A real-call StackBuf return is flattened into consecutive ABI cells and
    /// copied into a fresh consecutive run in the caller. `inline_stack_ret`
    /// describes those logical bindings to the surrounding let/tuple lowering.
    pub(super) fn call(&mut self, callee: &str, args: &[Expr], n_ret: usize) -> Vec<Off> {
        if callee == "blake2s" {
            self.fail("blake2s is a statement: `blake2s(a, b, out)` writes the digest into the 2-cell stack run `out`")
        };
        self.inline_stack_ret = None;
        if self.defs.get(callee).is_some_and(|d| d.inline) {
            let dsts: Vec<Off> = (0..n_ret).map(|_| self.fresh()).collect();
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
        self.lower_call(callee, args, None, &physical, false);
        self.inline_stack_ret = Some(binds);
        logical
    }

    /// Evaluate `callee(args)` into `dsts`, inlining the callee when it is
    /// `@inline` ([`Self::try_inline`]), else a real call.
    pub(super) fn call_into(&mut self, callee: &str, args: &[Expr], dsts: &[Off]) {
        if callee == "blake2s" {
            self.fail("blake2s is a statement, not a value-returning call")
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
            self.lower_call(callee, args, None, dsts, false);
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

    /// Consume the [`RetBind`] a single-value inlined tail return recorded,
    /// for a call in EXPRESSION position (embedded in arithmetic, a store
    /// RHS, a single-target match arm): there is no name to alias-bind, so an
    /// aliased return materializes into a plain cell (free for a var / an
    /// exp-0 g-address; one `MUL` for a shifted pointer). `dst` is the call's
    /// destination cell, already written by a real call or a plain-scalar
    /// return, so it is the fallback.
    pub(super) fn take_inline_ret_cell(&mut self, dst: Off) -> Off {
        match self.inline_stack_ret.take().and_then(|b| b.into_iter().next()) {
            Some(RetBind::Gaddr(ga)) => self.materialize(ga),
            Some(RetBind::Stack(base, size)) => {
                if size != 1 {
                    self.fail("a multi-cell StackBuf return needs a `let` binding, not an expression use")
                };
                // The run's first cell: a single returned value sits there, and a
                // `let` consumer reaches the same one by binding the run
                // ([`ret_binding`]).
                base
            }
            _ => dst,
        }
    }
    /// The value a `Const` parameter takes, as the literal that substitutes for
    /// it: a `GEN ** k` argument stays a g-power, everything else must fold to a
    /// compile-time integer (a bound name, a const-array element `DEPTH[lvl]`,
    /// `len(...)`, index arithmetic over other `Const` params). `None` when it
    /// does not fold.
    fn const_arg(&self, a: &Expr) -> Option<Expr> {
        Some(match a {
            Expr::Lit(n) => Expr::Lit(*n),
            Expr::Gen => Expr::GPow(1),
            Expr::GPow(k) => Expr::GPow(*k),
            other => Expr::Lit(self.try_const_index(other)? as u128),
        })
    }
}
