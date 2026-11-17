//! Addressing: which value a name means, the runs of values a slice names, and the pointer and `β` offset a heap
//! access reads through. Every index is bounds-checked, in every position.

use super::*;

impl FnExpand<'_> {
    /// The run of values `e` names: a whole `StackBuf`, a `StackBuf` slice, a `HeapBuf` slice with compile-time
    /// bounds, or a runtime-start heap slice `buf[i:i + k]`.
    pub(super) fn cell_run(&mut self, e: &Expr) -> CellRun {
        match e {
            Expr::Var(_) => {
                let (base, len) = self.stack_of(e).unwrap_or_else(|| {
                    self.fail(format!(
                        "only a StackBuf names a run of cells unsliced, got `{e:?}`; slice a \
                             HeapBuf instead: `buf[lo:lo + k]`"
                    ))
                });
                CellRun::Stack { base, len }
            }
            Expr::Slice(arr, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                (Some(lo), Some(hi)) => {
                    if lo >= hi {
                        self.fail(format!("empty slice {lo}:{hi}"))
                    };
                    let len = hi - lo;
                    if let Some((base, size)) = self.stack_of(arr) {
                        if hi > size {
                            self.fail(format!("slice {lo}:{hi} out of bounds (StackBuf size {size})"))
                        };
                        CellRun::Stack { base: base + lo, len }
                    } else {
                        self.check_heap_bound(arr, lo as u128, len as u128);
                        let (ptr, lo) = self.heap_base(arr, lo as u128);
                        CellRun::Heap { ptr, lo, len }
                    }
                }
                _ => {
                    if self.stack_of(arr).is_some() {
                        self.fail(
                            "a StackBuf slice needs compile-time bounds (frame offsets are baked into the bytecode)",
                        )
                    };
                    let k = plus_k(lo, hi).unwrap_or_else(|| {
                        self.fail(format!("a runtime slice must be `buf[i:i + k]`, got `{lo:?}:{hi:?}`"))
                    });
                    let len =
                        u32::try_from(k).unwrap_or_else(|_| self.fail(format!("slice length {k} does not fit in u32")));
                    if len == 0 {
                        self.fail(format!(
                            "a runtime slice `{lo:?}:{hi:?}` has length 0, so it names no cell"
                        ))
                    };
                    if let Some(GAddr { base: None, exp, .. }) = self.gaddr_of(lo) {
                        self.check_heap_bound(arr, exp, u128::from(len));
                    }
                    let (ptr, lo) = self.heap_addr(arr, lo);
                    CellRun::Heap { ptr, lo, len }
                }
            },
            other => self.fail(format!(
                "expected a StackBuf, a StackBuf slice, or a HeapBuf slice, got `{other:?}`"
            )),
        }
    }

    /// Address `arr[idx]` as `(pointer, β)`: a constant g-power index folds into `β`, a runtime one into the
    /// pointer.
    pub(super) fn heap_addr(&mut self, arr: &Expr, idx: &Expr) -> (V, u32) {
        let bare_int = matches!(self.try_lit(idx), Some(n) if n != 1);
        let known = self.eval(idx);
        if (bare_int || known.addr.is_none())
            && let Some(c) = known.field
        {
            let why = match (known.diverging_readings(), small_gpow(c)) {
                (Some((n, _)), _) => format!(
                    "reads as the integer {n} but as the field constant {:#x}:{:#x}, so it would \
                     name two different cells. Write `buf[GEN ** k]` for cell k",
                    c.c1, c.c0
                ),
                (None, Some(k)) if bare_int => format!(
                    "is a plain integer naming cell {k}, while the slice `buf[n:n + 1]` reads the \
                     same number as cell n. Write `buf[GEN ** {k}]` and say which you mean"
                ),
                (None, Some(k)) => return self.heap_base(arr, k),
                (None, None) => format!(
                    "folds to the field constant {:#x}:{:#x}, which is not a g-power up to g^{FOLD_MAX}, \
                     so it names no heap cell (did an integer index leak in from a StackBuf conversion?)",
                    c.c1, c.c0
                ),
            };
            self.fail(format!("heap index {why}"));
        }
        match known.addr {
            Some(GAddr { base: None, exp, .. }) => return self.heap_base(arr, exp),
            Some(GAddr {
                base: Some(ib), exp, ..
            }) => {
                if let Some(ga) = self.gaddr_of(arr)
                    && let (Some(ab), Some(total)) = (ga.base, ga.exp.checked_add(exp))
                    && total <= FOLD_MAX
                {
                    let ptr = self.pure_mul(ab, ib);
                    return (ptr, total as u32);
                }
            }
            None => {}
        }
        self.array_ptr(arr, idx)
    }

    /// Compile-time bounds check: when `arr` is a sized `HeapBuf` or an `addr` pointer (shifted or not) and the
    /// access is at the compile-time exponent `exp`, reject `exp + span` past its size.
    pub(super) fn check_heap_bound(&self, arr: &Expr, extra: u128, span: u128) {
        let Some(ga) = self.gaddr_of(arr) else { return };
        let Some(base) = ga.base else { return };
        let exp = ga.exp.saturating_add(extra);
        let end = exp.saturating_add(span);
        if let Some(len) = ga.run {
            if end > u128::from(len) {
                let what = if span == 1 {
                    format!("index {exp}")
                } else {
                    format!("slice {exp}:{end}")
                };
                self.fail(format!(
                    "frame {what} out of bounds for the StackBuf({len}) named by `addr`"
                ));
            }
            return;
        }
        let Some(&size) = self.heap_sizes.get(&base) else {
            return;
        };
        if end > size {
            let name = self
                .scope
                .names
                .iter()
                .filter(|(_, b)| matches!(b.val, Binding::Scalar(c) if c == base))
                .map(|(n, _)| n.as_str())
                .min()
                .unwrap_or("?");
            if span == 1 {
                self.fail(format!(
                    "heap index {exp} out of bounds for `{name}` (HeapBuf size {size})"
                ));
            }
            self.fail(format!(
                "heap slice {exp}:{end} out of bounds for `{name}` (HeapBuf size {size})"
            ));
        }
    }

    /// `addr(sb)`: a pointer to the run of a `StackBuf`, the atom `p = addr [run]`.
    pub(super) fn stack_addr(&mut self, args: &[Expr]) -> GAddr {
        if args.len() != 1 {
            self.fail("addr(buf) takes one StackBuf")
        };
        let (base, len) = self.stack_of(&args[0]).unwrap_or_else(|| {
            self.fail(format!(
                "addr() names a frame run, so it takes a StackBuf, got `{:?}`",
                args[0]
            ))
        });
        let p = self.fresh();
        self.frame_addr(p, base, len);
        self.addr_runs.insert(p, (base, len));
        GAddr {
            base: Some(p),
            exp: 0,
            run: Some(len),
        }
    }

    /// Address `arr·g^extra` as `(pointer, β)`, folding `arr`'s shift and `extra` into `β` up to [`FOLD_MAX`].
    fn heap_base(&mut self, arr: &Expr, extra: u128) -> (V, u32) {
        self.check_heap_bound(arr, extra, 1);
        if let Some(ga) = self.gaddr_of(arr)
            && let (Some(base), Some(exp)) = (ga.base, ga.exp.checked_add(extra))
            && exp <= FOLD_MAX
        {
            return (base, exp as u32);
        }
        let a = self.expr(arr);
        if extra == 0 {
            return (a, 0);
        }
        let k = self.const_cell(F64::G.pow(extra).into());
        (self.pure_mul(a, k), 0)
    }

    /// A runtime heap index: a constant g-power factor folds into `β`, the rest multiplies the pointer.
    fn array_ptr(&mut self, arr: &Expr, idx: &Expr) -> (V, u32) {
        if let Expr::Mul(a, b) = idx {
            for (c, r) in [(a, b), (b, a)] {
                if let Some(k) = self.const_gpow(c) {
                    let (la, lr) = (self.expr(arr), self.expr(r));
                    return (self.pure_mul(la, lr), k);
                }
            }
        }
        let (la, li) = (self.expr(arr), self.expr(idx));
        (self.pure_mul(la, li), 0)
    }

    /// A value holding an address: a constant is a constant; a base with no shift is the base; a shifted `addr`
    /// pointer is the `addr` of its run from the shift on; another shifted base `c·g^exp` is a product, from the
    /// nearest materialization `c·g^e` below whose distance `g^(exp-e)` is a constant set in this scope, when
    /// `g^exp` is not one, else from `c` and `g^exp`. A second materialization of the same `c·g^exp` repeats the
    /// first's atoms on fresh values.
    pub(super) fn materialize(&mut self, ga: GAddr) -> V {
        match ga {
            GAddr {
                base: Some(c), exp: 0, ..
            } => c,
            GAddr { base: None, exp, .. } => self.const_cell(F64::G.pow(exp).into()),
            GAddr { base: Some(c), exp, .. } => {
                if let Some(&(base, len)) = self.addr_runs.get(&c) {
                    let p = self.fresh();
                    let skip = u32::try_from(exp).unwrap_or(len).min(len);
                    self.frame_addr(p, base + skip, len - skip);
                    return p;
                }
                let mats = self.scope.mats.get(&c).cloned().unwrap_or_default();
                if let Some(m) = mats.iter().find(|m| m.exp == exp) {
                    let k = self.const_cell(F64::G.pow(m.dist).into());
                    return self.pure_mul(m.src, k);
                }
                let has = |s: &Self, e: u128| s.scope.consts.contains(&F64::G.pow(e).into());
                let from = if has(self, exp) {
                    None
                } else {
                    mats.iter()
                        .filter(|m| m.exp < exp && has(self, exp - m.exp))
                        .max_by_key(|m| m.exp)
                };
                let (src, dist) = match from {
                    Some(m) => (m.out, exp - m.exp),
                    None => (c, exp),
                };
                let k = self.const_cell(F64::G.pow(dist).into());
                let o = self.pure_mul(src, k);
                self.scope
                    .mats
                    .entry(c)
                    .or_default()
                    .push(Mat { exp, out: o, src, dist });
                o
            }
        }
    }

    /// If `e` names a `StackBuf` variable, its run.
    pub(super) fn stack_of(&self, e: &Expr) -> Option<(V, u32)> {
        match e {
            Expr::Var(v) => self.scope.stack(v),
            _ => None,
        }
    }

    /// A fresh run holding the heap run of `len` cells at `ptr`'s g-power offset `lo`, one load each.
    pub(super) fn heap_to_stack(&mut self, ptr: V, lo: u32, len: u32) -> V {
        let run = self.alloc_stack(len);
        self.load_run(ptr, lo, len, run);
        run
    }

    /// One load per cell between the heap run of `len` cells at `ptr`'s offset `lo` and the run at `run`.
    pub(super) fn load_run(&mut self, ptr: V, lo: u32, len: u32, run: V) {
        for k in 0..len {
            self.atom(Atom::Load(run + k, ptr, lo + k));
        }
    }
}
