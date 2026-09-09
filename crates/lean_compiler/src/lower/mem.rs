//! Addressing, and the store path: which cell a name means, and what a write to
//! it costs. Two rules, both of which have been broken here before.
//!
//! **Every index is bounds-checked, in every position.** A store's right-hand
//! side is an index as much as an expression is, and a slice checks its whole
//! SPAN rather than its first cell.
//!
//! **A store always emits, and the machine decides what it means.** If the cell
//! already holds a value the store is the write-once equality ASSERTION, which is
//! what makes `s[k] = <checked value>` pin a hint; if it does not, the store is
//! what gives the cell its value. The compiler tracks nothing to tell those
//! apart, so there is no state here that could disagree with the machine.

use super::*;

impl FnLower<'_> {
    /// Resolve an expression naming a run of consecutive cells: a whole
    /// `StackBuf`, a `StackBuf` slice, a `HeapBuf` slice with compile-time
    /// bounds, or a runtime-start heap slice `buf[i:i + k]` (whose length is
    /// the only thing its bounds reveal). Heap runs fold the buffer's symbolic
    /// shift and the slice start into the pointer offset.
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
                // Compile-time bounds: integer cell indexes `lo..hi` (frame
                // offsets for a stack, g-power exponents for the heap).
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
                // Runtime start (heap only): `buf[i:i + k]` with a runtime
                // g-power index `i` names the cells `buf·i·g^j`, j < k. The
                // `hi` bound cannot be evaluated, only shape-checked against
                // `lo`. One MUL folds `i` into the pointer.
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
                    // `heap_addr` bounds-checks ONE cell. A start that folds
                    // (`GEN ** k`, or a name bound to one) reaches this arm because
                    // it is not an INTEGER, yet its offset IS known, so the run's
                    // length has to be checked here or it never is.
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

    /// Address `arr[idx]` as `(base_cell, β)`. A constant g-power `idx` folds
    /// into `β` ([`Self::heap_base`]); a runtime index materializes the pointer.
    pub(super) fn heap_addr(&mut self, arr: &Expr, idx: &Expr) -> (Off, u32) {
        // A compile-time index that is a plain field constant but NOT a
        // g-power (`buf[0]`, `buf[2]`, an integer unroll var) can never name
        // a heap cell (cell k lives at `buf · g^k`) and would deref a wild
        // address at proving time. Reject it here, where the source is known.
        // A BARE literal index is rejected even now that `gaddr_of` reads `2^k`
        // as `g^k` in a pointer: `hb[2]` would silently mean cell 1, while slice
        // bounds stayed integer (`hb[2:4]` starts at cell 2), so one spelling
        // would name two different cells. An index built from `GEN` is fine, and
        // `1` is `g^0` either way.
        let bare_int = matches!(self.try_lit(idx), Some(n) if n != 1);
        if (bare_int || self.gaddr_of(idx).is_none())
            && let Some(c) = self.try_field_const(idx)
        {
            // Two reasons reach here and they read differently. A bare integer
            // index may well BE a g-power (4 is g²), and is rejected for being
            // ambiguous against slice syntax rather than for naming nothing.
            let why = match self.const_gpow(idx) {
                Some(k) => format!(
                    "is a plain integer naming cell {k}, while the slice `buf[n:n + 1]` reads the \
                     same number as cell n. Write `buf[GEN ** {k}]` and say which you mean"
                ),
                None => format!(
                    "folds to the field constant {:#x}:{:#x}, which is not a g-power, so it names \
                     no heap cell (did an integer index leak in from a StackBuf conversion?)",
                    c.c1, c.c0
                ),
            };
            self.fail(format!("heap index {why}"));
        }
        match self.gaddr_of(idx) {
            Some(GAddr { base: None, exp, .. }) => return self.heap_base(arr, exp),
            // A runtime-base index carrying a constant g-power shift
            // (`buf[cursor * GEN ** k]`): fold the whole constant part (the
            // index's shift plus `arr`'s own symbolic shift) into `β`, and
            // emit ONE pointer multiply instead of materializing g^k.
            Some(GAddr {
                base: Some(ib), exp, ..
            }) => {
                if let Some(ga) = self.gaddr_of(arr)
                    && let (Some(ab), Some(total)) = (ga.base, ga.exp.checked_add(exp))
                    && total <= FOLD_MAX
                {
                    let ptr = self.pure(PureOp::Mul, ab, ib);
                    return (ptr, total as u32);
                }
            }
            None => {}
        }
        // Fall back to the constant-g-power-factor fold (a runtime index still
        // materializes the pointer `MUL`, with any constant factor in `β`).
        self.array_ptr(arr, idx)
    }

    /// Compile-time bounds check: when `arr` resolves to a sized `HeapBuf`
    /// (directly or through shifted aliases) and the whole index is the
    /// compile-time exponent `exp`, reject `exp + span > size`. Runtime
    /// indices are not checked (their value is not known here).
    pub(super) fn check_heap_bound(&self, arr: &Expr, extra: u128, span: u128) {
        let Some(ga) = self.gaddr_of(arr) else { return };
        let (Some(base), Some(exp)) = (ga.base, ga.exp.checked_add(extra)) else {
            return;
        };
        // A frame pointer from `addr(sb)`: `exp` is an absolute frame offset and
        // `base` is the shared `fp` cell, so the run comes from the address's own
        // provenance rather than from `heap_sizes`.
        if let Some((start, len)) = ga.run {
            let (start, len) = (start as u128, len as u128);
            if exp < start || exp + span > start + len {
                let off = exp.saturating_sub(start); // `exp < start` is unreachable: gmul only adds
                let what = if span == 1 {
                    format!("index {off}")
                } else {
                    format!("slice {off}:{}", off + span)
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
        if exp + span > size {
            // Several names can share a cell, so pick the first alphabetically
            // rather than the first the map happens to yield: the same program
            // must blame the same name on every build.
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
                "heap slice {exp}:{} out of bounds for `{name}` (HeapBuf size {size})",
                exp + span
            ));
        }
    }

    /// `addr(sb)`: the g-address `fp·g^base` of a `StackBuf`'s first cell, so a
    /// frame run can be pointed at (indexed at runtime, or handed to a callee)
    /// while its own accesses stay direct frame cells. Materializing `fp` is the
    /// ISA's one cost here, amortized per function ([`Self::self_fp`]); the
    /// address is a folded [`GAddr`], so `addr(sb) * GEN ** k` stays virtual.
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
        GAddr {
            base: Some(self.self_fp()),
            exp: base as u128,
            run: Some((base, len)),
        }
    }

    /// Address `arr·g^extra` as `(base_cell, β)`, folding `arr`'s symbolic shift
    /// and the constant `extra` into `β`. Falls back to a materialized pointer
    /// (`β = 0`) when there is no runtime base or the offset exceeds [`FOLD_MAX`].
    fn heap_base(&mut self, arr: &Expr, extra: u128) -> (Off, u32) {
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
        let k = self.const_cell(g_pow_u128(extra).into());
        (self.pure(PureOp::Mul, a, k), 0)
    }

    /// Resolve a heap access `arr[idx]` to a `DEREF`-ready pair: a cell
    /// holding a pointer `p` and a compile-time exponent `o2`, the accessed
    /// cell being `m[p·g^o2]` (heap addressing in the exponent: cell `g^k`
    /// of the buffer sits at `arr·g^k`). The fallback of [`Self::heap_addr`],
    /// which has already folded away a wholly constant index: here a constant
    /// g-power *factor* still goes into the `o2` immediate, so only the
    /// runtime factor costs a pointer `MUL`.
    fn array_ptr(&mut self, arr: &Expr, idx: &Expr) -> (Off, u32) {
        // `buf[r * GEN ** k]` (either factor order): o2 takes the constant,
        // the pointer MUL takes only the runtime factor `r`.
        if let Expr::Mul(a, b) = idx {
            for (c, r) in [(a, b), (b, a)] {
                if let Some(k) = self.const_gpow(c) {
                    let (la, lr) = (self.expr(arr), self.expr(r));
                    return (self.pure(PureOp::Mul, la, lr), k);
                }
            }
        }
        let (la, li) = (self.expr(arr), self.expr(idx));
        (self.pure(PureOp::Mul, la, li), 0)
    }

    /// Realize a [`GAddr`] into a frame cell holding its value: a constant is one
    /// `SET`; a base with no shift is already that cell; a shifted base is a
    /// `SET`+`MUL`.
    pub(super) fn materialize(&mut self, ga: GAddr) -> Off {
        match ga {
            GAddr {
                base: Some(c), exp: 0, ..
            } => c,
            GAddr { base, exp, .. } => {
                let k = self.const_cell(g_pow_u128(exp).into());
                let Some(c) = base else { return k };
                self.pure(PureOp::Mul, c, k)
            }
        }
    }

    /// If `e` names a `StackBuf` variable, its `(base, size)`.
    pub(super) fn stack_of(&self, e: &Expr) -> Option<(Off, u32)> {
        match e {
            Expr::Var(v) => self.scope.stack(v),
            _ => None,
        }
    }

    /// Allocate `n` *consecutive* fresh frame cells (a stack run), returning the
    /// base. Nothing else may `fresh()` between them, so they stay adjacent.
    pub(super) fn alloc_stack(&mut self, n: u32) -> Off {
        let base = self.next;
        self.next += n;
        base
    }
}
