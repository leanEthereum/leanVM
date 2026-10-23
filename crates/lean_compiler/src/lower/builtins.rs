//! The precompile and the hints: the two places a value arrives without an
//! instruction computing it.
//!
//! `keccak` is a STATEMENT, not an expression: it writes the sponge state into a
//! run the caller names, so a pre-written destination checks the digest instead
//! of computing it, by the same write-once rule as any store.
//!
//! A hint writes values the prover chose and the circuit did not, so **the
//! program must constrain them**. A hint names its destination's PHYSICAL cells,
//! and since every store emits there is nothing for the compiler to prepare: a
//! later `s[k] = <checked value>` is a second write of that cell, which is the
//! assertion that pins the hinted value.

use super::*;

impl FnLower<'_> {
    /// `keccak(a, b, out, tail=, len=)`: the Keccak-256 of a message of at most 128 bytes, one
    /// `KECCAK` instruction. The message cells are `a ‖ b ‖ tail` (two, two and four cells;
    /// `tail` omitted is none), and the message is their first `len` bytes (by default all of
    /// them, 64 bytes without `tail` and 128 with). A cell wholly past `len` must be a literal
    /// zero; the bytes past `len` in the cell where the message ends must be zero, unchecked.
    ///
    /// The output is the 13-cell state, its first two cells the digest. A 13-cell
    /// `out` receives it (a heap run through the stack), a 2-cell `out` just the
    /// digest (write-once: a pre-written `out` asserts it).
    ///
    /// `cap=` is the Fiat-Shamir duplex step in overwrite mode instead, with no padding: the
    /// eight message cells overwrite lanes `0..16`, and lanes `16..25`, the transcript's
    /// capacity, are `cap`'s, the five cells a previous output ends with (`cap` that 13-cell
    /// output or those five cells). Lane 16 is in Keccak-256's 17-lane rate, but the
    /// transcript keeps it.
    fn lower_keccak(&mut self, args: &[Expr]) {
        let kwargs = self.keccak_kwargs(args, "keccak", &["a", "b", "out"], &["tail", "len", "cap"]);
        let mut cells = self.keccak_operand(&args[0], 2);
        cells.extend(self.keccak_operand(&args[1], 2));
        if let Some(tail) = kwargs.get("tail") {
            cells.extend(self.keccak_operand(tail, 4));
        }
        if let Some(cap) = kwargs.get("cap") {
            if kwargs.contains_key("len") {
                self.fail("keccak cap= is an overwrite duplex step: it takes no len=")
            }
            let cap = self.prev_state(cap, 5).unwrap_or_else(|| {
                self.fail(format!(
                    "keccak cap= must be a previous {STATE_CELLS}-cell output or its last five cells"
                ))
            });
            cells.resize(8, SpongeCell::Zero);
            let out = self.keccak_out(&args[2]);
            let (m, tail) = self.keccak_rate(&cells, None);
            self.emit(LOp::Keccak {
                m,
                tail,
                b8: cap,
                cap: cap + 1,
                c: out.state,
                in_odd: false,
                out_odd: false,
            });
            self.keccak_finish(out);
            return;
        }
        let len = self.keccak_len(&kwargs, cells.len() as u32);
        let out = self.keccak_out(&args[2]);
        self.emit_keccak_message(cells, Some(len), None, out.state);
        self.keccak_finish(out);
    }

    /// `keccak_cells(cells, out, state=, len=, final=)`: the Keccak-256 of the message the
    /// cells hold, 136 bytes a `KECCAK` instruction, into `out` as for [`Self::lower_keccak`].
    /// `cells` is a run (a `StackBuf`, or a slice with compile-time bounds) or a list of words,
    /// and the message is their first `len` bytes (all of them by default; past `len`, as for
    /// [`Self::lower_keccak`]).
    ///
    /// `state=`, a previous 13-cell output, continues a hash whose message so far is a whole
    /// number of block pairs, 272 bytes or 17 cells each, so that the cells start a block at
    /// a cell boundary. `final=0` absorbs the cells zero-extended to whole blocks, with no
    /// padding: the start of a hash continued later, or a bare permutation.
    fn lower_keccak_cells(&mut self, args: &[Expr]) {
        let kwargs = self.keccak_kwargs(args, "keccak_cells", &["cells", "out"], &["state", "len", "final"]);
        let comprehension;
        let list = match &args[0] {
            Expr::ListComp(body, var, lo, hi) => {
                let bound = |e: &Expr| {
                    self.try_const_int(e).unwrap_or_else(|| {
                        self.fail(format!(
                            "a list comprehension's bounds must be compile-time integers, got `{e:?}`"
                        ))
                    })
                };
                comprehension = Expr::ListLit(
                    (bound(lo)..bound(hi))
                        .map(|i| crate::parser::subst_var(body, var, &Expr::Lit(i)))
                        .collect(),
                );
                &comprehension
            }
            e => e,
        };
        let cells = self.sponge_cells(list);
        if cells.is_empty() {
            self.fail("keccak_cells hashes at least one cell")
        }
        let is_final = match kwargs.get("final") {
            Some(e) => {
                self.try_const_int(e)
                    .unwrap_or_else(|| self.fail(format!("keccak `final` must be a compile-time integer, got `{e:?}`")))
                    != 0
            }
            None => true,
        };
        let final_len = if is_final {
            Some(self.keccak_len(&kwargs, cells.len() as u32))
        } else {
            if kwargs.contains_key("len") {
                self.fail("keccak_cells final=0 absorbs whole cells: it takes no len=")
            }
            None
        };
        let state = kwargs.get("state").map(|state| {
            self.prev_state(state, STATE_CELLS).unwrap_or_else(|| {
                self.fail(format!(
                    "keccak_cells state= must be the {STATE_CELLS}-cell run a previous keccak wrote"
                ))
            })
        });
        let out = self.keccak_out(&args[1]);
        self.emit_keccak_message(cells, final_len, state, out.state);
        self.keccak_finish(out);
    }

    /// The message length `len=` names, at most the `n` cells' bytes and all of them by default.
    fn keccak_len(&self, kwargs: &HashMap<&str, &Expr>, n: u32) -> u32 {
        let Some(e) = kwargs.get("len") else { return 16 * n };
        let len = self
            .try_const_int(e)
            .unwrap_or_else(|| self.fail(format!("keccak `len` must be a compile-time integer, got `{e:?}`")));
        if len > u128::from(16 * n) {
            self.fail(format!(
                "keccak len= {len} is past the {} bytes of its {n} cells",
                16 * n
            ))
        };
        len as u32
    }

    /// The keywords after builtin `f`'s `positional` arguments, checked against `allowed`.
    fn keccak_kwargs<'e>(
        &self,
        args: &'e [Expr],
        f: &str,
        positional: &[&str],
        allowed: &[&str],
    ) -> HashMap<&'e str, &'e Expr> {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        if first_kw != positional.len() {
            self.fail(format!(
                "{f} takes {} positional arguments: ({})",
                positional.len(),
                positional.join(", ")
            ))
        };
        let kws = &args[first_kw..];
        if !(kws
            .iter()
            .all(|a| matches!(a, Expr::Call(name, v) if name.starts_with("__kw_") && v.len() == 1)))
        {
            self.fail("keyword arguments must follow the positional keccak arguments")
        };
        let mut kwargs: HashMap<&str, &Expr> = HashMap::new();
        for kw in kws {
            let Expr::Call(name, value) = kw else { unreachable!() };
            let key = name.strip_prefix("__kw_").unwrap();
            if kwargs.insert(key, &value[0]).is_some() {
                self.fail(format!("duplicate keccak keyword `{key}`"))
            };
        }
        if !(kwargs.keys().all(|k| allowed.contains(k))) {
            // Sorted: a `HashMap`'s order would make the same mistake report
            // differently between builds.
            let mut bad: Vec<&&str> = kwargs.keys().filter(|k| !allowed.contains(k)).collect();
            bad.sort_unstable();
            self.fail(format!("unknown keccak keyword {bad:?}; the keywords are {allowed:?}"))
        };
        kwargs
    }

    /// Where a `keccak` writes: the 13-cell stack run the instruction targets, and
    /// what to copy out of it afterwards.
    fn keccak_out(&mut self, e: &Expr) -> KeccakOut {
        match self.cell_run(e) {
            CellRun::Stack { base, len } if len >= STATE_CELLS => KeccakOut {
                state: base,
                copy: None,
            },
            run @ (CellRun::Heap { len: STATE_CELLS, .. }
            | CellRun::Stack { len: 2, .. }
            | CellRun::Heap { len: 2, .. }) => KeccakOut {
                state: self.alloc_stack(STATE_CELLS),
                copy: Some(run),
            },
            _ => self.fail(format!(
                "a keccak destination is a {STATE_CELLS}-cell run (the state) or a 2-cell run (the digest)"
            )),
        }
    }

    /// Copy what [`Self::keccak_out`] promised out of the state it wrote.
    fn keccak_finish(&mut self, out: KeccakOut) {
        match out.copy {
            None => {}
            Some(CellRun::Stack { base, len }) => {
                for k in 0..len {
                    self.copy(out.state + k, base + k);
                }
            }
            Some(CellRun::Heap { ptr, lo, len }) => self.deref_run(ptr, lo, len, out.state),
        }
    }

    /// Emit the `KECCAK` blocks absorbing `cells` into `state` (the zero state if `None`), the
    /// last writing the 13-cell run `out`. With `final_len` the message is the cells' first
    /// `final_len` bytes, padded; without, the cells zero-extended to whole blocks.
    fn emit_keccak_message(
        &mut self,
        mut cells: Vec<SpongeCell>,
        final_len: Option<u32>,
        state: Option<Off>,
        out: Off,
    ) {
        let blocks = match final_len {
            Some(len) => len as usize / RATE + 1,
            None => (16 * cells.len()).div_ceil(RATE),
        };
        // Block `k` reads the nine cells from `17k / 2`.
        let read = 17 * (blocks - 1) / 2 + BLOCK_CELLS as usize;
        if cells.len() < read {
            cells.resize(read, SpongeCell::Zero);
        }
        if let Some(len) = final_len {
            // A cell wholly past the message would be absorbed (or, past the last block,
            // dropped) as if it were part of it.
            let past = (len as usize).div_ceil(16);
            if let Some(k) = (past..cells.len()).find(|&k| !matches!(cells[k], SpongeCell::Zero)) {
                self.fail(format!(
                    "keccak len= {len} ends before message cell {k}, which is not a literal 0"
                ))
            }
            self.xor_byte(&mut cells, len as usize, primitives::hash::PAD_FIRST);
            self.xor_byte(&mut cells, blocks * RATE - 1, primitives::hash::PAD_LAST);
        }
        // Block `k` is read in the layout of its parity, so each block's output is written in
        // the next one's, the last's in the even layout, where the digest is the first two cells.
        let mut state = state;
        for k in 0..blocks {
            let last = k + 1 == blocks;
            let c = if last { out } else { self.alloc_stack(STATE_CELLS) };
            let block = &cells[17 * k / 2..][..BLOCK_CELLS as usize];
            let (m, tail) = self.keccak_rate(block, state);
            let b8 = match state {
                None => self.sponge_cell(block[8]),
                Some(st) => self.sponge_xor(st + 8, block[8], None),
            };
            let cap = state.map_or_else(|| self.keccak_pad_run() + 1, |st| st + 9);
            self.emit(LOp::Keccak {
                m,
                tail,
                b8,
                cap,
                c,
                in_odd: k % 2 == 1,
                out_odd: !last && k % 2 == 0,
            });
            state = Some(c);
        }
    }

    /// XOR the byte `v` into byte `at` of the message cells.
    fn xor_byte(&mut self, cells: &mut [SpongeCell], at: usize, v: u8) {
        let (cell, byte) = (at / 16, at % 16);
        let w = u64::from(v) << (8 * (byte % 8));
        let v = if byte < 8 {
            F192::new(w, 0, 0)
        } else {
            F192::new(0, w, 0)
        };
        cells[cell] = match cells[cell] {
            SpongeCell::Zero => SpongeCell::Const(v),
            SpongeCell::Const(c) => SpongeCell::Const(c + v),
            SpongeCell::Cell(o) => {
                let (k, dst) = (self.const_cell(v), self.fresh());
                self.emit(LOp::Xor { a: o, b: k, c: dst });
                SpongeCell::Cell(dst)
            }
        };
    }

    /// The `m` and `tail` cells of a `KECCAK` reading the block's first eight cells: themselves
    /// from the zero state, or XORed into the cells of the previous output `st` they line up with.
    fn keccak_rate(&mut self, block: &[SpongeCell], st: Option<Off>) -> ([Off; 4], Off) {
        let Some(st) = st else {
            return (
                [0, 1, 2, 3].map(|i| self.sponge_cell(block[i])),
                self.sponge_run(&block[4..8]),
            );
        };
        let m = [0, 1, 2, 3].map(|i| self.sponge_xor(st + i, block[i as usize], None));
        if block[4..8].iter().all(|c| matches!(c, SpongeCell::Zero)) {
            return (m, st + 4);
        }
        let tail = self.alloc_stack(4);
        for j in 0..4 {
            self.sponge_xor(st + 4 + j, block[4 + j as usize], Some(tail + j));
        }
        (m, tail)
    }

    /// `state ⊕ c`, into `dst` if given: a zero `c` is the state cell itself (or a copy of it
    /// into `dst`).
    fn sponge_xor(&mut self, state: Off, c: SpongeCell, dst: Option<Off>) -> Off {
        let other = match c {
            SpongeCell::Zero => {
                return match dst {
                    Some(d) => {
                        self.copy(state, d);
                        d
                    }
                    None => state,
                };
            }
            c => self.sponge_cell(c),
        };
        let d = dst.unwrap_or_else(|| self.fresh());
        self.emit(LOp::Xor {
            a: state,
            b: other,
            c: d,
        });
        d
    }

    /// Four consecutive frame cells holding `cells`: where they already lie, a window of the
    /// padding run, or a fresh copy.
    fn sponge_run(&mut self, cells: &[SpongeCell]) -> Off {
        let at = |k: usize| match cells[k] {
            SpongeCell::Cell(o) => o.checked_sub(k as u32),
            _ => None,
        };
        if let Some(base) = at(0)
            && (1..cells.len()).all(|k| at(k) == Some(base))
        {
            return base;
        }
        let zero = |c: &SpongeCell| matches!(c, SpongeCell::Zero);
        if cells.iter().all(zero) {
            return self.keccak_pad_run() + 1;
        }
        if matches!(cells[0], SpongeCell::Const(v) if v == keccak_pad_value()) && cells[1..].iter().all(zero) {
            return self.keccak_pad_run();
        }
        let t = self.alloc_stack(cells.len() as u32);
        for (j, &c) in cells.iter().enumerate() {
            let dst = t + j as u32;
            match c {
                SpongeCell::Zero => self.set_const(dst, F192::ZERO),
                SpongeCell::Const(v) => self.set_const(dst, v),
                SpongeCell::Cell(o) => self.copy(o, dst),
            }
        }
        t
    }

    /// The statement-position builtins, `true` if `f` was one of them (else the
    /// caller emits an ordinary call). The `hint_*` ones queue prover-side
    /// advice, re-checked in-circuit by their caller: `hint_decompose_bits`
    /// writes a value's bits into a buffer, `hint_decompose_bits_exponent` the
    /// bits of `n` where the value is `g^n` (a bounded dlog at witness
    /// generation), `hint_f192_limbs` a value's coordinate limbs.
    pub(super) fn lower_builtin(&mut self, f: &str, args: &[Expr]) -> bool {
        match f {
            "hint_decompose_bits" | "hint_decompose_bits_exponent" => {
                let plain = f == "hint_decompose_bits";
                if args.len() != 3 && !(plain && args.len() == 4) {
                    self.fail(format!(
                        "{f} takes `(bits, value, nbits{})`, got {} arguments",
                        if plain { "[, start]" } else { "" },
                        args.len()
                    ))
                };
                let nbits = self.const_index(&args[2]);
                let bits = self.bits_dest(&args[0], nbits, f);
                let value = self.expr(&args[1]);
                self.pending.push(Hint::Resolved(if plain {
                    let start = args.get(3).map_or(0, |start| self.const_index(start));
                    let end = u64::from(start) + u64::from(nbits);
                    if end > 192 {
                        self.fail(format!("{f} reads bits {start}..{end} of a 192-bit word"))
                    };
                    RHint::BitDecompose {
                        value,
                        bits,
                        nbits,
                        start,
                    }
                } else {
                    RHint::BitDecomposeExp { value, bits, nbits }
                }));
            }
            "keccak" => self.lower_keccak(args),
            "keccak_cells" => self.lower_keccak_cells(args),
            "assert_in_k" => {
                if args.len() != 2 {
                    self.fail("assert_in_k(a, b) takes two scalar cells")
                };
                let a = self.expr(&args[0]);
                let b = self.expr(&args[1]);
                let zero = self.zero();
                self.emit(LOp::Jump { oc: zero, od: a, of: b });
            }
            "hint_f192_limbs" => {
                if args.len() != 2 {
                    self.fail(format!(
                        "hint_f192_limbs takes two arguments, `(dest, value)`, got {}",
                        args.len()
                    ))
                };
                let (base, len) = self.stack_of(&args[0]).unwrap_or_else(|| {
                    self.fail(format!(
                        "hint_f192_limbs writes 1..=3 frame cells, so its destination must be a \
                             StackBuf, got `{:?}`",
                        args[0]
                    ))
                });
                if !((1..=3).contains(&len)) {
                    self.fail("hint_f192_limbs destination must have 1..=3 cells")
                };
                let value = self.expr(&args[1]);
                // Names the physical cells, as the two consumers above do: whatever
                // the program stores into them afterwards is a second write, and so
                // the assertion that pins these limbs.
                self.pending
                    .push(Hint::Resolved(RHint::FieldLimbs { value, base, len }));
            }
            _ => return false,
        }
        true
    }

    /// The message cells `e` names: a list literal's words (a literal `0` known to be zero,
    /// which lets a constant window of the padding run stand in for it), or a run of cells, a
    /// heap run bridged through the stack since `KECCAK` addresses only frame cells.
    fn sponge_cells(&mut self, e: &Expr) -> Vec<SpongeCell> {
        if let Expr::ListLit(words) = e {
            return words
                .iter()
                .map(|w| match self.try_const_int(w) {
                    Some(0) => SpongeCell::Zero,
                    _ => SpongeCell::Cell(self.expr(w)),
                })
                .collect();
        }
        let (base, len) = match self.cell_run(e) {
            CellRun::Stack { base, len } => (base, len),
            CellRun::Heap { ptr, lo, len } => (self.heap_to_stack(ptr, lo, len), len),
        };
        (0..len).map(|k| SpongeCell::Cell(base + k)).collect()
    }

    /// A `keccak` operand: [`Self::sponge_cells`] of exactly `n` cells.
    fn keccak_operand(&mut self, e: &Expr, n: usize) -> Vec<SpongeCell> {
        let cells = self.sponge_cells(e);
        if cells.len() != n {
            match e {
                Expr::ListLit(_) => self.fail(format!(
                    "a keccak operand written as a list needs exactly {n} words, got {}",
                    cells.len()
                )),
                _ => self.fail(format!(
                    "this keccak operand spans exactly {n} cells; slice a larger buffer: `buf[lo:lo + {n}]`"
                )),
            }
        }
        cells
    }

    /// The frame cells holding the last `n` cells of a previous 13-cell output `e`, or `e` as
    /// those `n` cells alone: a stack run in place, a heap run bridged through the stack.
    fn prev_state(&mut self, e: &Expr, n: u32) -> Option<Off> {
        match self.try_cell_run(e).ok()? {
            CellRun::Stack { base, len } if len >= STATE_CELLS => Some(base + STATE_CELLS - n),
            CellRun::Stack { base, len } if len == n => Some(base),
            CellRun::Heap { ptr, lo, len } if len == STATE_CELLS || len == n => {
                Some(self.heap_to_stack(ptr, lo + len - n, n))
            }
            _ => None,
        }
    }

    /// [`Self::cell_run`], or the reason it is not one, without failing.
    fn try_cell_run(&mut self, e: &Expr) -> Result<CellRun, ()> {
        match e {
            Expr::Var(_) | Expr::Slice(..) => Ok(self.cell_run(e)),
            _ => Err(()),
        }
    }

    /// A frame cell holding `c`.
    fn sponge_cell(&mut self, c: SpongeCell) -> Off {
        match c {
            SpongeCell::Zero => self.keccak_pad_run() + 1,
            SpongeCell::Const(v) if v == keccak_pad_value() => self.keccak_pad_run(),
            SpongeCell::Const(v) => self.const_cell(v),
            SpongeCell::Cell(o) => o,
        }
    }

    /// The five cells `[pad, 0, 0, 0, 0]` every `keccak` in this scope shares
    /// ([`Scope::keccak_pad`]): the zero `tail` and `cap` start at `+1`, a 64-byte message's
    /// `tail` at `+0`. Set, never left unwritten: an unwritten cell is the prover's.
    fn keccak_pad_run(&mut self) -> Off {
        if let Some(o) = self.scope.keccak_pad {
            return o;
        }
        let o = self.alloc_stack(5);
        for k in 0..5 {
            let value = if k == 0 { keccak_pad_value() } else { F192::ZERO };
            self.set_const(o + k, value);
            self.scope
                .const_cells
                .entry([value.c0, value.c1, value.c2])
                .or_insert(o + k);
        }
        self.scope.keccak_pad = Some(o);
        o
    }

    /// A computed-advice bit buffer's destination ([`BitsDest`]). Not
    /// [`Self::cell_run`]: these builtins take a bare `HeapBuf` and carry the
    /// length in `nbits`, where a cell run would demand a slice.
    pub(super) fn bits_dest(&mut self, e: &Expr, nbits: u32, what: &str) -> BitsDest {
        match self.stack_of(e) {
            Some((base, len)) => {
                if len < nbits {
                    self.fail(format!(
                        "{what} needs {nbits} cells, its StackBuf destination has {len}"
                    ))
                };
                // The hint names the physical cells, as `hint_f192_limbs` does.
                BitsDest::Stack(base)
            }
            None => {
                // Bounds-checked like the `StackBuf` arm above, and like every
                // other heap consumer. Without this a `HeapBuf` destination wrote
                // `nbits` cells with nothing checking the buffer held them, so the
                // bits ran on into the next buffer while the same call with a
                // `StackBuf` destination was rejected.
                self.check_heap_bound(e, 0, u128::from(nbits));
                BitsDest::Heap(self.expr(e))
            }
        }
    }

    /// `hint_witness(dest, "name")`: resolve `dest` to a run of cells and
    /// queue the witness-fill hint (no instructions: the values are written
    /// by the runner before the next instruction executes, unconstrained).
    pub(super) fn lower_hint_witness(&mut self, dest: &Expr, name: &str) {
        let name = name.to_string();
        let hint = match self.cell_run(dest) {
            CellRun::Stack { base, len } => RHint::WitnessStack { name, base, len },
            CellRun::Heap { ptr, lo, len } => RHint::WitnessHeap { name, ptr, lo, len },
        };
        self.pending.push(Hint::Resolved(hint));
    }
}

/// Cells a sponge state occupies.
const STATE_CELLS: u32 = leanvm_core::keccak::STATE_CELLS as u32;
/// The rate cells of a state, the nine a block covers.
const BLOCK_CELLS: u32 = leanvm_core::keccak::RATE_CELLS as u32;
/// Bytes a block absorbs.
const RATE: usize = primitives::hash::RATE;

/// A cell holding the padding's first byte at its start: `0x01` in the low lane.
fn keccak_pad_value() -> F192 {
    F192::new(u64::from(primitives::hash::PAD_FIRST), 0, 0)
}

/// Where a `keccak` writes: the 13-cell stack run its instruction targets, and a
/// run to copy the state or the digest out to afterwards.
struct KeccakOut {
    state: Off,
    copy: Option<CellRun>,
}

/// One message cell of a `keccak` block, as the lowering knows it.
#[derive(Clone, Copy, Debug)]
enum SpongeCell {
    Zero,
    Const(F192),
    Cell(Off),
}
