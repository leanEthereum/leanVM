//! The precompile and the hints: the two places a value arrives without an
//! instruction computing it.
//!
//! `sha3` is a STATEMENT, not an expression: it writes the sponge state into a
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
    /// `sha3(a, b, out, tail=, state=, len=, final=)`: one block of
    /// [`primitives::hash::hash`], one `SHA3` instruction.
    ///
    /// The block's eight message cells are `a ‖ b ‖ tail` (two, two and four
    /// cells; `tail` omitted is zero). Without `state` this is the first block of
    /// a hash, from the zero state; with it, `state` is the previous block's
    /// 13-cell output and the message is XORed into it. `len=` makes this the
    /// final block of a message ending `len` bytes into it, and places the
    /// padding's first byte there (bytes past it must be zero); `final=0` makes it
    /// a non-final block of 128 message bytes; with neither, the block is final and
    /// its message fills the operands given, 64 bytes without `tail` and 128 with.
    ///
    /// The output is the 13-cell state, its first two cells the digest. A 13-cell
    /// `out` receives it (a heap run through the stack), a 2-cell `out` just the
    /// digest (write-once: a pre-written `out` asserts it). `state` may likewise
    /// be a heap run, bridged into the stack.
    ///
    /// `cap=` is a duplex step in overwrite mode instead: the eight message cells
    /// ARE the rate, and the capacity is `cap`'s, the five cells a previous output
    /// ends with (`cap` that 13-cell output or those five cells). No padding, no
    /// XOR: the instruction reads the message cells and `cap` as they are.
    fn lower_sha3(&mut self, args: &[Expr]) {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        if first_kw != 3 {
            self.fail("sha3 takes three positional arguments: (a, b, out)")
        };
        let kwargs = self.sha3_kwargs(&args[first_kw..], &["tail", "state", "len", "final", "cap"]);
        let const_kw = |this: &Self, name: &str| -> Option<u128> {
            kwargs.get(name).map(|e| {
                this.try_const_int(e)
                    .unwrap_or_else(|| this.fail(format!("sha3 `{name}` must be a compile-time integer, got `{e:?}`")))
            })
        };
        if let Some(cap) = kwargs.get("cap") {
            if ["state", "len", "final"].iter().any(|k| kwargs.contains_key(k)) {
                self.fail("sha3 cap= is an overwrite duplex step: it takes no state=, len= or final=")
            }
            let cap = match self.try_cell_run(cap) {
                Ok(CellRun::Stack { base, len }) if len == STATE_CELLS => base + 8,
                Ok(CellRun::Stack { base, len: 5 }) => base,
                Ok(CellRun::Heap { ptr, lo, len }) if len == STATE_CELLS || len == 5 => {
                    let from = lo + len - 5;
                    let run = self.alloc_stack(5);
                    for k in 0..5 {
                        self.deref(ptr, from + k, run + k, DerefMode::Cell);
                    }
                    run
                }
                _ => self.fail(format!(
                    "sha3 cap= must be a previous {STATE_CELLS}-cell output or its last five cells"
                )),
            };
            let [a0, a1] = self.sha3_words::<2>(&args[0]);
            let [b0, b1] = self.sha3_words::<2>(&args[1]);
            let m = [a0, a1, b0, b1].map(|c| self.sponge_cell(c));
            let tail = match kwargs.get("tail") {
                Some(tail) => match self.try_cell_run(tail) {
                    Ok(CellRun::Stack { base, len: 4 }) => base,
                    _ => {
                        let cells = self.sha3_words::<4>(tail);
                        let t = self.alloc_stack(4);
                        for (j, c) in cells.into_iter().enumerate() {
                            let dst = t + j as u32;
                            match c {
                                SpongeCell::Zero => self.set_const(dst, F192::ZERO),
                                SpongeCell::Const(v) => self.set_const(dst, v),
                                SpongeCell::Cell(o) => self.copy(o, dst),
                            }
                        }
                        t
                    }
                },
                None => self.sha3_pad_run() + 1,
            };
            let out = self.sha3_out(&args[2]);
            self.emit(LOp::Sha3 {
                m,
                tail,
                cap,
                c: out.state,
            });
            self.sha3_finish(out);
            return;
        }
        let is_final = const_kw(self, "final").unwrap_or(1) != 0;
        let len = const_kw(self, "len");
        // The message bytes this block carries, if it is the final one.
        let final_len = if is_final {
            let len = len.unwrap_or(if kwargs.contains_key("tail") { 128 } else { 64 });
            if len > 128 {
                self.fail(format!("sha3 len= {len} is past the block's 128 message bytes"))
            };
            // A message ending on a whole block ends in that block, never in an empty one.
            if len == 0 && kwargs.contains_key("state") {
                self.fail("sha3 len=0 after a previous block hashes no message: end that block with len=128")
            };
            Some(len as u32)
        } else {
            if len.is_some_and(|l| l != 128) {
                self.fail("a sha3 block with final=0 carries 128 message bytes, so len= can only be 128")
            };
            None
        };

        let mut block = [SpongeCell::Zero; 8];
        let [a0, a1] = self.sha3_words::<2>(&args[0]);
        let [b0, b1] = self.sha3_words::<2>(&args[1]);
        block[..4].copy_from_slice(&[a0, a1, b0, b1]);
        let mut tail_run = None;
        if let Some(tail) = kwargs.get("tail") {
            if let Ok(CellRun::Stack { base, len: 4 }) = self.try_cell_run(tail) {
                tail_run = Some(base);
            }
            block[4..].copy_from_slice(&self.sha3_words::<4>(tail));
        }
        let state = kwargs.get("state").map(|state| match self.try_cell_run(state) {
            Ok(CellRun::Stack { base, len }) if len >= STATE_CELLS => base,
            Ok(CellRun::Heap { ptr, lo, len }) if len == STATE_CELLS => {
                let st = self.alloc_stack(STATE_CELLS);
                for k in 0..STATE_CELLS {
                    self.deref(ptr, lo + k, st + k, DerefMode::Cell);
                }
                st
            }
            _ => self.fail(format!(
                "sha3 state= must be the {STATE_CELLS}-cell run a previous sha3 wrote"
            )),
        });
        let out = self.sha3_out(&args[2]);
        self.emit_sha3_block(block, tail_run, state, final_len, out.state);
        self.sha3_finish(out);
    }

    /// `sha3_cells(run, out)`: the hash of the whole run of cells `run` (a
    /// `StackBuf`, or a slice with compile-time bounds), eight cells a `SHA3`
    /// block, into `out` as for [`Self::lower_sha3`].
    fn lower_sha3_cells(&mut self, args: &[Expr]) {
        if args.len() != 2 {
            self.fail("sha3_cells takes two arguments: (run, out)")
        };
        let run = self.cell_run(&args[0]);
        let n = run.cells();
        let out = self.sha3_out(&args[1]);
        // The chunk's cells, and its base if they are a consecutive stack run.
        let chunk = |this: &mut Self, lo: u32, len: u32| -> (Vec<SpongeCell>, Option<Off>) {
            match run {
                CellRun::Stack { base, .. } => (
                    (0..len).map(|k| SpongeCell::Cell(base + lo + k)).collect(),
                    Some(base + lo),
                ),
                CellRun::Heap { ptr, lo: hlo, .. } => {
                    let t = this.alloc_stack(len);
                    for k in 0..len {
                        this.deref(ptr, hlo + lo + k, t + k, DerefMode::Cell);
                    }
                    ((0..len).map(|k| SpongeCell::Cell(t + k)).collect(), Some(t))
                }
            }
        };
        let nonfinal = n.saturating_sub(1) / 8;
        let mut state = None;
        for c in 0..nonfinal {
            let (cells, base) = chunk(self, 8 * c, 8);
            let next = self.alloc_stack(STATE_CELLS);
            let block: [SpongeCell; 8] = cells.try_into().unwrap();
            self.emit_sha3_block(block, base.map(|b| b + 4), state, None, next);
            state = Some(next);
        }
        let last = n - 8 * nonfinal;
        let (cells, base) = chunk(self, 8 * nonfinal, last);
        let mut block = [SpongeCell::Zero; 8];
        block[..last as usize].copy_from_slice(&cells);
        let tail_run = if last == 8 { base.map(|b| b + 4) } else { None };
        self.emit_sha3_block(block, tail_run, state, Some(16 * last), out.state);
        self.sha3_finish(out);
    }

    /// The keywords after a builtin's positional arguments, checked against
    /// `allowed`.
    fn sha3_kwargs<'e>(&self, kws: &'e [Expr], allowed: &[&str]) -> HashMap<&'e str, &'e Expr> {
        if !(kws
            .iter()
            .all(|a| matches!(a, Expr::Call(name, v) if name.starts_with("__kw_") && v.len() == 1)))
        {
            self.fail("keyword arguments must follow the positional sha3 arguments")
        };
        let mut kwargs: HashMap<&str, &Expr> = HashMap::new();
        for kw in kws {
            let Expr::Call(name, value) = kw else { unreachable!() };
            let key = name.strip_prefix("__kw_").unwrap();
            if kwargs.insert(key, &value[0]).is_some() {
                self.fail(format!("duplicate sha3 keyword `{key}`"))
            };
        }
        if !(kwargs.keys().all(|k| allowed.contains(k))) {
            // Sorted: a `HashMap`'s order would make the same mistake report
            // differently between builds.
            let mut bad: Vec<&&str> = kwargs.keys().filter(|k| !allowed.contains(k)).collect();
            bad.sort_unstable();
            self.fail(format!("unknown sha3 keyword {bad:?}; the keywords are {allowed:?}"))
        };
        kwargs
    }

    /// Where a `sha3` writes: the 13-cell stack run the instruction targets, and
    /// what to copy out of it afterwards.
    fn sha3_out(&mut self, e: &Expr) -> Sha3Out {
        match self.cell_run(e) {
            CellRun::Stack { base, len } if len >= STATE_CELLS => Sha3Out {
                state: base,
                copy: None,
            },
            run @ (CellRun::Heap { len: STATE_CELLS, .. }
            | CellRun::Stack { len: 2, .. }
            | CellRun::Heap { len: 2, .. }) => Sha3Out {
                state: self.alloc_stack(STATE_CELLS),
                copy: Some(run),
            },
            _ => self.fail(format!(
                "a sha3 destination is a {STATE_CELLS}-cell run (the state) or a 2-cell run (the digest)"
            )),
        }
    }

    /// Copy what [`Self::sha3_out`] promised out of the state it wrote.
    fn sha3_finish(&mut self, out: Sha3Out) {
        match out.copy {
            None => {}
            Some(CellRun::Stack { base, len }) => {
                for k in 0..len {
                    self.copy(out.state + k, base + k);
                }
            }
            Some(CellRun::Heap { ptr, lo, len }) => {
                for k in 0..len {
                    self.deref(ptr, lo + k, out.state + k, DerefMode::Cell);
                }
            }
        }
    }

    /// Emit one `SHA3` block into the 13-cell run `c`: the padding folded into
    /// the message if `final_len` says this block ends it, the message XORed into
    /// `state` if there is one, every constant window of a fresh block taken from
    /// the padding run.
    fn emit_sha3_block(
        &mut self,
        mut block: [SpongeCell; 8],
        mut tail_run: Option<Off>,
        state: Option<Off>,
        final_len: Option<u32>,
        c: Off,
    ) {
        // Padding in lane 16, the lone cell: only a final block of 128 bytes.
        let mut lone_pad = false;
        if let Some(len) = final_len {
            if len == 128 {
                lone_pad = true;
            } else {
                let (cell, byte) = ((len / 16) as usize, len % 16);
                let pad = u64::from(primitives::hash::PAD_FIRST) << (8 * (byte % 8));
                let v = if byte < 8 {
                    F192::new(pad, 0, 0)
                } else {
                    F192::new(0, pad, 0)
                };
                block[cell] = match block[cell] {
                    SpongeCell::Zero => SpongeCell::Const(v),
                    SpongeCell::Const(w) => SpongeCell::Const(w + v),
                    SpongeCell::Cell(o) => {
                        let (k, dst) = (self.const_cell(v), self.fresh());
                        self.emit(LOp::Xor { a: o, b: k, c: dst });
                        SpongeCell::Cell(dst)
                    }
                };
                if cell >= 4 {
                    tail_run = None;
                }
            }
        }

        let (m, tail, cap) = match state {
            // A later block: XOR the message into the previous state's rate cells.
            // A zero message cell passes the state's cell through, so a tail with
            // no message keeps the previous run, and the capacity always does
            // unless the padding lands in lane 16.
            Some(st) => {
                let m: [Off; 4] = std::array::from_fn(|i| self.sponge_xor(st + i as u32, block[i], None));
                let tail = if block[4..].iter().all(|c| matches!(c, SpongeCell::Zero)) {
                    st + 4
                } else {
                    let t = self.alloc_stack(4);
                    for j in 0..4 {
                        self.sponge_xor(st + 4 + j as u32, block[4 + j], Some(t + j as u32));
                    }
                    t
                };
                let cap = if lone_pad {
                    let cap = self.alloc_stack(5);
                    let pad = self.sha3_pad_run();
                    self.emit(LOp::Xor {
                        a: st + 8,
                        b: pad,
                        c: cap,
                    });
                    for k in 1..5 {
                        self.copy(st + 8 + k, cap + k);
                    }
                    cap
                } else {
                    st + 8
                };
                (m, tail, cap)
            }
            // The first block, from the zero state: every constant window comes out
            // of the one padding run.
            None => {
                let pad = self.sha3_pad_run();
                let m: [Off; 4] = std::array::from_fn(|i| self.sponge_cell(block[i]));
                let tail = match (tail_run, &block[4..]) {
                    (Some(base), _) => base,
                    (None, [SpongeCell::Zero, SpongeCell::Zero, SpongeCell::Zero, SpongeCell::Zero]) => pad + 1,
                    (
                        None,
                        [
                            SpongeCell::Const(v),
                            SpongeCell::Zero,
                            SpongeCell::Zero,
                            SpongeCell::Zero,
                        ],
                    ) if *v == sha3_pad_value() => pad,
                    (None, cells) => {
                        let cells: Vec<SpongeCell> = cells.to_vec();
                        let t = self.alloc_stack(4);
                        for (j, c) in cells.into_iter().enumerate() {
                            let dst = t + j as u32;
                            match c {
                                SpongeCell::Zero => self.set_const(dst, F192::ZERO),
                                SpongeCell::Const(v) => self.set_const(dst, v),
                                SpongeCell::Cell(o) => self.copy(o, dst),
                            }
                        }
                        t
                    }
                };
                (m, tail, if lone_pad { pad } else { pad + 1 })
            }
        };
        self.emit(LOp::Sha3 { m, tail, cap, c });
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
            "sha3" => self.lower_sha3(args),
            "sha3_cells" => self.lower_sha3_cells(args),
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

    /// `N` message cells of a `sha3` block: a list literal of `N` words (a literal
    /// `0` known to be zero, which lets a constant window of the padding run stand
    /// in for it), or a run of `N` cells, a heap slice bridged through the stack
    /// one `DEREF` per cell since `SHA3` addresses only frame cells.
    fn sha3_words<const N: usize>(&mut self, e: &Expr) -> [SpongeCell; N] {
        if let Expr::ListLit(words) = e {
            if words.len() != N {
                self.fail(format!(
                    "a sha3 operand written as a list needs exactly {N} words, got {}",
                    words.len()
                ))
            };
            return std::array::from_fn(|k| match self.try_const_int(&words[k]) {
                Some(0) => SpongeCell::Zero,
                _ => SpongeCell::Cell(self.expr(&words[k])),
            });
        }
        match self.cell_run(e) {
            CellRun::Stack { base, len } if len == N as u32 => {
                std::array::from_fn(|k| SpongeCell::Cell(base + k as u32))
            }
            CellRun::Heap { ptr, lo, len } if len == N as u32 => {
                let t = self.alloc_stack(N as u32);
                for k in 0..N as u32 {
                    self.deref(ptr, lo + k, t + k, DerefMode::Cell);
                }
                std::array::from_fn(|k| SpongeCell::Cell(t + k as u32))
            }
            _ => self.fail(format!(
                "this sha3 operand spans exactly {N} cells; slice a larger buffer: `buf[lo:lo + {N}]`"
            )),
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
            SpongeCell::Zero => self.sha3_pad_run() + 1,
            SpongeCell::Const(v) if v == sha3_pad_value() => self.sha3_pad_run(),
            SpongeCell::Const(v) => self.const_cell(v),
            SpongeCell::Cell(o) => o,
        }
    }

    /// `state ⊕ c`, into `dst` if given: a zero `c` is the state cell itself (or
    /// a copy of it into `dst`).
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

    /// The six cells `[pad, 0, 0, 0, 0, 0]` every fresh `sha3` in this scope
    /// shares ([`Scope::sha3_pad`]): the zero `tail` and `cap` start at `+1`, a
    /// 64-byte message's `tail` and a 128-byte one's `cap` at `+0`.
    fn sha3_pad_run(&mut self) -> Off {
        if let Some(o) = self.scope.sha3_pad {
            return o;
        }
        let o = self.alloc_stack(6);
        for k in 0..6 {
            let value = if k == 0 { sha3_pad_value() } else { F192::ZERO };
            self.set_const(o + k, value);
            self.scope
                .const_cells
                .entry([value.c0, value.c1, value.c2])
                .or_insert(o + k);
        }
        self.scope.sha3_pad = Some(o);
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

/// A cell holding the padding's first byte at its start: `0x01` in the low lane.
fn sha3_pad_value() -> F192 {
    F192::new(u64::from(primitives::hash::PAD_FIRST), 0, 0)
}

/// Where a `sha3` writes: the 13-cell stack run its instruction targets, and a
/// run to copy the state or the digest out to afterwards.
struct Sha3Out {
    state: Off,
    copy: Option<CellRun>,
}

/// One message cell of a `sha3` block, as the lowering knows it.
#[derive(Clone, Copy, Debug)]
enum SpongeCell {
    Zero,
    Const(F192),
    Cell(Off),
}
