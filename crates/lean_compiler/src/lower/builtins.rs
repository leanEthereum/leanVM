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
    /// `blake2s(a, b, out)`: the digest of the two 256-bit operands lands in the
    /// existing 2-cell run `out` (write-once: if `out` was already written, this
    /// asserts the digest equals it). A heap `out` slice takes the digest via a
    /// fresh stack pair and two `DEREF`s after the hash, the store direction
    /// being the same instruction as the load (write-once fills the unset side).
    /// Keyword arguments set the metadata: `counter=` / `final=` / `last_node=`
    /// build it at compile time, `md=` takes the whole word from a value the
    /// program computed.
    fn lower_blake2s(&mut self, args: &[Expr]) {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        if first_kw != 3 {
            self.fail("blake2s takes three positional arguments: (a, b, out)")
        };
        if !(args[first_kw..]
            .iter()
            .all(|a| matches!(a, Expr::Call(name, v) if name.starts_with("__kw_") && v.len() == 1)))
        {
            self.fail("keyword arguments must follow the three positional blake2s arguments")
        };
        let mut kwargs: HashMap<&str, &Expr> = HashMap::new();
        for kw in &args[first_kw..] {
            let Expr::Call(name, value) = kw else { unreachable!() };
            let key = name.strip_prefix("__kw_").unwrap();
            if kwargs.insert(key, &value[0]).is_some() {
                self.fail(format!("duplicate blake2s keyword `{key}`"))
            };
        }
        let allowed = ["cv", "counter", "final", "last_node", "md"];
        if !(kwargs.keys().all(|k| allowed.contains(k))) {
            // Sorted: a `HashMap`'s order would make the same mistake report
            // differently between builds.
            let mut bad: Vec<&&str> = kwargs.keys().filter(|k| !allowed.contains(k)).collect();
            bad.sort_unstable();
            self.fail(format!("unknown blake2s keyword {bad:?}; the keywords are {allowed:?}"))
        };
        let customized = kwargs.keys().any(|k| matches!(*k, "counter" | "final" | "last_node"));
        // `md=` hands over the whole metadata word as a runtime value, so it
        // replaces the three keywords that would otherwise build it.
        let runtime_md = kwargs.get("md").copied();
        if runtime_md.is_some() && customized {
            self.fail("blake2s md= is the whole metadata word, so counter=, final= and last_node= cannot come with it")
        };
        if kwargs.contains_key("cv") && !customized && runtime_md.is_none() {
            self.fail(
                "blake2s with cv= requires one of counter=, final=, last_node= or md=, since a chained \
                 block is not the default one-block hash",
            )
        };

        let a = self.blake2s_input(&args[0]);
        let b = self.blake2s_input(&args[1]);
        let (c, heap_out) = match self.blake2s_operand(&args[2]) {
            CellRun::Stack { base, .. } => (base, None),
            CellRun::Heap { ptr, lo, .. } => (self.alloc_stack(2), Some((ptr, lo))),
        };
        let cv = if let Some(value) = kwargs.get("cv") {
            self.blake2s_cv(value)
        } else {
            self.default_blake2s_cv()
        };
        let md = match runtime_md {
            // A metadata word the program computes, which is what lets a hash whose
            // block count is only known at run time carry the byte counter the
            // standard asks for (doc §sec:prog-byte-counter). It owes the same
            // canonical embedding as every other operand: the memory interaction
            // carries a literal zero above its two low limbs.
            //
            // Aliasing the digest destination is the one case write-once does not
            // catch: the runner reads the metadata before storing the digest, while
            // the witness reads the finished memory image, so the two disagree and
            // the proof fails its opening rather than saying why.
            Some(expr) => {
                let md = self.expr(expr);
                if md == c || md == c + 1 {
                    self.fail("blake2s md= must not name a cell of the digest destination")
                };
                md
            }
            None => {
                let const_kw = |this: &Self, name: &str, default: u128| -> u128 {
                    kwargs
                        .get(name)
                        .map(|e| {
                            this.try_const_int(e).unwrap_or_else(|| {
                                self.fail(format!(
                                    "BLAKE2s `{name}` must be a compile-time integer, got `{e:?}`; \
                                     a metadata word computed at run time goes through md="
                                ))
                            })
                        })
                        .unwrap_or(default)
                };
                // BLAKE2s metadata is just the cumulative byte counter and two flags, so
                // a multi-block hash is `counter = 64 * blocks_before + bytes_in_this_block`
                // and `final = 1` on the last block. The default is the one-block hash of
                // a full 64-byte input, which is what `vmhash::compress` and every Merkle
                // node use.
                let counter = const_kw(self, "counter", 64);
                let counter = u64::try_from(counter)
                    .unwrap_or_else(|_| self.fail(format!("blake2s counter= {counter} does not fit in u64")));
                let f0 = if const_kw(self, "final", if customized { 0 } else { 1 }) != 0 {
                    lean_vm::hash_flock::FINAL_FLAG
                } else {
                    0
                };
                let f1 = if const_kw(self, "last_node", 0) != 0 {
                    u32::MAX
                } else {
                    0
                };
                // A compile-time metadata is a pooled `SET`: one per distinct value
                // per frame, however many compressions read it.
                self.const_cell(lean_vm::hash_flock::metadata(counter, f0, f1))
            }
        };
        // Each operand is two 128-bit chunk cells; the flexible opcode addresses
        // the four input cells independently (`blake2s_input` forwards the real
        // chunk sources where it can). The digest occupies the two consecutive
        // output cells `c, g·c`.
        self.emit(LOp::Blake2s {
            ins: [a[0], a[1], b[0], b[1]],
            cv,
            c,
            md,
        });
        if let Some((ptr, lo)) = heap_out {
            for k in 0..2 {
                self.deref(ptr, lo + k, c + k, DerefMode::Cell);
            }
        }
    }

    /// `sha3(a, b, out, tail=, state=, len=, final=)`: one block of
    /// [`primitives::keccak::hash`], one `SHA3` instruction.
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
    /// `out` receives it (a heap run through the stack); a 2-cell `out` makes this
    /// a digest step, which writes the digest alone (write-once: a pre-written
    /// `out` asserts it). `state` may likewise be a heap run, bridged into the
    /// stack.
    fn lower_sha3(&mut self, args: &[Expr]) {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        if first_kw != 3 {
            self.fail("sha3 takes three positional arguments: (a, b, out)")
        };
        let kwargs = self.sha3_kwargs(&args[first_kw..], &["tail", "state", "len", "final"]);
        let const_kw = |this: &Self, name: &str| -> Option<u128> {
            kwargs.get(name).map(|e| {
                this.try_const_int(e)
                    .unwrap_or_else(|| this.fail(format!("sha3 `{name}` must be a compile-time integer, got `{e:?}`")))
            })
        };
        let is_final = const_kw(self, "final").unwrap_or(1) != 0;
        let len = const_kw(self, "len");
        // The message bytes this block carries, if it is the final one.
        let final_len = if is_final {
            let len = len.unwrap_or(if kwargs.contains_key("tail") { 128 } else { 64 });
            if len > 128 {
                self.fail(format!("sha3 len= {len} is past the block's 128 message bytes"))
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
        if let Some(tail) = kwargs.get("tail") {
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
        self.emit_sha3_block(block, state, final_len, &out, Pad::Sha3);
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
        // The chunk's cells, a heap run bridged through the stack.
        let chunk = |this: &mut Self, lo: u32, len: u32| -> Vec<SpongeCell> {
            match run {
                CellRun::Stack { base, .. } => (0..len).map(|k| SpongeCell::Cell(base + lo + k)).collect(),
                CellRun::Heap { ptr, lo: hlo, .. } => {
                    let t = this.alloc_stack(len);
                    for k in 0..len {
                        this.deref(ptr, hlo + lo + k, t + k, DerefMode::Cell);
                    }
                    (0..len).map(|k| SpongeCell::Cell(t + k)).collect()
                }
            }
        };
        let nonfinal = n.saturating_sub(1) / 8;
        let mut state = None;
        for c in 0..nonfinal {
            let block: [SpongeCell; 8] = chunk(self, 8 * c, 8).try_into().unwrap();
            let next = Sha3Out {
                base: self.alloc_stack(STATE_CELLS),
                digest: false,
                heap: None,
            };
            self.emit_sha3_block(block, state, None, &next, Pad::Sha3);
            state = Some(next.base);
        }
        let last = n - 8 * nonfinal;
        let cells = chunk(self, 8 * nonfinal, last);
        let mut block = [SpongeCell::Zero; 8];
        block[..last as usize].copy_from_slice(&cells);
        self.emit_sha3_block(block, state, Some(16 * last), &out, Pad::Sha3);
        self.sha3_finish(out);
    }

    /// `keccak(head, out, words=run)`: Keccak-256, the EVM's `keccak256`, of the
    /// byte string `head ‖ words`, into `out` as for [`Self::lower_sha3`].
    ///
    /// `head` is a list of at least one cell, a literal `0` known to be zero and
    /// any other compile-time integer a constant; `words=` (optional) is a run whose every
    /// cell enters as a 32-byte word, the cell then 16 zero bytes (an `n`-byte
    /// value top-aligned in a `bytes32`). The message is a whole number of cells.
    ///
    /// Up to 128 bytes this is one block, lowered as a `sha3` block with
    /// Keccak's padding byte. Past that the 136-byte rate splits cells: block `j`
    /// starts at byte `136 j`, mid-cell when `j` is odd, and lane 16 is message
    /// data in every block but the last. A split cell is taken apart into its two
    /// 64-bit lanes (a hinted low lane, the high lane `(x + lo)/y`, both proved in
    /// `K`) and the lanes repacked, and a non-final block cancels the last
    /// padding bit the opcode always sets in lane 16. Cells known to be zero cost
    /// nothing.
    fn lower_keccak(&mut self, args: &[Expr]) {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        if first_kw != 2 {
            self.fail("keccak takes two positional arguments: (head, out)")
        };
        let kwargs = self.sha3_kwargs(&args[first_kw..], &["words"]);
        let Expr::ListLit(head) = &args[0] else {
            self.fail("keccak's head is a list of at least one cell, `[a, 0, b, ...]`")
        };
        let mut msg: Vec<SpongeCell> = head
            .iter()
            .map(|w| match self.try_const_int(w) {
                Some(0) => SpongeCell::Zero,
                Some(v) => SpongeCell::Const(F192::new(v as u64, (v >> 64) as u64, 0)),
                None => SpongeCell::Cell(self.expr(w)),
            })
            .collect();
        if let Some(words) = kwargs.get("words") {
            let run = self.cell_run(words);
            for k in 0..run.cells() {
                let cell = match run {
                    CellRun::Stack { base, .. } => base + k,
                    CellRun::Heap { ptr, lo, .. } => {
                        let t = self.fresh();
                        self.deref(ptr, lo + k, t, DerefMode::Cell);
                        t
                    }
                };
                msg.extend([SpongeCell::Cell(cell), SpongeCell::Zero]);
            }
        }
        let out = self.sha3_out(&args[1]);
        let len = 16 * msg.len() as u32;
        if len <= 128 {
            let mut block = [SpongeCell::Zero; 8];
            block[..msg.len()].copy_from_slice(&msg);
            self.emit_sha3_block(block, None, Some(len), &out, Pad::Keccak);
        } else {
            self.emit_keccak_blocks(&msg, &out);
        }
        self.sha3_finish(out);
    }

    /// Keccak-256 of `msg` (more than one block) into `out`.
    fn emit_keccak_blocks(&mut self, msg: &[SpongeCell], out: &Sha3Out) {
        const RATE: u32 = primitives::keccak::RATE as u32;
        let len = 16 * msg.len() as u32;
        let n_blocks = len / RATE + 1;
        let y = F192::Y;
        let y_inv = y.inv();
        // A split cell's (low, high) lanes, each a K element in a frame cell.
        let mut lanes_of: HashMap<Off, (Off, Off)> = HashMap::new();
        let mut state: Option<Off> = None;
        for j in 0..n_blocks {
            let last = j + 1 == n_blocks;
            // Message lane `lambda` (8 bytes at `8 lambda`), as a K-valued sponge cell.
            let mut lane = |this: &mut Self, lambda: u32| -> SpongeCell {
                let Some(&cell) = msg.get((lambda / 2) as usize) else {
                    return SpongeCell::Zero;
                };
                let high = lambda % 2 == 1;
                match cell {
                    SpongeCell::Zero => SpongeCell::Zero,
                    SpongeCell::Const(v) => {
                        let w = if high { v.c1 } else { v.c0 };
                        if w == 0 {
                            SpongeCell::Zero
                        } else {
                            SpongeCell::Const(F192::new(w, 0, 0))
                        }
                    }
                    SpongeCell::Cell(o) => {
                        let (lo, hi) = *lanes_of.entry(o).or_insert_with(|| {
                            let lo = this.alloc_stack(1);
                            this.pending.push(Hint::Resolved(RHint::FieldLimbs {
                                value: o,
                                base: lo,
                                len: 1,
                            }));
                            let (t, hi) = (this.fresh(), this.fresh());
                            this.emit(LOp::Xor { a: o, b: lo, c: t });
                            let k = this.const_cell(y_inv);
                            this.emit(LOp::Mul { a: t, b: k, c: hi });
                            let zero = this.zero();
                            this.emit(LOp::Jump {
                                oc: zero,
                                od: lo,
                                of: hi,
                            });
                            (lo, hi)
                        });
                        SpongeCell::Cell(if high { hi } else { lo })
                    }
                }
            };
            // The block's rate: eight cells (lanes 2t, 2t+1) and lane 16.
            let first = 17 * j;
            let mut block = [SpongeCell::Zero; 9];
            for (t, slot) in block[..8].iter_mut().enumerate() {
                let lambda = first + 2 * t as u32;
                *slot = if lambda.is_multiple_of(2) {
                    msg.get((lambda / 2) as usize).copied().unwrap_or(SpongeCell::Zero)
                } else {
                    let (a, b) = (lane(self, lambda), lane(self, lambda + 1));
                    self.pack_lanes(a, b, y)
                };
            }
            block[8] = lane(self, first + 16);
            // Padding: Keccak's first byte after the message in the last block;
            // the opcode's END bit is the last one there, and is cancelled in lane
            // 16 of every other block, which carries message data instead.
            if last {
                let p = len - RATE * j;
                let (cell, byte) = ((p / 16) as usize, p % 16);
                let bits = u64::from(primitives::keccak::KECCAK_PAD_FIRST) << (8 * (byte % 8));
                let v = if cell == 8 || byte < 8 {
                    F192::new(bits, 0, 0)
                } else {
                    F192::new(0, bits, 0)
                };
                block[cell] = self.sponge_add(block[cell], v);
            } else {
                block[8] = self.sponge_add(block[8], F192::new(primitives::keccak::END_BIT, 0, 0));
            }

            let pad = Pad::Keccak;
            let (m, cap): ([Off; 8], Off) = match state {
                Some(st) => {
                    let m = std::array::from_fn(|i| self.sponge_xor(st + i as u32, block[i], None, pad));
                    let cap = if matches!(block[8], SpongeCell::Zero) {
                        st + 8
                    } else {
                        let cap = self.alloc_stack(5);
                        self.sponge_xor(st + 8, block[8], Some(cap), pad);
                        for k in 1..5 {
                            self.copy(st + 8 + k, cap + k);
                        }
                        cap
                    };
                    (m, cap)
                }
                None => {
                    let m = std::array::from_fn(|i| self.sponge_cell(block[i], pad));
                    let cap = self.alloc_stack(5);
                    self.write_sponge_cell(block[8], cap);
                    for k in 1..5 {
                        self.set_const(cap + k, F192::ZERO);
                    }
                    (m, cap)
                }
            };
            let (next, digest) = if last {
                (out.base, out.digest)
            } else {
                (self.alloc_stack(STATE_CELLS), false)
            };
            self.emit(LOp::Sha3 {
                m,
                cap,
                c: next,
                digest,
            });
            state = Some(next);
        }
    }

    /// `a + y b` for two K-valued sponge cells (lanes), as one sponge cell.
    fn pack_lanes(&mut self, a: SpongeCell, b: SpongeCell, y: F192) -> SpongeCell {
        let hi = match b {
            SpongeCell::Zero => SpongeCell::Zero,
            SpongeCell::Const(v) => SpongeCell::Const(v * y),
            SpongeCell::Cell(o) => {
                let (k, d) = (self.const_cell(y), self.fresh());
                self.emit(LOp::Mul { a: o, b: k, c: d });
                SpongeCell::Cell(d)
            }
        };
        match (a, hi) {
            (SpongeCell::Zero, h) => h,
            (l, SpongeCell::Zero) => l,
            (SpongeCell::Const(l), h) => self.sponge_add(h, l),
            (l, SpongeCell::Const(h)) => self.sponge_add(l, h),
            (SpongeCell::Cell(l), SpongeCell::Cell(h)) => {
                let d = self.fresh();
                self.emit(LOp::Xor { a: l, b: h, c: d });
                SpongeCell::Cell(d)
            }
        }
    }

    /// `c + v` for a constant `v`.
    fn sponge_add(&mut self, c: SpongeCell, v: F192) -> SpongeCell {
        match c {
            SpongeCell::Zero => SpongeCell::Const(v),
            SpongeCell::Const(w) => SpongeCell::Const(w + v),
            SpongeCell::Cell(o) => {
                let (k, d) = (self.const_cell(v), self.fresh());
                self.emit(LOp::Xor { a: o, b: k, c: d });
                SpongeCell::Cell(d)
            }
        }
    }

    /// Write `c` into the frame cell `dst`.
    fn write_sponge_cell(&mut self, c: SpongeCell, dst: Off) {
        match c {
            SpongeCell::Zero => self.set_const(dst, F192::ZERO),
            SpongeCell::Const(v) => self.set_const(dst, v),
            SpongeCell::Cell(o) => self.copy(o, dst),
        }
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

    /// Where a `sha3` writes: the stack run the instruction targets, the whole
    /// state or, for a 2-cell destination, the digest alone (a digest step), and
    /// the heap run to store it to afterwards.
    fn sha3_out(&mut self, e: &Expr) -> Sha3Out {
        match self.cell_run(e) {
            CellRun::Stack { base, len } if len >= STATE_CELLS => Sha3Out {
                base,
                digest: false,
                heap: None,
            },
            CellRun::Stack { base, len: 2 } => Sha3Out {
                base,
                digest: true,
                heap: None,
            },
            run @ CellRun::Heap { len, .. } if len == STATE_CELLS || len == 2 => Sha3Out {
                base: self.alloc_stack(len),
                digest: len == 2,
                heap: Some(run),
            },
            _ => self.fail(format!(
                "a sha3 destination is a {STATE_CELLS}-cell run (the state) or a 2-cell run (the digest)"
            )),
        }
    }

    /// Store what [`Self::sha3_out`] wrote to the heap run it promised.
    fn sha3_finish(&mut self, out: Sha3Out) {
        if let Some(CellRun::Heap { ptr, lo, len }) = out.heap {
            for k in 0..len {
                self.deref(ptr, lo + k, out.base + k, DerefMode::Cell);
            }
        }
    }

    /// Emit one `SHA3` block into `out`: the padding `pad_kind` folded into the
    /// message if `final_len` says this block ends it, the message XORed into
    /// `state` if there is one, and every zero or padding cell of a fresh block one
    /// of the padding run's. The eight message cells are the instruction's own
    /// operands, so nothing is gathered into a consecutive run.
    fn emit_sha3_block(
        &mut self,
        mut block: [SpongeCell; 8],
        state: Option<Off>,
        final_len: Option<u32>,
        out: &Sha3Out,
        pad_kind: Pad,
    ) {
        // Padding in lane 16, the lone cell: only a final block of 128 bytes.
        // Below that the padding byte goes into the message.
        let mut lone_pad = false;
        if let Some(len) = final_len {
            if len == 128 {
                lone_pad = true;
            } else {
                let (cell, byte) = ((len / 16) as usize, len % 16);
                let pad = u64::from(pad_kind.byte()) << (8 * (byte % 8));
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
            }
        }

        let (m, cap): ([Off; 8], Off) = match state {
            // A later block: XOR the message into the previous state's rate cells.
            // A zero message cell passes the state's cell through, and the capacity
            // is the previous run's unless the padding lands in lane 16.
            Some(st) => {
                let m = std::array::from_fn(|i| self.sponge_xor(st + i as u32, block[i], None, pad_kind));
                let cap = if lone_pad {
                    let cap = self.alloc_stack(5);
                    let pad = self.pad_run(pad_kind);
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
                (m, cap)
            }
            // The first block, from the zero state: every constant window comes out
            // of the one padding run.
            None => {
                let pad = self.pad_run(pad_kind);
                let m = std::array::from_fn(|i| self.sponge_cell(block[i], pad_kind));
                (m, if lone_pad { pad } else { pad + 1 })
            }
        };
        self.emit(LOp::Sha3 {
            m,
            cap,
            c: out.base,
            digest: out.digest,
        });
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
                if args.len() != 3 {
                    self.fail(format!(
                        "{f} takes three arguments, `(bits, value, nbits)`, got {}",
                        args.len()
                    ))
                };
                let nbits = self.const_index(&args[2]);
                let bits = self.bits_dest(&args[0], nbits, f);
                let value = self.expr(&args[1]);
                self.pending.push(Hint::Resolved(if f == "hint_decompose_bits" {
                    RHint::BitDecompose { value, bits, nbits }
                } else {
                    RHint::BitDecomposeExp { value, bits, nbits }
                }));
            }
            "blake2s" => self.lower_blake2s(args),
            "sha3" => self.lower_sha3(args),
            "sha3_cells" => self.lower_sha3_cells(args),
            "keccak" => self.lower_keccak(args),
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

    /// Resolve a `blake2s` operand: a [`Self::cell_run`] pinned to exactly 2
    /// cells, a 256-bit value being two 128-bit cells. Stack operands are used
    /// in place; heap operands must be bridged through the stack, since
    /// `BLAKE2s` addresses only frame cells (see [`Self::blake2s_input`]).
    fn blake2s_operand(&mut self, e: &Expr) -> CellRun {
        let run = self.cell_run(e);
        if run.cells() != 2 {
            self.fail("a blake2s operand must span exactly 2 cells (two 128-bit words); slice a larger buffer: `buf[lo:lo + 2]`")
        };
        run
    }

    /// A `blake2s` *input* operand as its two independently-addressed 128-bit
    /// chunk bases (each chunk is ONE 128-bit cell): stack runs in place; a heap
    /// slice is pulled into a fresh stack pair first, one `DEREF` per cell
    /// (`m[ptr·g^{lo+k}] == m[fp+t+k]`, the `β` immediate doing the pointer
    /// offset). The heap cells must already be written.
    ///
    /// A LIST LITERAL names its two words directly and allocates nothing. The
    /// opcode addresses its four input chunks independently, so an operand
    /// assembled out of values living elsewhere never has to be gathered into a
    /// consecutive run: `blake2s([a, b], …)` is the spelling that says so.
    pub(super) fn blake2s_input(&mut self, e: &Expr) -> [Off; 2] {
        if let Expr::ListLit(words) = e {
            if words.len() != 2 {
                self.fail(format!(
                    "a blake2s operand written as a list needs exactly 2 words, got {}",
                    words.len()
                ))
            };
            return [self.expr(&words[0]), self.expr(&words[1])];
        }
        match self.blake2s_operand(e) {
            CellRun::Stack { base, .. } => [base, base + 1],
            CellRun::Heap { ptr, lo, .. } => {
                let t = self.alloc_stack(2);
                for k in 0..2 {
                    self.deref(ptr, lo + k, t + k, DerefMode::Cell);
                }
                [t, t + 1]
            }
        }
    }

    fn default_blake2s_cv(&mut self) -> Off {
        if let Some(o) = self.scope.blake2s_iv {
            return o;
        }
        let o = self.alloc_stack(2);
        for (k, value) in lean_vm::hash_flock::IV_CELLS.into_iter().enumerate() {
            self.set_const(o + k as u32, value);
            self.scope
                .const_cells
                .entry([value.c0, value.c1, value.c2])
                .or_insert(o + k as u32);
        }
        self.scope.blake2s_iv = Some(o);
        o
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

    /// A frame cell holding `c`, zero and the padding cell out of `pad`'s run.
    fn sponge_cell(&mut self, c: SpongeCell, pad: Pad) -> Off {
        match c {
            SpongeCell::Zero => self.pad_run(pad) + 1,
            SpongeCell::Const(v) if v == pad.value() => self.pad_run(pad),
            SpongeCell::Const(v) => self.const_cell(v),
            SpongeCell::Cell(o) => o,
        }
    }

    /// `state ⊕ c`, into `dst` if given: a zero `c` is the state cell itself (or
    /// a copy of it into `dst`).
    fn sponge_xor(&mut self, state: Off, c: SpongeCell, dst: Option<Off>, pad: Pad) -> Off {
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
            c => self.sponge_cell(c, pad),
        };
        let d = dst.unwrap_or_else(|| self.fresh());
        self.emit(LOp::Xor {
            a: state,
            b: other,
            c: d,
        });
        d
    }

    /// The six cells `[pad, 0, 0, 0, 0, 0]` every fresh `sha3` (or `keccak`) in
    /// this scope shares ([`Scope::sha3_pad`]): a zero `cap` starts at `+1` and a
    /// 128-byte message's at `+0`, and a zero or padding message cell is one of them.
    fn pad_run(&mut self, pad: Pad) -> Off {
        if let Some(o) = self.scope.sha3_pad[pad as usize] {
            return o;
        }
        let o = self.alloc_stack(6);
        for k in 0..6 {
            let value = if k == 0 { pad.value() } else { F192::ZERO };
            self.set_const(o + k, value);
            self.scope
                .const_cells
                .entry([value.c0, value.c1, value.c2])
                .or_insert(o + k);
        }
        self.scope.sha3_pad[pad as usize] = Some(o);
        o
    }

    /// A computed-advice bit buffer's destination ([`BitsDest`]). Not
    /// [`Self::cell_run`]: these builtins take a bare `HeapBuf` and carry the
    /// length in `nbits`, where a cell run would demand a slice.
    pub(super) fn bits_dest(&mut self, e: &Expr, nbits: u32, what: &str) -> BitsDest {
        // A `StackBuf`, or a compile-time slice of one: a run of frame cells.
        let stack = match e {
            Expr::Slice(arr, ..) if self.stack_of(arr).is_some() => match self.cell_run(e) {
                CellRun::Stack { base, len } => Some((base, len)),
                CellRun::Heap { .. } => unreachable!("a StackBuf slice is a stack run"),
            },
            _ => self.stack_of(e),
        };
        match stack {
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
    /// A BLAKE2s chaining value must occupy two consecutive frame cells because
    /// the opcode carries one base offset for both words. Preserve a genuine
    /// consecutive pair, including a heap pair already bridged by
    /// [`Self::blake2s_input`]. A `cv` written as a two-word LIST exposes two
    /// sources that need not be adjacent, so those are copied into a fresh
    /// consecutive pair.
    fn blake2s_cv(&mut self, e: &Expr) -> Off {
        let pair = self.blake2s_input(e);
        if pair[1] == pair[0] + 1 {
            return pair[0];
        }
        let cv = self.alloc_stack(2);
        self.copy(pair[0], cv);
        self.copy(pair[1], cv + 1);
        cv
    }
}

/// Cells a sponge state occupies.
const STATE_CELLS: u32 = lean_vm::hash_flock_keccak::STATE_CELLS as u32;

/// The padding a sponge block uses: SHA3-256's (`sha3`, the leanVM hash) or
/// Keccak-256's (`keccak`, the EVM's). They differ only in the first padding
/// byte; the last bit is the opcode's own.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Pad {
    Sha3 = 0,
    Keccak = 1,
}

impl Pad {
    fn byte(self) -> u8 {
        match self {
            Self::Sha3 => primitives::keccak::PAD_FIRST,
            Self::Keccak => primitives::keccak::KECCAK_PAD_FIRST,
        }
    }

    /// A cell holding the padding's first byte at its start, in the low lane.
    fn value(self) -> F192 {
        F192::new(u64::from(self.byte()), 0, 0)
    }
}

/// Where a `sha3` writes: the stack run its instruction targets, the 13-cell
/// state or with `digest` the 2-cell digest alone, and a heap run to store it to
/// afterwards.
struct Sha3Out {
    base: Off,
    digest: bool,
    heap: Option<CellRun>,
}

/// One message cell of a `sha3` block, as the lowering knows it.
#[derive(Clone, Copy, Debug)]
enum SpongeCell {
    Zero,
    Const(F192),
    Cell(Off),
}
