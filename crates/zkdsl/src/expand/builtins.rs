//! The Keccak builtins and the hints: the two places a value arrives without an instruction computing it.

use super::*;

impl FnExpand<'_> {
    /// `keccak(a, b, out, tail=, len=, cap=, pad_tail=)`: the Keccak-256 of the first `len` bytes of
    /// `a ‖ b ‖ tail`, one `KECCAK`; with `cap=`, the duplex step in overwrite mode over the five cells a previous
    /// output ends with.
    fn lower_keccak(&mut self, args: &[Expr]) {
        let kwargs = self.keccak_kwargs(args, "keccak", &["a", "b", "out"], &["tail", "len", "cap", "pad_tail"]);
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
            let mut ins = m.to_vec();
            ins.extend(Self::run(tail, 4));
            ins.extend(Self::run(cap, 5));
            self.atom(Atom::Keccak {
                ins,
                outs: Self::run(out.state, out.cells),
                in_odd: false,
                out_odd: false,
            });
            self.keccak_finish(out);
            return;
        }
        let len = self.keccak_len(&kwargs, cells.len() as u32);
        let padded = kwargs.contains_key("pad_tail");
        if padded {
            self.pad_tail_in_place(&kwargs, &cells, len);
        }
        let out = self.keccak_out(&args[2]);
        self.emit_keccak_message(cells, Some(len), None, &out, padded);
        self.keccak_finish(out);
    }

    /// `pad_tail=1`: set the cells of the `tail` slice from `len` on to the padding (its first byte, then zeros).
    fn pad_tail_in_place(&mut self, kwargs: &HashMap<&str, &Expr>, cells: &[SpongeCell], len: u32) {
        const TAIL: usize = 4;
        if kwargs.get("pad_tail").and_then(|e| self.try_const_int(e)) != Some(1) {
            self.fail("keccak pad_tail= takes 1")
        }
        let base = match kwargs.get("tail").map(|tail| self.try_cell_run(tail)) {
            Some(Ok(CellRun::Stack { base, .. })) => base,
            _ => self.fail("keccak pad_tail=1 needs tail= a StackBuf slice"),
        };
        let past = len as usize / 16;
        if !len.is_multiple_of(16) || !(TAIL..cells.len()).contains(&past) {
            self.fail(format!(
                "keccak pad_tail=1 needs len= ending a tail cell (64, 80, 96 or 112), got {len}"
            ))
        }
        let set = base + (past - TAIL) as u32..base + (cells.len() - TAIL) as u32;
        if cells[..TAIL]
            .iter()
            .any(|cell| matches!(cell, SpongeCell::Cell(o) if set.contains(o)))
        {
            self.fail("keccak pad_tail=1: a or b reads a cell past len, which the padding sets")
        }
        for (k, o) in set.enumerate() {
            self.set_const(o, if k == 0 { keccak_pad_value() } else { F128::ZERO });
        }
    }

    /// `keccak_cells(cells, out, state=, len=, final=)`: the Keccak-256 of the message the cells hold, 136 bytes a
    /// `KECCAK`, continuing `state` if given; `final=0` absorbs the cells zero-extended to whole blocks, unpadded.
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
        self.emit_keccak_message(cells, final_len, state, &out, false);
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
            let mut bad: Vec<&&str> = kwargs.keys().filter(|k| !allowed.contains(k)).collect();
            bad.sort_unstable();
            self.fail(format!("unknown keccak keyword {bad:?}; the keywords are {allowed:?}"))
        };
        kwargs
    }

    /// Where a `keccak` writes: a run of one or two values, or the first thirteen of a longer one, in place; else
    /// a fresh run for a heap run of one, two or thirteen cells, copied there afterwards.
    fn keccak_out(&mut self, e: &Expr) -> KeccakOut {
        match self.cell_run(e) {
            CellRun::Stack {
                base,
                len: len @ (1 | 2 | STATE_CELLS..),
            } => KeccakOut {
                state: base,
                cells: len.min(STATE_CELLS),
                heap: None,
            },
            CellRun::Heap {
                ptr,
                lo,
                len: len @ (1 | 2 | STATE_CELLS),
            } => KeccakOut {
                state: self.alloc_stack(len),
                cells: len,
                heap: Some((ptr, lo)),
            },
            _ => self.fail(format!(
                "a keccak destination is a {STATE_CELLS}-cell run (the state), a 2-cell run (the digest) or a 1-cell run (its first cell)"
            )),
        }
    }

    /// Copy what [`Self::keccak_out`] promised out of the values written.
    fn keccak_finish(&mut self, out: KeccakOut) {
        if let Some((ptr, lo)) = out.heap {
            self.load_run(ptr, lo, out.cells, out.state);
        }
    }

    /// The `KECCAK` atoms absorbing `cells` into `state` (the zero state if `None`), the last writing the values
    /// of `out`, each earlier one a whole 13-value state the next one reads. With `final_len` the message is the
    /// cells' first `final_len` bytes, padded; without, the cells zero-extended to whole blocks. `padded`: the
    /// cells past `final_len` already hold the padding.
    fn emit_keccak_message(
        &mut self,
        mut cells: Vec<SpongeCell>,
        final_len: Option<u32>,
        state: Option<V>,
        out: &KeccakOut,
        padded: bool,
    ) {
        let blocks = match final_len {
            Some(len) => keccak256::permutations(len as usize),
            None => (16 * cells.len()).div_ceil(RATE),
        };
        let read = 17 * (blocks - 1) / 2 + BLOCK_CELLS as usize;
        if cells.len() < read {
            cells.resize(read, SpongeCell::Zero);
        }
        if let Some(len) = final_len {
            if !padded {
                let past = (len as usize).div_ceil(16);
                if let Some(k) = (past..cells.len()).find(|&k| !matches!(cells[k], SpongeCell::Zero)) {
                    self.fail(format!(
                        "keccak len= {len} ends before message cell {k}, which is not a literal 0"
                    ))
                }
                self.xor_byte(&mut cells, len as usize, keccak256::PAD_FIRST);
            }
            self.xor_byte(&mut cells, blocks * RATE - 1, keccak256::PAD_LAST);
        }
        let mut state = state;
        for k in 0..blocks {
            let last = k + 1 == blocks;
            let (c, out_cells) = if last {
                (out.state, out.cells)
            } else {
                (self.alloc_stack(STATE_CELLS), STATE_CELLS)
            };
            let block = &cells[17 * k / 2..][..BLOCK_CELLS as usize];
            let (m, tail) = self.keccak_rate(block, state);
            let b8 = match state {
                None => self.sponge_cell(block[8]),
                Some(st) => self.sponge_xor(st + 8, block[8], None),
            };
            let cap = state.map_or_else(|| self.keccak_pad_run() + 1, |st| st + 9);
            let mut ins = m.to_vec();
            ins.extend(Self::run(tail, 4));
            ins.push(b8);
            ins.extend(Self::run(cap, 4));
            self.atom(Atom::Keccak {
                ins,
                outs: Self::run(c, out_cells),
                in_odd: k % 2 == 1,
                out_odd: !last && k % 2 == 0,
            });
            state = Some(c);
        }
    }

    /// XOR the byte `v` into byte `at` of the message cells: into a constant, or by one `add` with a constant.
    fn xor_byte(&mut self, cells: &mut [SpongeCell], at: usize, v: u8) {
        let (cell, byte) = (at / 16, at % 16);
        let w = u64::from(v) << (8 * (byte % 8));
        let v = if byte < 8 { F128::new(w, 0) } else { F128::new(0, w) };
        cells[cell] = match cells[cell] {
            SpongeCell::Zero => SpongeCell::Const(v),
            SpongeCell::Const(c) => SpongeCell::Const(c + v),
            SpongeCell::Cell(o) => {
                let k = self.const_cell(v);
                let dst = self.fresh();
                self.atom(Atom::Add(dst, o, k));
                SpongeCell::Cell(dst)
            }
        };
    }

    /// The `m` values and the `tail` run of a `KECCAK` reading the block's first eight cells: themselves from the
    /// zero state, or XORed into the values of the previous output `st` they line up with.
    fn keccak_rate(&mut self, block: &[SpongeCell], st: Option<V>) -> ([V; 4], V) {
        let Some(st) = st else {
            let m = [0, 1, 2, 3].map(|i| self.sponge_cell(block[i]));
            return (m, self.sponge_run(&block[4..8]));
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

    /// `state + c`, into `dst` if given: a zero `c` is the state value itself, or a copy of it into `dst`.
    fn sponge_xor(&mut self, state: V, c: SpongeCell, dst: Option<V>) -> V {
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
        self.atom(Atom::Add(d, state, other));
        d
    }

    /// A run of values holding the message cells: where they already lie, a window of the padding run, or a fresh
    /// copy.
    fn sponge_run(&mut self, cells: &[SpongeCell]) -> V {
        let vals: Vec<V> = cells
            .iter()
            .filter_map(|c| match c {
                SpongeCell::Cell(o) => Some(*o),
                _ => None,
            })
            .collect();
        if vals.len() == cells.len() && vals.windows(2).all(|w| self.adjacent(w[0], w[1])) {
            return vals[0];
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
                SpongeCell::Zero => self.set_const(dst, F128::ZERO),
                SpongeCell::Const(v) => self.set_const(dst, v),
                SpongeCell::Cell(o) => self.copy(o, dst),
            }
        }
        t
    }

    /// The statement-position builtins, `true` if `f` was one of them.
    pub(super) fn lower_builtin(&mut self, f: &str, args: &[Expr]) -> bool {
        match f {
            "hint_decompose_bits" | "hint_decompose_bits_exponent" => {
                let plain = f == "hint_decompose_bits";
                if args.len() != 3 {
                    self.fail(format!(
                        "{f} takes `(bits, value, nbits)`, got {} arguments",
                        args.len()
                    ))
                };
                let nbits = self.const_index(&args[2]);
                if !plain && nbits > MAX_EXPONENT_BITS {
                    self.fail(format!("{f} writes at most {MAX_EXPONENT_BITS} bits, got {nbits}"))
                }
                let dest = self.bits_dest(&args[0], nbits, f);
                let value = self.expr(&args[1]);
                if plain {
                    if nbits > 128 {
                        self.fail(format!("{f} reads {nbits} bits of a 128-bit word"))
                    };
                    self.hint(Hint::Bits {
                        value,
                        start: 0,
                        nbits,
                        dest,
                    });
                } else {
                    self.hint(Hint::BitsExp { value, nbits, dest });
                }
            }
            "hint_windows_exponent" => {
                if !(5..=6).contains(&args.len()) {
                    self.fail(format!(
                        "{f} takes `(dest, value, start, width, count[, at])`, got {} arguments",
                        args.len()
                    ))
                };
                let start = self.const_index(&args[2]);
                let width = self.const_index(&args[3]);
                let count = self.const_index(&args[4]);
                if !(1..=16).contains(&width) || u64::from(start) + u64::from(width * count) > 128 {
                    self.fail(format!("{f}: windows of 1..=16 bits inside a 128-bit word"))
                };
                let at = args.get(5).map_or(0, |at| self.const_index(at));
                let dest = match self.bits_dest(&args[0], at + count, f) {
                    Dest::Stack(cells) => Dest::Stack(cells[at as usize..].to_vec()),
                    Dest::Heap { ptr, off, len } => Dest::Heap {
                        ptr,
                        off: off + at,
                        len: len - at,
                    },
                };
                let value = self.expr(&args[1]);
                self.hint(Hint::WindowsExp {
                    value,
                    start,
                    width,
                    count,
                    dest,
                });
            }
            "hint_decompose_digits_exponent" => {
                if args.len() != 6 {
                    self.fail(format!(
                        "{f} takes `(dest, value, nbits, ndigits, digit_bits, start)`, got {} arguments",
                        args.len()
                    ))
                };
                let nbits = self.const_index(&args[2]);
                let ndigits = self.const_index(&args[3]);
                let digit_bits = self.const_index(&args[4]);
                if nbits > MAX_EXPONENT_BITS || !(1..=16).contains(&digit_bits) {
                    self.fail(format!("{f}: nbits <= {MAX_EXPONENT_BITS} and 1 <= digit_bits <= 16"))
                }
                let dest = self.bits_dest(&args[0], ndigits, f);
                let value = self.expr(&args[1]);
                let (start, start_cell) = match self.try_const_index(&args[5]) {
                    Some(k) => (k, None),
                    None => (0, Some(self.expr(&args[5]))),
                };
                self.hint(Hint::DigitsExp {
                    value,
                    nbits,
                    ndigits,
                    digit_bits,
                    start,
                    start_cell,
                    dest,
                });
            }
            "keccak" => self.lower_keccak(args),
            "keccak_cells" => self.lower_keccak_cells(args),
            "assert_in_k" => {
                if args.len() != 2 {
                    self.fail("assert_in_k(a, b) takes two scalar cells")
                };
                let a = self.expr(&args[0]);
                let b = self.expr(&args[1]);
                self.atom(Atom::AssertInK(a, b));
            }
            "assert_gpow" => {
                if args.len() != 1 {
                    self.fail("assert_gpow(x) takes one scalar cell")
                };
                let x = self.expr(&args[0]);
                let t = self.fresh();
                self.atom(Atom::Touch(t, x));
            }
            "hint_f128_limbs" => {
                if args.len() != 2 {
                    self.fail(format!(
                        "hint_f128_limbs takes two arguments, `(dest, value)`, got {}",
                        args.len()
                    ))
                };
                let (base, len) = self.stack_of(&args[0]).unwrap_or_else(|| {
                    self.fail(format!(
                        "hint_f128_limbs writes 1..=2 frame cells, so its destination must be a \
                             StackBuf, got `{:?}`",
                        args[0]
                    ))
                });
                if !((1..=2).contains(&len)) {
                    self.fail("hint_f128_limbs destination must have 1..=2 cells")
                };
                let value = self.expr(&args[1]);
                self.hint(Hint::Limbs {
                    value,
                    dest: Self::run(base, len),
                });
            }
            _ => return false,
        }
        true
    }

    /// The message cells `e` names: a list literal's words (a literal `0` a known zero), or a run of values, a
    /// heap run loaded into a fresh run.
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

    /// The values holding the last `n` cells of a previous 13-cell output `e`, or `e` as those `n` cells alone: a
    /// run in place, a heap run loaded into a fresh one.
    fn prev_state(&mut self, e: &Expr, n: u32) -> Option<V> {
        match self.try_cell_run(e).ok()? {
            CellRun::Stack { base, len } if len >= STATE_CELLS => Some(base + STATE_CELLS - n),
            CellRun::Stack { base, len } if len == n => Some(base),
            CellRun::Heap { ptr, lo, len } if len == STATE_CELLS || len == n => {
                Some(self.heap_to_stack(ptr, lo + len - n, n))
            }
            _ => None,
        }
    }

    /// [`Self::cell_run`], or `Err` for an expression that names no run.
    fn try_cell_run(&mut self, e: &Expr) -> Result<CellRun, ()> {
        match e {
            Expr::Var(_) | Expr::Slice(..) => Ok(self.cell_run(e)),
            _ => Err(()),
        }
    }

    /// A value holding the message cell `c`.
    fn sponge_cell(&mut self, c: SpongeCell) -> V {
        match c {
            SpongeCell::Zero => self.keccak_pad_run() + 1,
            SpongeCell::Const(v) if v == keccak_pad_value() => self.keccak_pad_run(),
            SpongeCell::Const(v) => self.const_cell(v),
            SpongeCell::Cell(o) => o,
        }
    }

    /// The run `[pad, 0, 0, 0, 0]` every `keccak` of this scope shares, set at the first: the zero `tail` and
    /// `cap` are its window from `+1`, a 64-byte message's `tail` its window from `+0`.
    pub(super) fn keccak_pad_run(&mut self) -> V {
        if let Some(o) = self.scope.keccak_pad {
            return o;
        }
        let o = self.alloc_stack(5);
        for k in 0..5 {
            let value = if k == 0 { keccak_pad_value() } else { F128::ZERO };
            self.set_const(o + k, value);
            self.scope.consts.insert(value);
        }
        self.scope.keccak_pad = Some(o);
        o
    }

    /// A computed-advice bit buffer's destination: the first `nbits` values of a `StackBuf`, or `nbits` cells of a
    /// bounds-checked heap buffer.
    pub(super) fn bits_dest(&mut self, e: &Expr, nbits: u32, what: &str) -> Dest {
        match self.stack_of(e) {
            Some((base, len)) => {
                if len < nbits {
                    self.fail(format!(
                        "{what} needs {nbits} cells, its StackBuf destination has {len}"
                    ))
                };
                Dest::Stack(Self::run(base, nbits))
            }
            None => {
                self.check_heap_bound(e, 0, u128::from(nbits));
                Dest::Heap {
                    ptr: self.expr(e),
                    off: 0,
                    len: nbits,
                }
            }
        }
    }

    /// `hint_witness(dest, "name")`: the stream's next entry into the run `dest` names.
    pub(super) fn lower_hint_witness(&mut self, dest: &Expr, name: &str) {
        let dest = match self.cell_run(dest) {
            CellRun::Stack { base, len } => Dest::Stack(Self::run(base, len)),
            CellRun::Heap { ptr, lo, len } => Dest::Heap { ptr, off: lo, len },
        };
        self.hint(Hint::Witness {
            stream: name.to_string(),
            dest,
        });
    }
}

/// Cells a sponge state occupies.
const STATE_CELLS: u32 = isa::STATE_CELLS as u32;
/// The rate cells of a state, the nine a block covers.
const BLOCK_CELLS: u32 = isa::RATE_CELLS as u32;
/// Bytes a block absorbs.
const RATE: usize = keccak256::RATE;
/// The largest `nbits` a `hint_decompose_*_exponent` accepts.
const MAX_EXPONENT_BITS: u32 = 40;

/// The last rate lane of a 64-byte message's one block: the padding's closing `0x80` byte.
pub(super) fn two_to_one_close() -> F128 {
    F128::new(0x80 << 56, 0)
}

/// A cell holding the padding's first byte at its start: `0x01` in the low lane.
fn keccak_pad_value() -> F128 {
    F128::new(u64::from(keccak256::PAD_FIRST), 0)
}

/// Where a `keccak` writes: the run its last atom writes, the count of values written there, and a heap run to
/// copy them to afterwards.
struct KeccakOut {
    state: V,
    cells: u32,
    heap: Option<(V, u32)>,
}

/// One message cell of a `keccak` block: a literal zero, a constant, or a value.
#[derive(Clone, Copy, Debug)]
enum SpongeCell {
    Zero,
    Const(F128),
    Cell(V),
}
