//! The recorded verifier lowered to RISC-V: extension registers allocated, hashes laid on their blocks, every address fixed.
//!
//! An element lives in an extension register while it is used, and nowhere else unless it came from memory.
//!
//! An element evicted while still needed, and with no place in memory, is stored to the scratch words by `esd` and
//! loaded back by `eld` when it is needed.

use super::record::{ELEMENT, Gen, Home, Loc, Op, POW_TAGS, leaf_slot};
use crate::rec::hash::PARAM_IV;
use crate::rv::Region;
use crate::rv::asm::*;
use crate::tables::Clock;
use ::pcs::whir::Stratum;
use std::collections::VecDeque;
use std::ops::Range;

/// The lowered program: its text and the size of its RAM.
pub(super) struct Lowered {
    /// The instructions.
    pub(super) text: Vec<u32>,
    /// The base-two logarithm of RAM's words.
    pub(super) log_ram: usize,
}

/// Integer registers the program keeps for one purpose.
mod reg {
    use crate::rv::Reg;

    /// Scratch.
    pub(super) const T: [Reg; 6] = [Reg::T0, Reg::T1, Reg::T2, Reg::T3, Reg::T4, Reg::T5];
    /// Pointers a compression is given, computed where they are used.
    pub(super) const P: [Reg; 3] = [Reg::RA, Reg::SP, Reg::GP];
    /// The transcript's state where no challenge holds it, then the two registers that follow it into a challenge.
    pub(super) const STATE: [Reg; 3] = [Reg::S0, Reg::S1, Reg::S2];
    /// A message built from words that are elsewhere.
    pub(super) const MESSAGE: Reg = Reg::S3;
    /// The parameter block's state: a one-block hash's chaining value.
    pub(super) const IV: Reg = Reg::S4;
    /// The constant 64, a one-block hash's counter.
    pub(super) const BLOCK_BYTES: Reg = Reg::S5;
    /// A chain's state between its blocks.
    pub(super) const CHAINED: Reg = Reg::TP;
    /// Registers each holding the base of one page of memory.
    pub(super) const PAGES: [Reg; 14] = [
        Reg::A0,
        Reg::A1,
        Reg::A2,
        Reg::A3,
        Reg::A4,
        Reg::A5,
        Reg::A6,
        Reg::A7,
        Reg::S6,
        Reg::S7,
        Reg::S8,
        Reg::S9,
        Reg::S10,
        Reg::S11,
    ];
}

/// The first extension register an element is allocated, after the constants and one scratch register.
const FIRST: u8 = 4;
/// The scratch extension register: where a check that keeps both its operands leaves its zero.
const SCRATCH: u8 = 3;
/// How many extension registers there are.
const REGISTERS: u8 = 128;

/// The program's own hash blocks, as words of [`Loc::Block`]: the parameter block's state, the transcript's state, a
/// message, a chain's state, then one message per tag of a step that absorbs nothing.
mod block {
    pub(super) const IV: usize = 0;
    pub(super) const STATE: usize = 4;
    pub(super) const MESSAGE: usize = 8;
    pub(super) const CHAINED: usize = 16;
    pub(super) const TAGS: usize = 24;
}

struct Lower<'g> {
    g: &'g Gen<'g>,
    a: Asm,
    /// Each element's uses still to come, as operation indices.
    uses: Vec<VecDeque<u32>>,
    /// The register holding each element, if one does.
    at: Vec<Option<u8>>,
    /// The element each register holds.
    held: [Option<u32>; REGISTERS as usize],
    /// Where each evicted element was stored.
    spilled: Vec<Option<Loc>>,
    /// The scratch words in use, the recorder's then the stored elements'.
    n_scratch: usize,
    /// The page each page register holds, and when it was last used.
    pages: [(u64, u64); reg::PAGES.len()],
    tick: u64,
    /// The register pointing at the transcript's state.
    state: Reg,
    /// The tags with a message block of their own.
    tags: Vec<u64>,
    consts: u64,
    blocks: u64,
    scratch: u64,
}

impl Lower<'_> {
    /// The byte address of a location.
    const fn address(&self, loc: Loc) -> u64 {
        match loc {
            Loc::Const(i) => self.consts + 8 * i as u64,
            Loc::Advice(i) => Region::ADVICE.base() + 8 * i as u64,
            Loc::Scratch(i) => self.scratch + 8 * i as u64,
            Loc::Block(i) => self.blocks + 8 * i as u64,
        }
    }

    /// A register and an offset naming the word at `loc`: a page register, loaded if no register holds the page.
    fn word(&mut self, loc: Loc) -> (Reg, i32) {
        let address = self.address(loc);
        let page = (address + 0x800) >> 12;
        let offset = address as i64 - ((page as i64) << 12);
        self.tick += 1;
        let slot = match self.pages.iter().position(|&(p, _)| p == page) {
            Some(slot) => slot,
            None => {
                let slot = (0..self.pages.len())
                    .min_by_key(|&i| self.pages[i].1)
                    .expect("a page register");
                self.a.lui(reg::PAGES[slot], page as u32);
                self.pages[slot].0 = page;
                slot
            }
        };
        self.pages[slot].1 = self.tick;
        (reg::PAGES[slot], offset as i32)
    }

    fn ld(&mut self, rd: Reg, loc: Loc) {
        let (base, offset) = self.word(loc);
        self.a.load(Ld, rd, offset, base);
    }

    fn sd(&mut self, rs: Reg, loc: Loc) {
        let (base, offset) = self.word(loc);
        self.a.store(Sd, rs, offset, base);
    }

    /// Point `r` at `loc`.
    fn pointer(&mut self, r: Reg, loc: Loc) {
        let (base, offset) = self.word(loc);
        self.a.i(Addi, r, base, offset);
    }

    /// The memory home of an element read off the proof.
    fn placed(&self, e: u32) -> Loc {
        match self.g.es[e as usize].0 {
            Home::Mem(loc) => loc,
            home => unreachable!("a scalar of the proof has a place, not {home:?}"),
        }
    }

    /// Trap unless the two registers are equal.
    fn assert_eq(&mut self, x: Reg, y: Reg) {
        self.a.word(BranchOp::Beq.encode(x, y, 8).bits()).word(0);
    }

    /// Copy `n` words.
    fn copy(&mut self, from: impl Fn(usize) -> Word, to: impl Fn(usize) -> Word, n: usize) {
        for i in 0..n {
            let t = reg::T[0];
            match from(i) {
                Word::At(loc) => self.ld(t, loc),
                Word::Block(base, offset) => {
                    self.a.load(Ld, t, offset, base);
                }
            }
            match to(i) {
                Word::At(loc) => self.sd(t, loc),
                Word::Block(base, offset) => {
                    self.a.store(Sd, t, offset, base);
                }
            }
        }
    }

    /// Load the element at `loc`, on a 32-byte boundary, into register `f`.
    fn load(&mut self, f: u8, loc: Loc) {
        debug_assert!(
            self.address(loc).is_multiple_of(8 * ELEMENT as u64),
            "an element's slot"
        );
        let (base, offset) = self.word(loc);
        self.a.eld(f, offset, base);
    }

    /// Store register `f` at `loc`, on a 32-byte boundary.
    fn store(&mut self, f: u8, loc: Loc) {
        debug_assert!(
            self.address(loc).is_multiple_of(8 * ELEMENT as u64),
            "an element's slot"
        );
        let (base, offset) = self.word(loc);
        self.a.esd(f, offset, base);
    }

    /// Whether the element is used after the operation being lowered.
    fn live(&self, e: u32) -> bool {
        !self.uses[e as usize].is_empty()
    }

    /// Where the element can be loaded from, if anywhere.
    fn home(&self, e: u32) -> Option<Loc> {
        match self.g.es[e as usize].0 {
            Home::Mem(loc) => Some(loc),
            _ => self.spilled[e as usize],
        }
    }

    /// Give up the register of an element: store it first if it is still needed and has no home.
    fn release(&mut self, f: u8) {
        let Some(e) = self.held[f as usize].take() else { return };
        self.at[e as usize] = None;
        if self.live(e) && self.home(e).is_none() {
            let loc = Loc::Scratch(self.n_scratch.next_multiple_of(ELEMENT));
            self.n_scratch = self.n_scratch.next_multiple_of(ELEMENT) + ELEMENT;
            self.spilled[e as usize] = Some(loc);
            self.store(f, loc);
        }
    }

    /// A register free to write, none of `keep`: a free one, else the one whose element is used furthest on.
    fn free(&mut self, keep: &[u8]) -> u8 {
        let candidates = (FIRST..REGISTERS).filter(|f| !keep.contains(f));
        let next_use = |held: Option<u32>| match held {
            None => (2, 0),
            Some(e) => match self.uses[e as usize].front() {
                None => (2, 0),
                Some(&at) => (u32::from(self.home(e).is_some()), at),
            },
        };
        // An element that is free to drop first, then one with a home, then the furthest use.
        let f = candidates
            .max_by_key(|&f| {
                let (class, at) = next_use(self.held[f as usize]);
                (class == 2, at, class)
            })
            .expect("more registers than an instruction pins");
        self.release(f);
        f
    }

    /// The register holding the element, loading it if none does.
    fn register(&mut self, e: u32, keep: &[u8]) -> u8 {
        if let Home::Pinned(f) = self.g.es[e as usize].0 {
            return f;
        }
        if let Some(f) = self.at[e as usize] {
            return f;
        }
        let f = self.free(keep);
        let loc = self.home(e).expect("an element not in a register has a home");
        self.load(f, loc);
        self.bind(f, e);
        f
    }

    fn bind(&mut self, f: u8, e: u32) {
        self.held[f as usize] = Some(e);
        self.at[e as usize] = Some(f);
    }

    /// The register `out = d + ...` accumulates into, holding `d`: `d`'s own if `d` is not used again, else a copy.
    fn accumulator(&mut self, d: u32, keep: &[u8]) -> u8 {
        let pinned = matches!(self.g.es[d as usize].0, Home::Pinned(_));
        match self.at[d as usize] {
            Some(f) if !self.live(d) && !pinned => {
                self.held[f as usize] = None;
                self.at[d as usize] = None;
                f
            }
            Some(f) => {
                let keep: Vec<u8> = keep.iter().copied().chain([f]).collect();
                let fresh = self.free(&keep);
                self.a.ext(Extmul, fresh, f, 0);
                fresh
            }
            None if pinned => {
                let Home::Pinned(f) = self.g.es[d as usize].0 else {
                    unreachable!()
                };
                let fresh = self.free(keep);
                self.a.ext(Extmul, fresh, f, 0);
                fresh
            }
            None => {
                let fresh = self.free(keep);
                let loc = self.home(d).expect("an element not in a register has a home");
                self.load(fresh, loc);
                fresh
            }
        }
    }

    /// The registers the operands already sit in, which loading another must not take.
    fn pins(&self, operands: &[Option<u32>]) -> Vec<u8> {
        (operands.iter().flatten())
            .filter_map(|&e| self.at[e as usize])
            .collect()
    }

    fn mul_add(&mut self, out: u32, a: u32, b: u32, d: Option<u32>) {
        let mut keep = self.pins(&[Some(a), Some(b), d]);
        let fa = self.register(a, &keep);
        keep.push(fa);
        let fb = self.register(b, &keep);
        keep.push(fb);
        let (f, op) = match d {
            Some(d) => (self.accumulator(d, &keep), Extmac),
            None => (self.free(&keep), Extmul),
        };
        self.a.ext(op, f, fa, fb);
        self.bind(f, out);
    }

    fn mul_k_add(&mut self, out: u32, a: u32, k: Loc, d: Option<u32>) {
        let mut keep = self.pins(&[Some(a), d]);
        let fa = self.register(a, &keep);
        keep.push(fa);
        let (f, op) = match d {
            Some(d) => (self.accumulator(d, &keep), Extmack),
            None => (self.free(&keep), Extmulk),
        };
        let t = reg::T[0];
        self.ld(t, k);
        self.a.ext(op, f, fa, t.index() as u8);
        self.bind(f, out);
    }

    fn assert_equal(&mut self, a: u32, b: u32) {
        let mut keep = self.pins(&[Some(a), Some(b)]);
        let fa = self.register(a, &keep);
        keep.push(fa);
        let fb = self.register(b, &keep);
        // The check leaves zero in its destination: an element not used again, else a copy.
        let pinned = |e: u32| matches!(self.g.es[e as usize].0, Home::Pinned(_));
        let (dead, other) = if !self.live(a) && !pinned(a) {
            (Some((a, fa)), fb)
        } else if !self.live(b) && !pinned(b) {
            (Some((b, fb)), fa)
        } else {
            (None, fb)
        };
        match dead {
            Some((e, f)) => {
                self.a.ext(Extmacz, f, other, 0);
                self.held[f as usize] = None;
                self.at[e as usize] = None;
            }
            None => {
                self.a.ext(Extmul, SCRATCH, fa, 0).ext(Extmacz, SCRATCH, other, 0);
            }
        }
    }

    /// Point a register at the message of a transcript step, and return it.
    ///
    /// The scalars are hashed where the advice has them: the program writes what the prover does not choose, their count,
    /// the tag, and the zeros of an absent first scalar.
    fn step_message(&mut self, block: Option<Loc>, count: usize, tag: u64) -> Reg {
        let (m, t) = (reg::P[0], reg::T[0]);
        let Some(block) = block else {
            let i = self.tags.iter().position(|&x| x == tag).expect("a tag's block");
            self.pointer(m, Loc::Block(block::TAGS + 8 * i));
            return m;
        };
        self.pointer(m, block);
        if count == 1 {
            for k in 0..3 {
                self.a.store(Sd, Reg::ZERO, 8 * k, m);
            }
        }
        self.a.li(t, count as u64).store(Sd, t, 24, m);
        self.a.li(t, tag).store(Sd, t, 56, m);
        m
    }

    /// A transcript step: its new state where its challenge is read, or back in the program's own block.
    fn step(&mut self, block: Option<Loc>, count: usize, tag: u64, challenge: Option<Loc>) {
        let m = self.step_message(block, count, tag);
        let to = match challenge {
            Some(loc) => {
                let to = if self.state == reg::STATE[1] {
                    reg::STATE[2]
                } else {
                    reg::STATE[1]
                };
                self.pointer(to, loc);
                to
            }
            None => reg::STATE[0],
        };
        self.a.blake2s(to, self.state, m, reg::BLOCK_BYTES, true);
        self.state = to;
    }

    /// A one-block hash of the eight words `message` gives, written where `to` points.
    fn node(&mut self, message: impl Fn(usize) -> Word, to: Reg) {
        self.copy(message, |k| Word::Block(reg::MESSAGE, 8 * k as i32), 8);
        self.a.blake2s(to, reg::IV, reg::MESSAGE, reg::BLOCK_BYTES, true);
    }

    fn grind(&mut self, block: Loc, bits: u32) {
        let t = reg::T[0];
        let nonce = block.add(ELEMENT);
        if bits == 0 {
            // No work: the nonce is zero.
            for k in 0..3 {
                self.ld(t, nonce.add(k));
                self.assert_eq(t, Reg::ZERO);
            }
        } else {
            // The base is a step that leaves the state where it is; the work is on the hash of the base and the nonce.
            let m = self.step_message(None, 0, POW_TAGS[0]);
            self.a.blake2s(reg::MESSAGE, self.state, m, reg::BLOCK_BYTES, true);
            self.copy(
                |k| Word::At(nonce.add(k)),
                |k| Word::Block(reg::MESSAGE, 32 + 8 * k as i32),
                3,
            );
            self.a.li(t, POW_TAGS[1]).store(Sd, t, 56, reg::MESSAGE);
            self.a
                .blake2s(reg::CHAINED, reg::IV, reg::MESSAGE, reg::BLOCK_BYTES, true);
            self.a.load(Ld, t, 0, reg::CHAINED).shift(Slli, t, t, 64 - bits);
            self.assert_eq(t, Reg::ZERO);
        }
        self.step(Some(block), 1, POW_TAGS[1], None);
    }

    fn clock(&mut self, e: u32) {
        let at = self.placed(e);
        let [t, u, one] = [reg::T[0], reg::T[1], reg::T[2]];
        // The high limbs are zero, the word's bits from the live one up are exactly the live bit, and its slot bits are zero.
        for k in 1..3 {
            self.ld(t, at.add(k));
            self.assert_eq(t, Reg::ZERO);
        }
        self.ld(t, at);
        self.a.shift(Srli, u, t, Clock::LIVE_BIT).i(Addi, one, Reg::ZERO, 1);
        self.assert_eq(u, one);
        self.a.i(Andi, u, t, Clock::CYCLE as i32 - 1);
        self.assert_eq(u, Reg::ZERO);
    }

    fn queries(&mut self, challenge: Loc, depth: usize, strata: &[Stratum], out: Loc) {
        let [t, u] = [reg::T[0], reg::T[1]];
        for (j, s) in strata.iter().enumerate() {
            let at = j * depth;
            let (limb, shift) = (at / 64, (at % 64) as u32);
            self.ld(t, challenge.add(limb));
            if shift > 0 {
                self.a.shift(Srli, t, t, shift);
            }
            if shift as usize + depth > 64 {
                self.ld(u, challenge.add(limb + 1));
                self.a.shift(Slli, u, u, 64 - shift).r(Or, t, t, u);
            }
            // The low bits are the challenge's, the top ones the stratum's index.
            let low = (depth - s.bits) as u32;
            if low == 0 {
                self.a.li(t, s.index as u64);
            } else {
                self.a.shift(Slli, t, t, 64 - low).shift(Srli, t, t, 64 - low);
                if s.index != 0 {
                    self.a.li(u, (s.index as u64) << low).r(Or, t, t, u);
                }
            }
            self.sd(t, out.add(j));
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn open_row(
        &mut self,
        pos: Loc,
        levels: usize,
        row_words: usize,
        leaf_words: usize,
        seed: Loc,
        leaf: Loc,
        packed: bool,
        path: Loc,
        out: Loc,
    ) {
        let position = reg::T[2];
        let [mut here, mut next, from] = reg::P;
        let prefix = leaf_words - row_words;
        let zero_blocks = prefix / 8;
        let n_blocks = leaf_words / 8;

        // The leaf: a chain from the state of its zero blocks, its last result written where the path starts.
        self.pointer(next, if levels > 0 { path } else { out });
        self.pointer(from, seed);
        if packed {
            // The words before the row are zero, whatever the advice holds.
            for k in 0..prefix - 8 * zero_blocks {
                self.sd(Reg::ZERO, leaf.add(k));
            }
            self.pointer(here, leaf);
        }
        let bytes = |index: usize| 64 * (index as u64 + 1);
        self.chained(zero_blocks..n_blocks, from, next, bytes, |l, index| {
            if !packed {
                l.fill(|k| (8 * index + k).checked_sub(prefix).map(|i| leaf.add(leaf_slot(i))));
                return reg::MESSAGE;
            }
            if index > zero_blocks {
                l.a.i(Addi, here, here, 64);
            }
            here
        });

        // The path: each level's block holds the node below it, then its sibling, in the order the position's bit
        // gives, and its hash is written into the next level's block.
        if levels > 0 {
            self.ld(position, pos);
        }
        for level in 0..levels {
            (here, next) = (next, here);
            if level + 1 == levels {
                self.pointer(next, out);
            } else {
                self.a.i(Addi, next, here, 64);
            }
            self.a.blake2s_node(next, reg::IV, here, position);
            if level + 1 < levels {
                self.a.shift(Srli, position, position, 1);
            }
        }
    }

    /// The message block of the program's own filled with eight words, a zero where `word` gives none.
    fn fill(&mut self, word: impl Fn(usize) -> Option<Loc>) {
        let t = reg::T[0];
        for k in 0..8 {
            let from = word(k).map_or(Reg::ZERO, |loc| {
                self.ld(t, loc);
                t
            });
            self.a.store(Sd, from, 8 * k as i32, reg::MESSAGE);
        }
    }

    /// A chain of compressions, one per block, from the state at `from` to the result at `to`, the last block final:
    /// block `j`'s message is where `message` points and its counter `bytes(j)`.
    fn chained(
        &mut self,
        blocks: Range<usize>,
        from: Reg,
        to: Reg,
        bytes: impl Fn(usize) -> u64,
        mut message: impl FnMut(&mut Self, usize) -> Reg,
    ) {
        let counter = reg::T[1];
        for index in blocks.clone() {
            let m = message(self, index);
            let last = index + 1 == blocks.end;
            self.a.li(counter, bytes(index)).blake2s(
                if last { to } else { reg::CHAINED },
                if index == blocks.start { from } else { reg::CHAINED },
                m,
                counter,
                last,
            );
        }
    }

    /// The hash of the words at `words`, into the digest at `out`: a chain from the parameter block's state.
    fn chain(&mut self, words: &[Loc], out: Loc) {
        let to = reg::P[0];
        let n_blocks = words.len().div_ceil(8).max(1);
        let length = 8 * words.len() as u64;
        self.pointer(to, out);
        let bytes = |j: usize| (64 * (j as u64 + 1)).min(length);
        self.chained(0..n_blocks, reg::IV, to, bytes, |l, j| {
            l.fill(|k| words.get(8 * j + k).copied());
            reg::MESSAGE
        });
    }

    fn op(&mut self, op: &Op) {
        match *op {
            Op::MulAdd { out, a, b, d } => self.mul_add(out, a, b, d),
            Op::MulKAdd { out, a, k, d } => {
                let k = self.g.k_loc(k);
                self.mul_k_add(out, a, k, d);
            }
            Op::AssertEq { a, b } => self.assert_equal(a, b),
            Op::Limbs { e, at } => {
                let f = self.register(e, &[]);
                self.store(f, at);
            }
            Op::Init { iv, output } => {
                self.state = reg::STATE[0];
                self.node(
                    |k| Word::At(if k < 4 { iv.add(k) } else { output.add(k - 4) }),
                    reg::STATE[0],
                );
            }
            Op::Step {
                block,
                count,
                tag,
                challenge,
            } => self.step(block, count, tag, challenge),
            Op::Grind { block, bits } => self.grind(block, bits),
            Op::Clock { e } => self.clock(e),
            Op::Queries {
                challenge,
                depth,
                ref strata,
                out,
            } => self.queries(challenge, depth, strata, out),
            Op::OpenRow {
                pos,
                levels,
                row_words,
                leaf_words,
                seed,
                leaf,
                packed,
                path,
                out,
            } => self.open_row(pos, levels, row_words, leaf_words, seed, leaf, packed, path, out),
            Op::Parent { left, right, out } => {
                let to = reg::P[0];
                self.pointer(to, out);
                self.node(|k| Word::At(if k < 4 { left.add(k) } else { right.add(k - 4) }), to);
            }
            Op::EqD { a, b } => {
                for k in 0..4 {
                    self.ld(reg::T[0], a.add(k));
                    self.ld(reg::T[1], b.add(k));
                    self.assert_eq(reg::T[0], reg::T[1]);
                }
            }
            Op::Root { lo, hi, out } => {
                for (half, loc) in [lo, hi].map(|e| self.placed(e)).into_iter().enumerate() {
                    self.copy(|k| Word::At(loc.add(k)), |k| Word::At(out.add(2 * half + k)), 2);
                    self.ld(reg::T[0], loc.add(2));
                    self.assert_eq(reg::T[0], Reg::ZERO);
                }
            }
            Op::InitState { state } => {
                self.state = reg::STATE[0];
                self.copy(
                    |k| Word::At(state.add(k)),
                    |k| Word::Block(reg::STATE[0], 8 * k as i32),
                    4,
                );
            }
            Op::State { out } => {
                let state = self.state;
                self.copy(
                    |k| Word::Block(state, 8 * k as i32),
                    |k| Word::At(if k < 3 { out[0].add(k) } else { out[1] }),
                    4,
                );
            }
            Op::Chain { ref words, out } => self.chain(words, out),
            Op::Exit { digest } => {
                // The output registers, then the exit: they are page registers until here.
                for k in 0..4 {
                    self.ld(reg::T[k], digest.add(k));
                }
                for (k, r) in Reg::OUTPUTS.into_iter().enumerate() {
                    self.a.i(Addi, r, reg::T[k], 0);
                }
                self.a.exit();
            }
        }
    }
}

/// A word of memory: at a location, or at an offset of a register holding a hash block's base.
#[derive(Clone, Copy)]
enum Word {
    At(Loc),
    Block(Reg, i32),
}

/// The elements an operation reads.
fn reads(op: &Op) -> impl Iterator<Item = u32> {
    let (x, y, z) = match *op {
        Op::MulAdd { a, b, d, .. } => (Some(a), Some(b), d),
        Op::MulKAdd { a, d, .. } => (Some(a), d, None),
        Op::AssertEq { a, b } => (Some(a), Some(b), None),
        Op::Limbs { e, .. } => (Some(e), None, None),
        _ => (None, None, None),
    };
    [x, y, z].into_iter().flatten()
}

/// Lower the recorded verifier to a program.
pub(super) fn lower(g: &Gen<'_>) -> Lowered {
    // A step that absorbs nothing hashes a block of its own, which holds its tag alone.
    let mut tags = Vec::new();
    for op in &g.ops {
        let tag = match *op {
            Op::Step { block: None, tag, .. } => tag,
            Op::Grind { bits, .. } if bits > 0 => POW_TAGS[0],
            _ => continue,
        };
        if !tags.contains(&tag) {
            tags.push(tag);
        }
    }
    // RAM: the constants, the hash blocks on a 64-byte boundary, then the scratch words.
    let blocks = g.consts.len().next_multiple_of(8);
    let scratch = blocks + block::TAGS + 8 * tags.len();
    let ram = Region::RAM.base();

    let mut uses = vec![VecDeque::new(); g.es.len()];
    for (i, op) in g.ops.iter().enumerate() {
        for e in reads(op) {
            uses[e as usize].push_back(i as u32);
        }
    }
    let mut l = Lower {
        g,
        a: Asm::new(),
        uses,
        at: vec![None; g.es.len()],
        held: [None; REGISTERS as usize],
        spilled: vec![None; g.es.len()],
        n_scratch: g.n_scratch,
        pages: [(u64::MAX, 0); reg::PAGES.len()],
        tick: 0,
        state: reg::STATE[0],
        tags,
        consts: ram,
        blocks: ram + 8 * blocks as u64,
        scratch: ram + 8 * scratch as u64,
    };
    let [state, message, iv, chained] =
        [block::STATE, block::MESSAGE, block::IV, block::CHAINED].map(|i| l.address(Loc::Block(i)));
    l.a.li(reg::STATE[0], state)
        .li(reg::MESSAGE, message)
        .li(reg::IV, iv)
        .li(reg::CHAINED, chained)
        .li(reg::BLOCK_BYTES, 64);
    // The image is empty: the program writes its constants itself, so two verifier programs differ by their text alone.
    for (k, word) in PARAM_IV.into_iter().enumerate() {
        l.a.li(reg::T[0], word).store(Sd, reg::T[0], 8 * k as i32, reg::IV);
    }
    for i in 0..l.tags.len() {
        let tag = l.tags[i];
        l.a.li(reg::T[0], tag);
        l.sd(reg::T[0], Loc::Block(block::TAGS + 8 * i + 7));
    }
    for (i, &word) in g.consts.iter().enumerate() {
        if word != 0 {
            l.a.li(reg::T[0], word);
            l.sd(reg::T[0], Loc::Const(i));
        }
    }
    for (i, op) in g.ops.iter().enumerate() {
        for e in reads(op) {
            let next = l.uses[e as usize].pop_front();
            debug_assert_eq!(next, Some(i as u32));
        }
        l.op(op);
    }
    debug_assert!(
        matches!(g.ops.last(), Some(Op::Exit { .. })),
        "a program ends on its output"
    );

    let log_ram = (scratch + l.n_scratch).next_power_of_two().trailing_zeros() as usize;
    Lowered {
        text: l.a.finish(),
        log_ram,
    }
}
