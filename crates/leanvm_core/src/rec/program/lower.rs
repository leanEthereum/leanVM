//! The recorded verifier lowered to RISC-V: extension registers allocated, hashes laid on their blocks, every address fixed.
//!
//! An element lives in an extension register while it is used, and nowhere else unless it came from memory.
//!
//! No instruction moves a register to memory, so an element evicted while still needed is hinted: the advice holds its
//! limbs, the program checks them against the register before giving it up, and reloads them when it needs them.

use super::record::{CHAIN_IV, Gen, Home, Loc, Op, POW_TAGS};
use crate::rv::Region;
use crate::rv::asm::*;
use crate::tables::Clock;
use std::collections::VecDeque;

/// The lowered program: its text, its image, and where the hints of evicted elements go in the advice.
pub(super) struct Lowered {
    /// The instructions.
    pub(super) text: Vec<u32>,
    /// RAM's first words.
    pub(super) image: Vec<u64>,
    /// The base-two logarithm of RAM's words.
    pub(super) log_ram: usize,
    /// The elements hinted after the recorded advice, in order, three words each.
    pub(super) spills: Vec<u32>,
}

/// Integer registers the program keeps for one purpose.
mod reg {
    use crate::rv::Reg;

    /// Scratch.
    pub(super) const T: [Reg; 6] = [Reg::T0, Reg::T1, Reg::T2, Reg::T3, Reg::T4, Reg::T5];
    /// The transcript's block, and the same 32 bytes on.
    pub(super) const TRANSCRIPT: [Reg; 2] = [Reg::S0, Reg::S1];
    /// The leaf chain's block, and the same 32 bytes on.
    pub(super) const LEAF: [Reg; 2] = [Reg::S2, Reg::S3];
    /// The one-block hashes' block, whose chaining value is the parameter block's.
    pub(super) const NODE: Reg = Reg::S4;
    /// The constant 64, a one-block hash's counter.
    pub(super) const BLOCK_BYTES: Reg = Reg::S5;
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
/// The scratch extension register: where a hint is loaded to be checked.
const SCRATCH: u8 = 3;
/// How many extension registers there are.
const REGISTERS: u8 = 128;

/// A hash block's words: the chaining value, the result, then the message.
const MESSAGE: i32 = 64;
const RESULT: i32 = 32;

struct Lower<'g> {
    g: &'g Gen<'g>,
    a: Asm,
    /// Each element's uses still to come, as operation indices.
    uses: Vec<VecDeque<u32>>,
    /// The register holding each element, if one does.
    at: Vec<Option<u8>>,
    /// The element each register holds.
    held: [Option<u32>; REGISTERS as usize],
    /// Where each evicted element's hint is.
    spilled: Vec<Option<Loc>>,
    spills: Vec<u32>,
    /// The page each page register holds, and when it was last used.
    pages: [(u64, u64); reg::PAGES.len()],
    tick: u64,
    /// Which half of the transcript's block holds its state.
    phase: usize,
    consts: u64,
    scratch: u64,
}

impl Lower<'_> {
    /// The byte address of a location.
    const fn address(&self, loc: Loc) -> u64 {
        match loc {
            Loc::Const(i) => self.consts + 8 * i as u64,
            Loc::Advice(i) => Region::ADVICE.base() + 8 * i as u64,
            Loc::Scratch(i) => self.scratch + 8 * i as u64,
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

    /// Load the element at `loc` into register `f`: `1 * l_0 + y * l_1 + y^2 * l_2`.
    fn load(&mut self, f: u8, loc: Loc) {
        // A constant's zero limbs need no instruction.
        let known = match loc {
            Loc::Const(i) => Some([self.g.consts[i], self.g.consts[i + 1], self.g.consts[i + 2]]),
            _ => None,
        };
        let t = reg::T[0];
        let mut op = Extmulk;
        for k in 0..3 {
            if known.is_some_and(|limbs| limbs[k] == 0) {
                continue;
            }
            self.ld(t, loc.add(k));
            self.a.ext(op, f, k as u8, t.index() as u8);
            op = Extmack;
        }
        if op == Extmulk {
            self.a.ext(Extmulk, f, 0, Reg::ZERO.index() as u8);
        }
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

    /// Give up the register of an element: hint it first if it is still needed and has no home.
    fn release(&mut self, f: u8) {
        let Some(e) = self.held[f as usize].take() else { return };
        self.at[e as usize] = None;
        if self.live(e) && self.home(e).is_none() {
            let loc = Loc::Advice(self.g.advice.len() + 3 * self.spills.len());
            self.spills.push(e);
            self.spilled[e as usize] = Some(loc);
            self.load(SCRATCH, loc);
            self.a.ext(Extmacz, SCRATCH, f, 0);
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

    /// The message word `k` of the transcript's block, whose state is in half `phase`.
    const fn transcript_word(&self, k: usize) -> Word {
        Word::Block(reg::TRANSCRIPT[0], MESSAGE + 8 * (k ^ (4 * self.phase)) as i32)
    }

    /// One transcript step from the state in half `phase`: its message, then the compression, the result in the other half.
    fn step_block(&mut self, first: Option<Loc>, last: Option<Loc>, tag: u64) {
        let t = reg::T[0];
        for (slot, scalar) in [first, last].into_iter().enumerate() {
            for k in 0..3 {
                let Word::Block(base, offset) = self.transcript_word(4 * slot + k) else {
                    unreachable!()
                };
                match scalar {
                    Some(loc) => {
                        self.ld(t, loc.add(k));
                        self.a.store(Sd, t, offset, base);
                    }
                    None => {
                        self.a.store(Sd, Reg::ZERO, offset, base);
                    }
                }
            }
        }
        let count = u64::from(first.is_some()) + u64::from(last.is_some());
        for (k, value) in [(3, count), (7, tag)] {
            let Word::Block(base, offset) = self.transcript_word(k) else {
                unreachable!()
            };
            self.a.li(t, value).store(Sd, t, offset, base);
        }
        self.a.blake2s(reg::TRANSCRIPT[self.phase], reg::BLOCK_BYTES, true);
    }

    /// The word `k` of the half of the transcript's block that is not the state's: a step's result.
    const fn transcript_result(&self, k: usize) -> Word {
        Word::Block(reg::TRANSCRIPT[0], 32 * (1 - self.phase) as i32 + 8 * k as i32)
    }

    fn step(&mut self, first: Option<Loc>, last: Option<Loc>, tag: u64, challenge: Option<Loc>) {
        self.step_block(first, last, tag);
        self.phase ^= 1;
        if let Some(to) = challenge {
            let phase = self.phase;
            self.copy(
                |k| Word::Block(reg::TRANSCRIPT[0], 32 * phase as i32 + 8 * k as i32),
                |k| Word::At(to.add(k)),
                3,
            );
        }
    }

    /// A one-block hash of the eight words `message` gives: the block's chaining value is the parameter block's.
    fn node(&mut self, message: impl Fn(usize) -> Word) {
        self.copy(message, |k| Word::Block(reg::NODE, MESSAGE + 8 * k as i32), 8);
        self.a.blake2s(reg::NODE, reg::BLOCK_BYTES, true);
    }

    fn grind(&mut self, nonce: Loc, bits: u32) {
        let t = reg::T[0];
        if bits == 0 {
            // No work: the nonce is zero.
            for k in 0..3 {
                self.ld(t, nonce.add(k));
                self.assert_eq(t, Reg::ZERO);
            }
        } else {
            // The base is a step that leaves the state where it is; the work is on the hash of the base and the nonce.
            self.step_block(None, None, POW_TAGS[0]);
            let base = |s: &Self, k: usize| s.transcript_result(k);
            let words: Vec<Word> = (0..4)
                .map(|k| base(self, k))
                .chain((0..3).map(|k| Word::At(nonce.add(k))))
                .collect();
            self.copy(|k| words[k], |k| Word::Block(reg::NODE, MESSAGE + 8 * k as i32), 7);
            self.a.li(t, POW_TAGS[1]).store(Sd, t, MESSAGE + 56, reg::NODE);
            self.a.blake2s(reg::NODE, reg::BLOCK_BYTES, true);
            self.a.load(Ld, t, RESULT, reg::NODE).shift(Slli, t, t, 64 - bits);
            self.assert_eq(t, Reg::ZERO);
        }
        self.step(None, Some(nonce), POW_TAGS[1], None);
    }

    fn clock(&mut self, at: Loc) {
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

    fn queries(&mut self, challenge: Loc, depth: usize, strata: &[::pcs::whir::Stratum], out: Loc) {
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
        path: Loc,
        out: Loc,
    ) {
        let [t, counter, bit, here, there, position] = reg::T;
        let prefix = leaf_words - row_words;
        let zero_blocks = prefix / 8;
        let n_blocks = leaf_words / 8;

        // The leaf: a chain from the state of its zero blocks, each block's result the next one's chaining value.
        self.copy(
            |k| Word::At(seed.add(k)),
            |k| Word::Block(reg::LEAF[0], 8 * k as i32),
            4,
        );
        let mut phase = 0;
        for index in zero_blocks..n_blocks {
            for k in 0..8 {
                let offset = MESSAGE + 8 * (k ^ (4 * phase)) as i32;
                let word = 8 * index + k;
                if word < prefix {
                    self.a.store(Sd, Reg::ZERO, offset, reg::LEAF[0]);
                } else {
                    self.ld(t, leaf.add(word - prefix));
                    self.a.store(Sd, t, offset, reg::LEAF[0]);
                }
            }
            self.a.li(counter, 64 * (index as u64 + 1));
            self.a.blake2s(reg::LEAF[phase], counter, index + 1 == n_blocks);
            phase ^= 1;
        }

        // The path: at each level the node goes left or right of its sibling by the position's bit.
        let mut node = Word::Block(reg::LEAF[0], 32 * phase as i32);
        if levels > 0 {
            self.ld(position, pos);
        }
        for level in 0..levels {
            self.a
                .i(Andi, bit, position, 1)
                .shift(Slli, bit, bit, 5)
                .shift(Srli, position, position, 1)
                .r(Add, here, reg::NODE, bit)
                .r(Sub, there, reg::NODE, bit);
            let from = node;
            self.copy(|k| from.add(k), |k| Word::Block(here, MESSAGE + 8 * k as i32), 4);
            self.copy(
                |k| Word::At(path.add(4 * level + k)),
                |k| Word::Block(there, MESSAGE + 32 + 8 * k as i32),
                4,
            );
            self.a.blake2s(reg::NODE, reg::BLOCK_BYTES, true);
            node = Word::Block(reg::NODE, RESULT);
        }
        self.copy(|k| node.add(k), |k| Word::At(out.add(k)), 4);
    }

    fn commit(&mut self, words: &[Loc]) {
        let [t, counter, ..] = reg::T;
        for (k, word) in CHAIN_IV.into_iter().enumerate() {
            self.a.li(t, word).store(Sd, t, 8 * k as i32, reg::LEAF[0]);
        }
        let n_blocks = words.len().div_ceil(8).max(1);
        let bytes = 8 * words.len() as u64;
        let mut phase = 0;
        for j in 0..n_blocks {
            for k in 0..8 {
                let offset = MESSAGE + 8 * (k ^ (4 * phase)) as i32;
                match words.get(8 * j + k) {
                    Some(&loc) => {
                        self.ld(t, loc);
                        self.a.store(Sd, t, offset, reg::LEAF[0]);
                    }
                    None => {
                        self.a.store(Sd, Reg::ZERO, offset, reg::LEAF[0]);
                    }
                }
            }
            self.a.li(counter, (64 * (j as u64 + 1)).min(bytes));
            self.a.blake2s(reg::LEAF[phase], counter, j + 1 == n_blocks);
            phase ^= 1;
        }
        // The output registers, then the exit: they are page registers until here.
        for (k, r) in Reg::OUTPUTS.into_iter().enumerate() {
            self.a.load(Ld, r, 32 * phase as i32 + 8 * k as i32, reg::LEAF[0]);
        }
        self.a.exit();
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
                self.load(SCRATCH, at);
                self.a.ext(Extmacz, SCRATCH, f, 0);
            }
            Op::Init { iv, output } => {
                self.phase = 0;
                self.node(|k| Word::At(if k < 4 { iv.add(k) } else { output.add(k - 4) }));
                self.copy(
                    |k| Word::Block(reg::NODE, RESULT + 8 * k as i32),
                    |k| Word::Block(reg::TRANSCRIPT[0], 8 * k as i32),
                    4,
                );
            }
            Op::Step {
                first,
                last,
                tag,
                challenge,
            } => self.step(first, last, tag, challenge),
            Op::Grind { nonce, bits } => self.grind(nonce, bits),
            Op::Clock { at } => self.clock(at),
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
                path,
                out,
            } => self.open_row(pos, levels, row_words, leaf_words, seed, leaf, path, out),
            Op::Parent { left, right, out } => {
                self.node(|k| Word::At(if k < 4 { left.add(k) } else { right.add(k - 4) }));
                self.copy(
                    |k| Word::Block(reg::NODE, RESULT + 8 * k as i32),
                    |k| Word::At(out.add(k)),
                    4,
                );
            }
            Op::EqD { a, b } => {
                for k in 0..4 {
                    self.ld(reg::T[0], a.add(k));
                    self.ld(reg::T[1], b.add(k));
                    self.assert_eq(reg::T[0], reg::T[1]);
                }
            }
            Op::Root { lo, hi, out } => {
                for (half, loc) in [lo, hi].into_iter().enumerate() {
                    self.copy(|k| Word::At(loc.add(k)), |k| Word::At(out.add(2 * half + k)), 2);
                    self.ld(reg::T[0], loc.add(2));
                    self.assert_eq(reg::T[0], Reg::ZERO);
                }
            }
            Op::Commit { ref words } => self.commit(words),
        }
    }
}

/// A word of memory: at a location, or at an offset of a register holding a hash block's base.
#[derive(Clone, Copy)]
enum Word {
    At(Loc),
    Block(Reg, i32),
}

impl Word {
    const fn add(self, k: usize) -> Self {
        match self {
            Self::At(loc) => Self::At(loc.add(k)),
            Self::Block(base, offset) => Self::Block(base, offset + 8 * k as i32),
        }
    }
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
    // RAM: the constants, the three hash blocks on 128-byte boundaries, then the scratch words.
    let blocks = g.consts.len().next_multiple_of(16);
    let scratch = blocks + 3 * 16;
    let words = scratch + g.n_scratch;
    let log_ram = words.next_power_of_two().trailing_zeros() as usize;
    let ram = Region::RAM.base();
    let block = |i: usize| ram + 8 * (blocks + 16 * i) as u64;

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
        spills: Vec::new(),
        pages: [(u64::MAX, 0); reg::PAGES.len()],
        tick: 0,
        phase: 0,
        consts: ram,
        scratch: ram + 8 * scratch as u64,
    };
    l.a.li(reg::TRANSCRIPT[0], block(0))
        .li(reg::TRANSCRIPT[1], block(0) + 32)
        .li(reg::LEAF[0], block(1))
        .li(reg::LEAF[1], block(1) + 32)
        .li(reg::NODE, block(2))
        .li(reg::BLOCK_BYTES, 64);
    for (i, op) in g.ops.iter().enumerate() {
        for e in reads(op) {
            let next = l.uses[e as usize].pop_front();
            debug_assert_eq!(next, Some(i as u32));
        }
        l.op(op);
    }
    debug_assert!(
        matches!(g.ops.last(), Some(Op::Commit { .. })),
        "a program ends on its output"
    );

    let mut image = g.consts.clone();
    image.resize(blocks + 2 * 16, 0);
    image.extend(CHAIN_IV);
    Lowered {
        text: l.a.finish(),
        image,
        log_ram,
        spills: l.spills,
    }
}
