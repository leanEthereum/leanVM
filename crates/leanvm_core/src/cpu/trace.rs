//! Per-opcode trace rows, emitted during execution and assembled into a [`Trace`].
//!
//! A row carries only what the witness fill cannot recover: the step's
//! `(pc, fp)`, the access counts read at access time, and `DEREF`'s resolved
//! store index. Everything else is a function of those:
//! operands and immediates come from `prog[pc]`, addresses from `fp` plus those
//! operands, and values from the final memory image, which is write-once and so
//! still holds what each accessed cell held at the time it was accessed. The
//! rows are the interpreter's largest write stream, so what they do not carry
//! they do not pay for, twice: once writing them and once reading them back.
//!
//! An access count is held as its exponent: the column holds `g^k`, the row `k`,
//! and the fill looks the power up.

/// `XOR` or `MUL` row: the three cells are `fp·g^{a,b,c}`.
pub(crate) struct Xrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
    pub(crate) ra: u32,
    pub(crate) rb: u32,
    pub(crate) rc: u32,
    pub(crate) bytecode_read: u32,
}
pub(crate) struct Srow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r: u32,
    pub(crate) bytecode_read: u32,
}
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r1: u32,
    pub(crate) r2: u32,
    pub(crate) r3: u32,
    pub(crate) bytecode_read: u32,
}
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) rc: u32,
    pub(crate) rd: u32,
    pub(crate) rf: u32,
    pub(crate) bytecode_read: u32,
}

/// `BLAKE2s` row: the nine per-cell memory access counts of the four
/// message-chunk cells, the chaining value's two cells, the output's two and the
/// metadata cell. The addresses are `fp·g^{ins[i]}`, `fp·g^{cv}`, `fp·g^{out}`,
/// `fp·g^{md}` and the successors of the middle two; the eighteen flock words are
/// those cells' lanes.
pub(crate) struct Brow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) ra: [u32; 2],  // per-cell counts for the two a input cells
    pub(crate) rb: [u32; 2],  // … the two b input cells
    pub(crate) rcv: [u32; 2], // … the two cv input cells
    pub(crate) rc: [u32; 2],  // … the two c output cells
    pub(crate) rmd: u32,      // … and the metadata cell
    pub(crate) bytecode_read: u32,
}

/// Rows in fixed-size chunks, so the trace grows without ever moving what it holds:
/// a `Vec` would copy every row written so far each time it doubled.
pub(crate) struct Rows<T> {
    chunks: Vec<Vec<T>>,
    len: usize,
}

const CHUNK_LOG: usize = 14;
const CHUNK: usize = 1 << CHUNK_LOG;

impl<T> Rows<T> {
    pub(crate) fn new() -> Self {
        Self {
            chunks: Vec::new(),
            len: 0,
        }
    }

    #[inline(always)]
    pub(crate) fn push(&mut self, row: T) {
        if self.len & (CHUNK - 1) == 0 {
            self.chunks.push(Vec::with_capacity(CHUNK));
        }
        // SAFETY: a chunk was pushed whenever the last one filled, so there is one.
        unsafe { self.chunks.last_mut().unwrap_unchecked() }.push(row);
        self.len += 1;
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub(crate) fn get(&self, i: usize) -> &T {
        &self.chunks[i >> CHUNK_LOG][i & (CHUNK - 1)]
    }

    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &T> {
        self.chunks.iter().flatten()
    }
}

pub(crate) struct Trace {
    pub(crate) xor: Rows<Xrow>,
    pub(crate) mul: Rows<Xrow>,
    pub(crate) set: Rows<Srow>,
    pub(crate) deref: Rows<Drow>,
    pub(crate) jump: Rows<Jrow>,
    pub(crate) blake2s: Rows<Brow>,
    pub(crate) bytecode_count: Vec<u32>, // per-pc execution count; the column holds g^{A[pc]}
    /// One past the highest access count, of a cell or a pc: the `g`-powers a fill looks up.
    pub(crate) counts: usize,
}

impl Trace {
    /// Rows per instruction table, in [`crate::cpu::Stats::TABLES`] order.
    pub(crate) fn row_counts(&self) -> [usize; crate::tables::N_TABLES] {
        [
            self.xor.len(),
            self.mul.len(),
            self.set.len(),
            self.deref.len(),
            self.jump.len(),
            self.blake2s.len(),
        ]
    }
}
