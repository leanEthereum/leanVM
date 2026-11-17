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
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(PartialEq))]
pub(crate) struct Xrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32, // frame base: address = fp + offset, operand = g^offset
    pub(crate) ra: u32,
    pub(crate) rb: u32,
    pub(crate) rc: u32,
    pub(crate) bytecode_read: u32,
}
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(PartialEq))]
pub(crate) struct Srow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r: u32,
    pub(crate) bytecode_read: u32,
}
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(PartialEq))]
pub(crate) struct Drow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r1: u32,
    pub(crate) r2: u32,
    pub(crate) r3: u32,
    pub(crate) bytecode_read: u32,
}
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(PartialEq))]
pub(crate) struct Jrow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) rc: u32,
    pub(crate) rd: u32,
    pub(crate) rf: u32,
    pub(crate) bytecode_read: u32,
}

/// `KECCAK` row: the per-cell memory access counts, in the order the table flushes
/// them (`tables::KeccakOp::cell`): the four `m` cells, the four `tail` cells, `b8`, the
/// four `cap` cells, then the thirteen output cells, zero for one the row does not write.
/// The input lanes are read back from the final memory image, the output lanes their permutation.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(PartialEq))]
pub(crate) struct Krow {
    pub(crate) pc: u32,
    pub(crate) fp: u32,
    pub(crate) r: [u32; crate::keccak::ROW_CELLS],
    pub(crate) bytecode_read: u32,
}

/// A row's place in the bus: its pc, how often that pc ran before it, and the access counts it read, in order.
pub(crate) trait Row: Copy + Send + Sync {
    fn pc(&self) -> u32;
    fn bytecode_read(&mut self) -> &mut u32;
    fn count(&mut self, i: usize) -> &mut u32;
}

macro_rules! row {
    ($t:ty, |$r:ident, $i:ident| $count:expr) => {
        impl Row for $t {
            fn pc(&self) -> u32 {
                self.pc
            }
            fn bytecode_read(&mut self) -> &mut u32 {
                &mut self.bytecode_read
            }
            fn count(&mut self, $i: usize) -> &mut u32 {
                let $r = self;
                $count
            }
        }
    };
}
row!(Xrow, |r, i| [&mut r.ra, &mut r.rb, &mut r.rc]
    .into_iter()
    .nth(i)
    .unwrap());
row!(Srow, |r, _i| &mut r.r);
row!(Drow, |r, i| [&mut r.r1, &mut r.r2, &mut r.r3]
    .into_iter()
    .nth(i)
    .unwrap());
row!(Jrow, |r, i| [&mut r.rc, &mut r.rd, &mut r.rf]
    .into_iter()
    .nth(i)
    .unwrap());
row!(Krow, |r, i| &mut r.r[i]);

/// An instruction table.
#[derive(Clone, Copy)]
pub(crate) enum Table {
    Xor,
    Mul,
    Set,
    Deref,
    Jump,
    Keccak,
}

/// Rows in fixed-size chunks, so the trace grows without ever moving what it holds:
/// a `Vec` would copy every row written so far each time it doubled.
#[cfg_attr(test, derive(PartialEq))]
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

    fn get_mut(&mut self, i: usize) -> &mut T {
        &mut self.chunks[i >> CHUNK_LOG][i & (CHUNK - 1)]
    }
}

impl<T: Row> Rows<T> {
    /// Append the rows `rows` picks from each part, in order and on the pool, each row's `bytecode_read` advanced by
    /// its part's offset at its pc.
    fn append(&mut self, parts: &[(&RowSet, &[u32])], rows: impl Fn(&RowSet) -> &Rows<T>) {
        // Each source chunk, its part's offsets, and the row it goes to.
        let mut tasks = Vec::new();
        let mut end = self.len;
        for &(part, offsets) in parts {
            for chunk in &rows(part).chunks {
                tasks.push((chunk, offsets, end));
                end += chunk.len();
            }
        }
        self.chunks
            .resize_with(end.div_ceil(CHUNK), || Vec::with_capacity(CHUNK));
        let dst: Vec<_> = self
            .chunks
            .iter_mut()
            .map(|c| parallel::SendPtr(c.as_mut_ptr()))
            .collect();
        parallel::for_each(tasks.len(), |t| {
            let (chunk, offsets, at) = tasks[t];
            for (i, row) in (at..).zip(chunk) {
                let mut row = *row;
                *row.bytecode_read() += offsets[row.pc() as usize];
                // SAFETY: row `i < end` lies in its chunk's capacity, and one task writes it.
                unsafe { dst[i >> CHUNK_LOG].add(i & (CHUNK - 1)).write(row) };
            }
        });
        for (c, chunk) in self.chunks.iter_mut().enumerate().skip(self.len >> CHUNK_LOG) {
            // SAFETY: every row of the chunk below `end` was written, above or before.
            unsafe { chunk.set_len((end - c * CHUNK).min(CHUNK)) };
        }
        self.len = end;
    }
}

/// The rows a walk emits, one [`Rows`] per instruction table.
pub(crate) struct RowSet {
    pub(crate) xor: Rows<Xrow>,
    pub(crate) mul: Rows<Xrow>,
    pub(crate) set: Rows<Srow>,
    pub(crate) deref: Rows<Drow>,
    pub(crate) jump: Rows<Jrow>,
    pub(crate) keccak: Rows<Krow>,
}

impl RowSet {
    pub(crate) fn new() -> Self {
        Self {
            xor: Rows::new(),
            mul: Rows::new(),
            set: Rows::new(),
            deref: Rows::new(),
            jump: Rows::new(),
            keccak: Rows::new(),
        }
    }

    /// Count `i` of row `row` of `table`.
    pub(crate) fn count(&mut self, table: Table, row: usize, i: usize) -> &mut u32 {
        match table {
            Table::Xor => self.xor.get_mut(row).count(i),
            Table::Mul => self.mul.get_mut(row).count(i),
            Table::Set => self.set.get_mut(row).count(i),
            Table::Deref => self.deref.get_mut(row).count(i),
            Table::Jump => self.jump.get_mut(row).count(i),
            Table::Keccak => self.keccak.get_mut(row).count(i),
        }
    }

    /// Append `parts` in order, on the pool, each row's `bytecode_read` advanced by its part's offset at its pc.
    pub(crate) fn append(&mut self, parts: &[(&RowSet, &[u32])]) {
        self.xor.append(parts, |p| &p.xor);
        self.mul.append(parts, |p| &p.mul);
        self.set.append(parts, |p| &p.set);
        self.deref.append(parts, |p| &p.deref);
        self.jump.append(parts, |p| &p.jump);
        self.keccak.append(parts, |p| &p.keccak);
    }
}

#[cfg_attr(test, derive(PartialEq))]
pub(crate) struct Trace {
    pub(crate) xor: Rows<Xrow>,
    pub(crate) mul: Rows<Xrow>,
    pub(crate) set: Rows<Srow>,
    pub(crate) deref: Rows<Drow>,
    pub(crate) jump: Rows<Jrow>,
    pub(crate) keccak: Rows<Krow>,
    pub(crate) bytecode_count: Vec<u32>, // per-pc execution count; the column holds g^{A[pc]}
    /// One past the highest access count, of a cell or a pc: the `g`-powers a fill looks up.
    pub(crate) counts: usize,
}

impl Trace {
    pub(crate) fn new(rows: RowSet, bytecode_count: Vec<u32>, counts: usize) -> Self {
        let RowSet {
            xor,
            mul,
            set,
            deref,
            jump,
            keccak,
        } = rows;
        Self {
            xor,
            mul,
            set,
            deref,
            jump,
            keccak,
            bytecode_count,
            counts,
        }
    }

    /// Rows per instruction table, in [`crate::cpu::Stats::TABLES`] order.
    pub(crate) fn row_counts(&self) -> [usize; crate::tables::N_TABLES] {
        [
            self.xor.len(),
            self.mul.len(),
            self.set.len(),
            self.deref.len(),
            self.jump.len(),
            self.keccak.len(),
        ]
    }
}
