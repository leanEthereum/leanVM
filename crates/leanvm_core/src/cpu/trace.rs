//! The trace: one [`Row`] per executed instruction, emitted during execution and
//! grouped by table, plus what the run leaves behind for the finalize blocks.
//!
//! A row carries what its accesses saw, its clock, and per access the timestamp its
//! cell was last accessed at, which the memory argument needs. Everything else comes
//! back from the program's entry at `index`.

use primitives::field::F64;

/// What a hash row adds to a row.
///
/// - The block's words as found, and the four the compression writes.
/// - The previous timestamp of every access, the registers' first.
pub(crate) struct HashRow {
    pub(crate) block: [u64; crate::rv::hash::WORDS],
    pub(crate) out: [u64; 4],
    pub(crate) prev: [u64; 2 + crate::rv::hash::WORDS],
}

impl HashRow {
    /// Word `k` of the block after the row.
    pub(crate) fn word_after(&self, k: usize) -> u64 {
        match k.wrapping_sub(crate::rv::hash::OUT as usize / 8) {
            j if j < 4 => self.out[j],
            _ => self.block[k],
        }
    }
}

pub(crate) struct Row {
    /// The entry executed.
    pub(crate) index: u32,
    /// The row's clock, zero on a padding row.
    pub(crate) ts: u64,
    pub(crate) v1: u64,
    pub(crate) v2: u64,
    /// What the class computed.
    pub(crate) out: u64,
    pub(crate) taken: bool,
    /// What the destination register held before the write, if the class makes one.
    pub(crate) vd_old: u64,
    /// The RAM cell a load or a store accessed: its bus address, what it held and
    /// what it holds. Zeros for another class.
    pub(crate) ram: crate::rv::machine::RamAccess,
    /// The timestamps the register accesses the class makes, then its RAM access, pull.
    /// A hash row keeps them in `hash` instead.
    pub(crate) prev: [u64; 4],
    pub(crate) hash: Option<Box<HashRow>>,
}

impl Row {
    /// The previous timestamps of the row's accesses in column order, at least as many as its class makes.
    pub(crate) fn prev(&self) -> &[u64] {
        match &self.hash {
            Some(hash) => &hash.prev,
            None => &self.prev,
        }
    }
}

pub(crate) struct Trace {
    /// Per table, in [`crate::tables::CLASSES`] order.
    pub(crate) rows: [Vec<Row>; crate::tables::N_TABLES],
    /// The registers after the run, and each one's last timestamp, the seed's if
    /// never touched.
    pub(crate) reg_fin: Vec<F64>,
    pub(crate) reg_ts: Vec<F64>,
    /// The same for RAM, and for the advice, whose initial words are committed too.
    pub(crate) ram_fin: Vec<F64>,
    pub(crate) ram_ts: Vec<F64>,
    pub(crate) adv_init: Vec<F64>,
    pub(crate) adv_fin: Vec<F64>,
    pub(crate) adv_ts: Vec<F64>,
    /// How many rows read each bytecode entry, as an integer.
    pub(crate) bytecode_reads: Vec<F64>,
    /// The clock the run ended on: the final state's timestamp.
    pub(crate) ts_final: u64,
}

impl Trace {
    /// Rows per instruction table.
    pub(crate) fn row_counts(&self) -> [usize; crate::tables::N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len())
    }

    /// How many of `rows` read each of the program's `n_entries` bytecode entries.
    pub(crate) fn read_counts(rows: &[Vec<Row>; crate::tables::N_TABLES], n_entries: usize) -> Vec<F64> {
        let mut counts = vec![F64::ZERO; n_entries];
        for row in rows.iter().flatten() {
            counts[row.index as usize].0 += 1;
        }
        counts
    }
}
