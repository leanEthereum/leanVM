//! The trace: one [`Row`] per executed instruction, emitted during execution and
//! grouped by table, plus what the run leaves behind for the finalize blocks.
//!
//! A row carries what its accesses saw, its clock, and per access the timestamp its
//! cell was last accessed at, which the memory argument needs. Everything else comes
//! back from the program's entry at `index`.

use std::sync::{Mutex, MutexGuard, PoisonError};

use primitives::field::F64;

/// What a hash row adds to a row.
///
/// - The block's words as found, and the four the compression writes.
/// - The previous timestamp of every access, the registers' first.
pub(crate) struct HashRow {
    pub(crate) block: [u64; crate::rv::Hash::WORDS],
    pub(crate) out: [u64; 4],
    pub(crate) prev: [u64; 2 + crate::rv::Hash::WORDS],
}

impl HashRow {
    /// Word `k` of the block after the row.
    pub(crate) const fn word_after(&self, k: usize) -> u64 {
        match k.wrapping_sub(crate::rv::Hash::OUT as usize / 8) {
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
    pub(crate) ram: crate::rv::WordAccess,
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
    /// Per table, in [`crate::tables::CLASSES`] order. The backing storage is reused
    /// across runs ([`RowBufs`]).
    pub(crate) rows: RowBufs,
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
    /// The clock the run ended on: the final state's timestamp.
    pub(crate) ts_final: u64,
}

impl Trace {
    /// Rows per instruction table.
    pub(crate) fn row_counts(&self) -> [usize; crate::tables::N_TABLES] {
        std::array::from_fn(|t| self.rows[t].len())
    }
}

/// One set of per-table row buffers, checked out for a run and returned when it ends.
///
/// The interpreter grows each table's `Vec` by doubling, on one thread, which copies
/// every row it already holds. A process-wide pool keeps a single cleared set, so the
/// next run pushes into storage that already has capacity and whose pages are already
/// faulted in. A run that overlaps another allocates its own; of the two sets, the one
/// with more slots is the one kept.
pub(crate) struct RowBufs {
    rows: [Vec<Row>; crate::tables::N_TABLES],
}

static POOL: Mutex<Option<[Vec<Row>; crate::tables::N_TABLES]>> = Mutex::new(None);

fn lock() -> MutexGuard<'static, Option<[Vec<Row>; crate::tables::N_TABLES]>> {
    // A panic while holding the pool must not retire it: the buffers are still there.
    POOL.lock().unwrap_or_else(PoisonError::into_inner)
}

fn slots(rows: &[Vec<Row>; crate::tables::N_TABLES]) -> usize {
    rows.iter().map(Vec::capacity).sum()
}

impl RowBufs {
    /// A cleared set from the pool, or fresh empty buffers when the pool is empty.
    pub(crate) fn checkout() -> Self {
        let mut rows = lock().take().unwrap_or_else(|| std::array::from_fn(|_| Vec::new()));
        for table in &mut rows {
            table.clear();
        }
        Self { rows }
    }
}

impl Drop for RowBufs {
    fn drop(&mut self) {
        let mut rows = std::mem::take(&mut self.rows);
        for table in &mut rows {
            table.clear();
        }
        let incoming = slots(&rows);
        if incoming == 0 {
            return;
        }
        // Drop the loser after releasing the lock: freeing a set is the slow part.
        let _loser = {
            let mut pool = lock();
            if pool.as_ref().is_none_or(|resident| slots(resident) < incoming) {
                pool.replace(rows)
            } else {
                None
            }
        };
    }
}

impl std::ops::Deref for RowBufs {
    type Target = [Vec<Row>; crate::tables::N_TABLES];

    fn deref(&self) -> &Self::Target {
        &self.rows
    }
}

impl std::ops::DerefMut for RowBufs {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.rows
    }
}
