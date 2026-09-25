//! Bridge to flock for the instruction classes: each class's circuit
//! ([`crate::rv::circuits`]), proven over one packed witness of its own.
//!
//! That witness is one more committed column of the stacked witness: instance `j` of
//! the batch is row `j` of the class's table, and flock's R1CS validity is discharged
//! by the same stacked WHIR opening, through one ring-switched region per class.
//!
//! A register or bytecode word is 64 bits and the packing is 64 bits a word, so the
//! words a row puts on the bus ARE packed words of its instance, the circuit's ports
//! ([`ClassSpec::ports`]). The table's columns for them are therefore virtual, their
//! claims routed to those words.

use crate::cpu::Row;
use crate::rv::Entry;
use crate::tables::{ClassSpec, N_TABLES, Word};
use crate::transcript::{ProverState, VerifierState};
use ::pcs::pack::LOG_PACKING;
use flock::circuit::Circuit;
use flock::reduction::{ReductionReplay, SliceClaim};
use flock::verifier::VerifyError;
use primitives::field::F64;
use std::sync::OnceLock;
use zk_alloc::ArenaVec;

/// The zerocheck's cube has at least this many variables (flock's univariate skip
/// plus its fixed-point dimensions), which floors the batch of a small circuit.
pub const MIN_CUBE_LOG: usize = 13;

/// `log2` of an instance's packed words: the stride between consecutive instances'
/// same-port words.
pub const fn stride_log(spec: &ClassSpec) -> usize {
    spec.k_log - LOG_PACKING
}

/// Table `t`'s gate list, built once.
pub fn circuit(t: usize) -> &'static Circuit {
    static CIRCUITS: [OnceLock<Circuit>; N_TABLES] = [const { OnceLock::new() }; N_TABLES];
    CIRCUITS[t].get_or_init(|| {
        let spec = crate::tables::CLASSES[t];
        let circuit = (spec.circuit)();
        assert_eq!(circuit.k_log(), spec.k_log, "{}'s block size moved", spec.name);
        assert_eq!(
            circuit.n_input_words(),
            spec.n_inputs,
            "{}'s input ports moved",
            spec.name
        );
        circuit
    })
}

/// `log2` of the batch proving `n_rows` instances: a power of two, at least flock's
/// stripe floor and at least what the zerocheck's cube needs.
pub const fn n_blocks_log(spec: &ClassSpec, n_rows: usize) -> usize {
    let n = if n_rows > 8 { n_rows } else { 8 };
    let natural = n.next_power_of_two().trailing_zeros() as usize;
    let floor = MIN_CUBE_LOG.saturating_sub(spec.k_log);
    if natural > floor { natural } else { floor }
}

/// A row's value of one circuit word.
fn word_of(word: Word, row: &Row, entry: &Entry) -> u64 {
    match word {
        Word::Flags => entry.flags,
        Word::Imm => entry.imm,
        Word::V1 => row.v1,
        Word::V2 => row.v2,
        Word::Out => row.out,
        Word::Taken => row.taken as u64,
        Word::Address => row.ram.address,
        Word::Cell(k) => row.hash.as_ref().map_or(row.ram.old, |h| h.block[k as usize]),
        Word::CellNew(k) => row.hash.as_ref().map_or(row.ram.new, |h| h.word_after(k as usize)),
        Word::Bad => 0,
        Word::HintQ => crate::rv::semantics::div_hints(row.v1, row.v2, entry.flags).0,
        Word::HintR => crate::rv::semantics::div_hints(row.v1, row.v2, entry.flags).1,
    }
}

/// The flock-native tables of one class's batch, kept from the pass that wrote its
/// committed column so the reduction needs no second witness pass.
pub(crate) struct Prepared {
    table: usize,
    n_blocks_log: usize,
    z: ArenaVec<u64>,
    a: ArenaVec<u64>,
    b: ArenaVec<u64>,
    z_lincheck: ArenaVec<u8>,
}

impl Prepared {
    /// Build table `t`'s batch, one instance per row, and write its packed witness
    /// into `window`, the class's committed column.
    pub(crate) fn build(t: usize, rows: &[Row], entries: &[Entry], window: &mut [F64]) -> Self {
        let spec = crate::tables::CLASSES[t];
        let n_blocks_log = n_blocks_log(spec, rows.len());
        assert_eq!(
            rows.len(),
            1 << n_blocks_log,
            "a table's rows fill its batch (cpu::filler)"
        );
        let circuit = circuit(t);
        let (z, a, b, z_lincheck) = circuit.generate_witness_by(rows, &rows[0], n_blocks_log, |row, words| {
            for (word, &port) in words.iter_mut().zip(spec.ports) {
                *word = word_of(port, row, &entries[row.index as usize]);
            }
        });
        assert_eq!(window.len(), z.len(), "the committed column is the wrong size");
        let stride = 1 << stride_log(spec);
        // `F64` is `repr(transparent)` over `u64`, and the packing is bit `i` at
        // position `i` on both sides.
        const BATCH: usize = 1 << 10;
        parallel::chunks_mut_zip(window, &z, stride * BATCH, |batch, dst, src| {
            for (j, src) in src.chunks_exact(stride).enumerate() {
                // What the circuit computed is what the interpreter did, or the bus
                // would carry one and flock prove the other.
                let row = &rows[batch * BATCH + j];
                for (k, &port) in spec.ports.iter().enumerate().skip(spec.n_inputs) {
                    let expected = word_of(port, row, &entries[row.index as usize]);
                    assert_eq!(
                        src[k], expected,
                        "{}'s circuit disagrees with the interpreter on {port:?}",
                        spec.name
                    );
                }
            }
            for (d, &s) in dst.iter_mut().zip(src) {
                *d = F64(s);
            }
        });
        Self {
            table: t,
            n_blocks_log,
            z,
            a,
            b,
            z_lincheck,
        }
    }

    /// Flock's zerocheck then lincheck, leaving the one claim on the committed column.
    pub(crate) fn prove(&self, ps: &mut ProverState) -> SliceClaim {
        let block = circuit(self.table).block();
        let stage = block.prove_zerocheck(self.n_blocks_log, &self.z, &self.a, &self.b, ps);
        block.prove_lincheck(self.n_blocks_log, stage, &self.z_lincheck, ps)
    }
}

/// The verifier's replay of table `t`'s reduction: zerocheck, then lincheck.
pub fn verify_reduction(t: usize, n_blocks_log: usize, vs: &mut VerifierState) -> Result<ReductionReplay, VerifyError> {
    circuit(t).block().verify(n_blocks_log, vs)
}
