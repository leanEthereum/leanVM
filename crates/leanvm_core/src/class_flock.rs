//! Bridge to flock for the instruction tables.
//!
//! Each class's circuit and each table's clock circuit is proven over one packed witness of its own. The
//! extension-field product has no class circuit, so its table has its clock circuit's alone.
//!
//! That witness is one more committed column of the stacked witness: instance `j` of
//! the batch is row `j` of the circuit's table, and flock's R1CS validity is discharged
//! by the same stacked WHIR opening, through one ring-switched region per circuit.
//!
//! A register or bytecode word is 64 bits and the packing is 64 bits a word, so the
//! words a row puts on the bus ARE packed words of its instance, the circuit's ports
//! ([`ClassSpec::ports`]). The table's columns for them are therefore virtual, their
//! claims routed to those words.

use crate::cpu::{Payloads, RowRef, Trace};
use crate::rv::Entry;
use crate::tables::{ClassSpec, ClassTable, N_CIRCUITS, N_TABLES, Part};
use ::pcs::pack::LOG_PACKING;
use fiat_shamir::transcript::{ProverState, VerifierState};
use flock::circuit::Circuit;
use flock::lincheck::MatrixClaim;
use flock::reduction::{ReductionReplay, Shape, SliceClaim};
use flock::verifier::FlockError;
use primitives::field::F64;
use std::sync::OnceLock;

/// The zerocheck's cube has at least this many variables (flock's univariate skip
/// plus its fixed-point dimensions), which floors the batch of a small circuit.
pub const MIN_CUBE_LOG: usize = flock::zerocheck::MIN_LOG_N;

/// The most input ports a circuit with a word-level witness has: the hash's fourteen.
const MAX_INPUT_WORDS: usize = 14;

/// The packed witnesses: every class circuit in table order (the tables that have one come first), then every
/// table's clock circuit.
pub const N_FLOCKS: usize = N_CIRCUITS + N_TABLES;

/// The table and the circuit of packed witness `f`.
pub const fn flock(f: usize) -> (usize, Part) {
    if f < N_CIRCUITS {
        (f, Part::Class)
    } else {
        (f - N_CIRCUITS, Part::Clock)
    }
}

/// The packed witness of table `t`'s circuit `part`.
///
/// # Panics
///
/// Panics for the class circuit of a table that has none.
pub const fn flock_index(t: usize, part: Part) -> usize {
    match part {
        Part::Class => {
            assert!(t < N_CIRCUITS, "the table has no class circuit");
            t
        }
        Part::Clock => N_CIRCUITS + t,
    }
}

/// `log2` of the bits one instance of a table's circuit occupies.
pub const fn k_log(spec: &ClassSpec, part: Part) -> usize {
    match part {
        Part::Class => spec.k_log,
        Part::Clock => spec.clock_k_log,
    }
}

/// `log2` of an instance's packed words: the stride between consecutive instances'
/// same-port words.
pub const fn stride_log(spec: &ClassSpec, part: Part) -> usize {
    k_log(spec, part) - LOG_PACKING
}

/// The most variables any packed witness's circuit has per instance.
pub fn max_k_log() -> usize {
    (0..N_FLOCKS).map(|f| shape(f).k_log).max().unwrap_or(0)
}

/// What the verifier's replay of packed witness `f`'s reduction reads of its circuit short of its matrices.
///
/// - The instance's size.
/// - The constant wire's column, the first after the port words.
///
/// The table's spec fixes both, so the replay builds no circuit, and building the circuit checks them.
pub const fn shape(f: usize) -> Shape {
    let (t, part) = flock(f);
    let spec = ClassSpec::ALL[t];
    let n_ports = match part {
        Part::Class => spec.ports.len(),
        // The clock, each access's previous timestamp and the clock's own inputs, then the step and its own outputs.
        Part::Clock => spec.n_accesses() + 2 + spec.clock_inputs.len() + spec.clock_outputs.len(),
    };
    Shape {
        k_log: k_log(spec, part),
        const_pin_col: 64 * n_ports,
    }
}

/// Packed witness `f`'s gate list, built once.
pub fn circuit(f: usize) -> &'static Circuit {
    static CIRCUITS: [OnceLock<Circuit>; N_FLOCKS] = [const { OnceLock::new() }; N_FLOCKS];
    CIRCUITS[f].get_or_init(|| {
        let (t, part) = flock(f);
        let spec = ClassSpec::ALL[t];
        let (circuit, n_inputs) = match part {
            Part::Class => (spec.class.circuit(), spec.n_inputs),
            Part::Clock => (spec.clock_circuit(), 1 + spec.n_accesses() + spec.clock_inputs.len()),
        };
        let shape = shape(f);
        assert_eq!(
            circuit.k_log(),
            shape.k_log,
            "{}'s {part:?} block size moved",
            spec.name
        );
        assert_eq!(
            circuit.const_pos(),
            shape.const_pin_col,
            "{}'s {part:?} constant wire moved",
            spec.name
        );
        assert_eq!(
            circuit.n_input_words(),
            n_inputs,
            "{}'s {part:?} input ports moved",
            spec.name
        );
        circuit
    })
}

/// `log2` of the batch proving `n_rows` instances: a power of two, at least flock's
/// stripe floor and at least what the zerocheck's cube needs for each of the table's circuits.
pub const fn n_blocks_log(spec: &ClassSpec, n_rows: usize) -> usize {
    let n = if n_rows > 8 { n_rows } else { 8 };
    let natural = n.next_power_of_two().trailing_zeros() as usize;
    let smallest = if spec.clock_k_log < spec.k_log || !spec.has_circuit() {
        spec.clock_k_log
    } else {
        spec.k_log
    };
    let floor = MIN_CUBE_LOG.saturating_sub(smallest);
    if natural > floor { natural } else { floor }
}

/// The flock-native tables of one class's batch, kept from the pass that wrote its
/// committed column so the reduction needs no second witness pass.
pub(crate) struct Prepared {
    flock: usize,
    n_blocks_log: usize,
    z: Vec<u64>,
    a: Vec<u64>,
    b: Vec<u64>,
    z_lincheck: Vec<u8>,
}

impl Prepared {
    /// Build packed witness `f`'s batch, one instance per row of its table, and write it
    /// into `window`, its committed column.
    pub(crate) fn build(f: usize, trace: &Trace, entries: &[Entry], window: &mut [F64]) -> Self {
        let table = trace.table(flock(f).0);
        match table.payloads {
            Payloads::None => Self::build_from(f, table.rows, |r| RowRef::plain(r), entries, window),
            // Why: the witness walk takes a slice, so a payload is paired with its row first.
            _ => {
                let refs: Vec<RowRef> = (0..table.rows.len()).map(|i| table.row(i)).collect();
                Self::build_from(f, &refs, |r| *r, entries, window)
            }
        }
    }

    /// Build packed witness `f`'s batch from its table's rows, each seen through `view`.
    fn build_from<S: Sync>(
        f: usize,
        rows: &[S],
        view: impl for<'r> Fn(&'r S) -> RowRef<'r> + Sync,
        entries: &[Entry],
        window: &mut [F64],
    ) -> Self {
        let (t, part) = flock(f);
        let spec = ClassSpec::ALL[t];
        let n_blocks_log = n_blocks_log(spec, rows.len());
        assert_eq!(
            rows.len(),
            1 << n_blocks_log,
            "a table's rows fill its batch (cpu::filler)"
        );
        let circuit = circuit(f);
        let ports = ClassTable::all()[t].ports(part);
        let n_inputs = circuit.n_input_words();
        let slots = spec.slots();
        // The row's input words, one per input port.
        let input_words = |row: &S, words: &mut [u64]| {
            let row = view(row);
            for (word, &port) in words.iter_mut().zip(ports) {
                *word = port.value(row, &entries[row.row.index as usize], &slots);
            }
        };
        // A class with a word-level witness skips the walk of its gate list; the others
        // walk it 64 instances at a time.
        let witness = spec.witness.filter(|_| part == Part::Class);
        let batch_witness = spec.batch_witness.filter(|_| part == Part::Class);
        let (z, a, b, z_lincheck) = batch_witness.map_or_else(
            || {
                witness.map_or_else(
                    || circuit.generate_witness_from(rows, &rows[0], n_blocks_log, input_words),
                    |witness| {
                        circuit.generate_witness_with(rows, &rows[0], n_blocks_log, |row, z, az, bz| {
                            let mut words = [0u64; MAX_INPUT_WORDS];
                            let words = &mut words[..n_inputs];
                            input_words(row, words);
                            witness(words, z, az, bz);
                        })
                    },
                )
            },
            |batch| {
                // Eight rows share a native arithmetic call before their byte stripe is packed.
                circuit.generate_witness_batched(rows, &rows[0], n_blocks_log, |rows, z, az, bz| {
                    let mut words = [[0u64; MAX_INPUT_WORDS]; 8];
                    for (row, words) in rows.into_iter().zip(&mut words) {
                        input_words(row, &mut words[..n_inputs]);
                    }
                    let inputs = std::array::from_fn(|i| &words[i][..n_inputs]);
                    batch(&inputs, z, az, bz);
                })
            },
        );
        assert_eq!(window.len(), z.len(), "the committed column is the wrong size");
        let stride = 1 << stride_log(spec, part);
        // `F64` is `repr(transparent)` over `u64`, and the packing is bit `i` at
        // position `i` on both sides.
        const BATCH: usize = 1 << 10;
        parallel::chunks_mut_zip(window, &z, stride * BATCH, |batch, dst, src| {
            for (j, src) in src.chunks_exact(stride).enumerate() {
                // What the circuit computed is what the interpreter did, or the bus
                // would carry one and flock prove the other.
                let row = view(&rows[batch * BATCH + j]);
                for (k, &port) in ports.iter().enumerate().skip(n_inputs) {
                    let expected = port.value(row, &entries[row.row.index as usize], &slots);
                    assert_eq!(
                        src[k], expected,
                        "{}'s {part:?} circuit disagrees with the interpreter on {port:?}",
                        spec.name
                    );
                }
            }
            for (d, &s) in dst.iter_mut().zip(src) {
                *d = F64(s);
            }
        });
        Self {
            flock: f,
            n_blocks_log,
            z,
            a,
            b,
            z_lincheck,
        }
    }

    /// Flock's zerocheck then lincheck, leaving the one claim on the committed column.
    pub(crate) fn prove(&self, ps: &mut ProverState) -> SliceClaim {
        let block = circuit(self.flock).block();
        let stage = block.prove_zerocheck(self.n_blocks_log, &self.z, &self.a, &self.b, ps);
        block.prove_lincheck(self.n_blocks_log, stage, &self.z_lincheck, ps)
    }
}

/// The verifier's replay of packed witness `f`'s reduction, zerocheck then lincheck, up to the circuit's matrices.
///
/// Their form is left as a claim for the built circuit to settle.
/// It reads only the circuit's shape, and builds none.
///
/// # Errors
///
/// Returns the first stage that refuses the proof.
pub fn verify_reduction(
    f: usize,
    n_blocks_log: usize,
    vs: &mut VerifierState,
) -> Result<(ReductionReplay, MatrixClaim), FlockError> {
    shape(f).verify_deferred(n_blocks_log, vs)
}
