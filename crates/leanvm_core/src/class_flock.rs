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

use crate::cpu::Row;
use crate::rv::{Div, Entry, Ext};
use crate::tables::{CLASSES, ClassSpec, N_CIRCUITS, N_TABLES, Part, Word};
use ::pcs::pack::LOG_PACKING;
use fiat_shamir::transcript::{ProverState, VerifierState};
use flock::circuit::Circuit;
use flock::reduction::{ReductionReplay, SliceClaim};
use flock::verifier::VerifyError;
use primitives::field::F64;
use std::sync::OnceLock;
use zk_alloc::ArenaVec;

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

/// Packed witness `f`'s gate list, built once.
pub fn circuit(f: usize) -> &'static Circuit {
    static CIRCUITS: [OnceLock<Circuit>; N_FLOCKS] = [const { OnceLock::new() }; N_FLOCKS];
    CIRCUITS[f].get_or_init(|| {
        let (t, part) = flock(f);
        let spec = CLASSES[t];
        let (circuit, n_inputs) = match part {
            Part::Class => (spec.class.circuit(), spec.n_inputs),
            Part::Clock => (spec.clock_circuit(), 1 + spec.n_accesses() + spec.clock_inputs.len()),
        };
        assert_eq!(
            circuit.k_log(),
            k_log(spec, part),
            "{}'s {part:?} block size moved",
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
/// stripe floor and at least what the zerocheck's cube needs for both of the table's circuits.
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

/// A row's value of one circuit word.
///
/// `slots` are the clock slots of the row's accesses.
fn word_of(word: Word, slots: &[u32], row: &Row, entry: &Entry) -> u64 {
    // The division's honest hints, the circuit's two prover-supplied ports.
    let hints = || {
        Div {
            flags: entry.flags,
            v1: row.v1,
            v2: row.v2,
        }
        .hints()
    };
    // An extension-field row's limbs and pointers.
    let ext = || row.ext.as_ref().expect("an extension-field row has its pointers");
    match word {
        Word::Clock => row.ts,
        Word::Prev(i) => row.prev()[i as usize],
        Word::Step => crate::tables::clock_step(row.ts, &row.prev()[..slots.len()], slots),
        Word::Flags => entry.flags,
        Word::Imm => entry.imm,
        Word::V1 => row.v1,
        Word::V2 => row.v2,
        Word::Out => row.out,
        Word::Taken => row.taken as u64,
        Word::Address => row.ram.address,
        Word::Cell(k) => row.hash.as_ref().map_or(row.ram.old, |h| h.block[k as usize]),
        Word::CellNew(k) => row.hash.as_ref().map_or(row.ram.new, |h| h.word_after(k as usize)),
        Word::Dest => ext().instance.pointers[2],
        Word::FlagBit(k) => entry.flags >> k & 1,
        Word::LimbAddress(k) => {
            let x = &ext().instance;
            Ext::bus_address(x.pointers, x.flags, k as usize)
        }
        Word::Bad => 0,
        Word::HintQ => hints().0,
        Word::HintR => hints().1,
    }
}

/// The flock-native tables of one class's batch, kept from the pass that wrote its
/// committed column so the reduction needs no second witness pass.
pub(crate) struct Prepared {
    flock: usize,
    n_blocks_log: usize,
    z: ArenaVec<u64>,
    a: ArenaVec<u64>,
    b: ArenaVec<u64>,
    z_lincheck: ArenaVec<u8>,
}

impl Prepared {
    /// Build packed witness `f`'s batch, one instance per row of its table, and write it
    /// into `window`, its committed column.
    pub(crate) fn build(f: usize, rows: &[Row], entries: &[Entry], window: &mut [F64]) -> Self {
        let (t, part) = flock(f);
        let spec = CLASSES[t];
        let n_blocks_log = n_blocks_log(spec, rows.len());
        assert_eq!(
            rows.len(),
            1 << n_blocks_log,
            "a table's rows fill its batch (cpu::filler)"
        );
        let circuit = circuit(f);
        let ports = crate::tables::tables()[t].ports(part);
        let n_inputs = circuit.n_input_words();
        let slots = spec.slots();
        // The row's input words, one per input port.
        let input_words = |row: &Row, words: &mut [u64]| {
            for (word, &port) in words.iter_mut().zip(ports) {
                *word = word_of(port, &slots, row, &entries[row.index as usize]);
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
                let row = &rows[batch * BATCH + j];
                for (k, &port) in ports.iter().enumerate().skip(n_inputs) {
                    let expected = word_of(port, &slots, row, &entries[row.index as usize]);
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

/// The verifier's replay of packed witness `f`'s reduction: zerocheck, then lincheck.
pub fn verify_reduction(f: usize, n_blocks_log: usize, vs: &mut VerifierState) -> Result<ReductionReplay, VerifyError> {
    circuit(f).block().verify(n_blocks_log, vs)
}
