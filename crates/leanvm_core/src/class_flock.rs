//! Bridge to flock for the instruction tables.
//!
//! Each class's circuit and each table's clock circuit is proven over one packed witness of its own.
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
use crate::rv::{Div, Entry};
use crate::tables::{CLASSES, ClassSpec, N_TABLES, Part, Word};
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

/// The packed witnesses: every table's class circuit in table order, then every table's clock circuit.
pub const N_FLOCKS: usize = 2 * N_TABLES;

/// The table and the circuit of packed witness `f`.
pub const fn flock(f: usize) -> (usize, Part) {
    if f < N_TABLES {
        (f, Part::Class)
    } else {
        (f - N_TABLES, Part::Clock)
    }
}

/// The packed witness of table `t`'s circuit `part`.
pub const fn flock_index(t: usize, part: Part) -> usize {
    match part {
        Part::Class => t,
        Part::Clock => N_TABLES + t,
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
            Part::Clock => (crate::tables::clock_circuit(&spec.slots()), 1 + spec.n_accesses()),
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
    let smallest = if spec.clock_k_log < spec.k_log {
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
    // An extension-field row's limbs.
    let ext = || row.ext.as_ref().expect("an extension-field row has its limbs");
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
        Word::Cell(k) => match (&row.hash, &row.ext) {
            (Some(h), _) => h.block[k as usize],
            (_, Some(x)) => x.instance.limbs[k as usize],
            _ => row.ram.old,
        },
        Word::CellNew(k) => match (&row.hash, &row.ext) {
            (Some(h), _) => h.word_after(k as usize),
            (_, Some(x)) => x.result.c[k as usize - 6],
            _ => row.ram.new,
        },
        Word::Dest => ext().instance.pointers[2],
        Word::LimbAddress(k) => {
            let i = crate::rv::ExtResult::OFFSET_LIMBS.iter().position(|&j| j == k as usize);
            ext().result.addresses[i.expect("a computed limb address")]
        }
        Word::LimbSeparator => ext().result.separator,
        Word::Bad => 0,
        Word::HintQ => hints().0,
        Word::HintR => hints().1,
    }
}

/// Instances of the padding unit: past the explicit instances, a batch is copies of
/// this many padding instances (§sec:jagged), which flock proves as one unit.
const PAD_UNIT: usize = 64;

/// One table of a batch: in the arena, or on the heap when the arena would not
/// recycle its block (below [`zk_alloc::REUSE_MIN`]), since a small arena block
/// outliving its neighbors keeps their released space from merging.
enum Table<T> {
    Arena(ArenaVec<T>),
    Heap(Vec<T>),
}

impl<T: Copy> Table<T> {
    /// Copied out, and released, while the arena's latest block: the copies are taken
    /// in reverse allocation order, so each pops the arena's cursor.
    fn new(table: ArenaVec<T>) -> Self {
        if size_of_val(&table[..]) < zk_alloc::REUSE_MIN {
            Self::Heap(table.to_vec())
        } else {
            Self::Arena(table)
        }
    }
}

impl<T> std::ops::Deref for Table<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        match self {
            Self::Arena(table) => table,
            Self::Heap(table) => table,
        }
    }
}

/// The flock-native tables of one class's batch, kept from the pass that wrote its
/// committed column so the reduction needs no second witness pass.
///
/// They hold the batch's first instances only, its rows and then padding instances
/// up to a whole number of [`PAD_UNIT`]s; every later instance repeats the padding
/// row, so the reduction takes them as copies of one unit of them (`pad`).
pub(crate) struct Prepared {
    flock: usize,
    n_blocks_log: usize,
    z: Table<u64>,
    a: Table<u64>,
    b: Table<u64>,
    z_lincheck: Table<u8>,
    /// The padding unit's `z`, `A·z` and `B·z`, when instances are left to it, on the
    /// heap as a small [`Table`] is.
    pad: Option<[Vec<u64>; 3]>,
}

impl Prepared {
    /// Build packed witness `f`'s batch of `2^n_blocks_log` instances from its table's
    /// committed rows, the live ones then the padding row every later row repeats,
    /// writing its committed column's pieces, `(first row, piece)`, in place as it goes.
    pub(crate) fn build(
        f: usize,
        n_blocks_log: usize,
        rows: &[Row],
        entries: &[Entry],
        pieces: Vec<(usize, &mut [F64])>,
    ) -> Self {
        let (t, part) = flock(f);
        let spec = CLASSES[t];
        let explicit = rows.len().next_multiple_of(PAD_UNIT).min(1 << n_blocks_log);
        let padding = rows.last().expect("a table commits at least its padding row");
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
        let generate =
            |rows: &[Row], n_instances: usize, copies: &mut [flock::ZCopy<'_>]| match (batch_witness, witness) {
                // Eight rows share a native arithmetic call before their byte stripe is packed.
                (Some(batch), _) => {
                    circuit.generate_witness_batched(rows, padding, n_instances, copies, |rows, z, az, bz| {
                        let mut words = [[0u64; MAX_INPUT_WORDS]; 8];
                        for (row, words) in rows.into_iter().zip(&mut words) {
                            input_words(row, &mut words[..n_inputs]);
                        }
                        let inputs = std::array::from_fn(|i| &words[i][..n_inputs]);
                        batch(&inputs, z, az, bz);
                    })
                }
                (None, None) => circuit.generate_witness_from(rows, padding, n_instances, copies, input_words),
                (None, Some(witness)) => {
                    circuit.generate_witness_with(rows, padding, n_instances, copies, |row, z, az, bz| {
                        let mut words = [0u64; MAX_INPUT_WORDS];
                        let words = &mut words[..n_inputs];
                        input_words(row, words);
                        witness(words, z, az, bz);
                    })
                }
            };
        let mut copies: Vec<flock::ZCopy<'_>> = (pieces.into_iter())
            .map(|(first, piece)| flock::ZCopy {
                first,
                // SAFETY: `F64` is `repr(transparent)` over `u64`, and the packing is bit
                // `i` at position `i` on both sides.
                words: unsafe { std::slice::from_raw_parts_mut(piece.as_mut_ptr().cast::<u64>(), piece.len()) },
            })
            .collect();
        let (z, a, b, z_lincheck) = generate(rows, explicit, &mut copies);
        // In reverse allocation order (`Table::new`).
        let z_lincheck = Table::new(z_lincheck);
        let (b, a, z) = (Table::new(b), Table::new(a), Table::new(z));
        let pad = (explicit < 1 << n_blocks_log).then(|| {
            // Built last, so the arena pops it whole once it is copied out.
            let (z, a, b, _) = generate(&[], PAD_UNIT, &mut []);
            [z.to_vec(), a.to_vec(), b.to_vec()]
        });
        let stride = 1 << stride_log(spec, part);
        assert_eq!(z.len(), explicit * stride, "the batch is the wrong size");
        const BATCH: usize = 1 << 10;
        parallel::for_each(rows.len().div_ceil(BATCH), |batch| {
            let first = batch * BATCH;
            for (j, row) in rows[first..rows.len().min(first + BATCH)].iter().enumerate() {
                let src = &z[(first + j) * stride..][..stride];
                // What the circuit computed is what the interpreter did, or the bus
                // would carry one and flock prove the other.
                for (k, &port) in ports.iter().enumerate().skip(n_inputs) {
                    let expected = word_of(port, &slots, row, &entries[row.index as usize]);
                    assert_eq!(
                        src[k], expected,
                        "{}'s {part:?} circuit disagrees with the interpreter on {port:?}",
                        spec.name
                    );
                }
            }
        });
        Self {
            flock: f,
            n_blocks_log,
            z,
            a,
            b,
            z_lincheck,
            pad,
        }
    }

    /// Flock's zerocheck then lincheck, leaving the one claim on the committed column.
    pub(crate) fn prove(&self, ps: &mut ProverState) -> SliceClaim {
        let block = circuit(self.flock).block();
        let pad = self.pad.as_ref().map(|[z, a, b]| [&z[..], &a[..], &b[..]]);
        let stage = block.prove_zerocheck(self.n_blocks_log, &self.z, &self.a, &self.b, pad, ps);
        // The padding instance, the unit's first.
        let pad_z = pad.map(|[z, ..]| &z[..z.len() / PAD_UNIT]);
        block.prove_lincheck(self.n_blocks_log, stage, &self.z_lincheck, pad_z, ps)
    }
}

/// The verifier's replay of packed witness `f`'s reduction: zerocheck, then lincheck.
pub fn verify_reduction(f: usize, n_blocks_log: usize, vs: &mut VerifierState) -> Result<ReductionReplay, VerifyError> {
    circuit(f).block().verify(n_blocks_log, vs)
}
