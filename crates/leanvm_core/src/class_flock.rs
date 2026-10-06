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
//! words a row puts on the bus ARE packed words of its instance, the circuit's ports.
//! The table's columns for them are therefore virtual, their claims routed to those words.

use crate::cpu::{Payloads, RowRef, Trace};
use crate::rv::RiscvProgram;
use crate::tables::{Fill, N_CIRCUITS, N_TABLES, Part, PerTable, TableId};
use flock::circuit::Circuit;
use flock::reduction::{Instance, Shape, min_n_blocks_log};
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

/// One packed witness: a table's class circuit, or its clock circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FlockId {
    table: TableId,
    part: Part,
}

impl FlockId {
    /// Every packed witness, in protocol order.
    pub const ALL: [Self; N_FLOCKS] = {
        let mut all = [Self::clock(TableId::ALU); N_FLOCKS];
        let mut t = 0;
        while t < N_TABLES {
            let table = TableId::ALL[t];
            if let Some(class) = Self::class(table) {
                all[class.index()] = class;
            }
            all[Self::clock(table).index()] = Self::clock(table);
            t += 1;
        }
        all
    };

    /// The most variables any packed witness's circuit has per instance.
    pub const MAX_K_LOG: usize = {
        let mut max = 0;
        let mut f = 0;
        while f < N_FLOCKS {
            if Self::ALL[f].k_log() > max {
                max = Self::ALL[f].k_log();
            }
            f += 1;
        }
        max
    };

    /// The class circuit of `table`, if its class has one.
    pub const fn class(table: TableId) -> Option<Self> {
        if table.spec().has_circuit() {
            Some(Self {
                table,
                part: Part::Class,
            })
        } else {
            None
        }
    }

    /// The clock circuit of `table`.
    pub const fn clock(table: TableId) -> Self {
        Self {
            table,
            part: Part::Clock,
        }
    }

    /// The table whose rows are the witness's instances.
    pub const fn table(self) -> TableId {
        self.table
    }

    /// Which of the table's circuits it is.
    pub const fn part(self) -> Part {
        self.part
    }

    /// Its position in protocol order.
    pub const fn index(self) -> usize {
        match self.part {
            Part::Class => self.table.index(),
            Part::Clock => N_CIRCUITS + self.table.index(),
        }
    }

    /// `log2` of the bits one instance occupies.
    pub const fn k_log(self) -> usize {
        let spec = self.table.spec();
        match (self.part, &spec.circuit) {
            (Part::Class, Some(circuit)) => circuit.k_log,
            (Part::Class, None) => unreachable!(),
            (Part::Clock, _) => spec.clock_k_log,
        }
    }

    /// `log2` of an instance's packed words: the stride between consecutive instances' same-port words.
    pub const fn stride_log(self) -> usize {
        self.k_log() - F64::DEGREE.ilog2() as usize
    }

    /// What the verifier's replay of the witness's reduction reads of its circuit short of its matrices.
    ///
    /// - The instance's size.
    /// - The constant wire's column, the first after the port words.
    ///
    /// The table's spec fixes both, so the replay builds no circuit, and building the circuit checks them.
    pub const fn shape(self) -> Shape {
        let spec = self.table.spec();
        let n_ports = match (self.part, &spec.circuit) {
            (Part::Class, Some(circuit)) => circuit.inputs.len() + circuit.outputs.len(),
            (Part::Class, None) => unreachable!(),
            // The clock, each access's previous timestamp and the clock's own inputs, then the step and its own outputs.
            (Part::Clock, _) => spec.n_accesses() + 2 + spec.clock_inputs.len() + spec.clock_outputs.len(),
        };
        Shape {
            k_log: self.k_log(),
            const_pin_col: 64 * n_ports,
        }
    }

    /// The witness's gate list, built once.
    pub fn circuit(self) -> &'static Circuit {
        static CIRCUITS: [OnceLock<Circuit>; N_FLOCKS] = [const { OnceLock::new() }; N_FLOCKS];
        CIRCUITS[self.index()].get_or_init(|| {
            let (spec, part) = (self.table.spec(), self.part);
            let (circuit, n_inputs) = match &spec.circuit {
                Some(circuit) if part == Part::Class => (spec.class.circuit(), circuit.inputs.len()),
                _ => (spec.clock_circuit(), 1 + spec.n_accesses() + spec.clock_inputs.len()),
            };
            let shape = self.shape();
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
}

/// `log2` of the batch proving a table's rows on one circuit, given `log2` of its bits per instance.
///
/// - At least flock's stripe floor of eight instances.
/// - At least what the zerocheck's cube of `2^13` bits needs.
pub const fn batch_log(k_log: usize, n_rows: usize) -> usize {
    let natural = min_n_blocks_log(if n_rows > 1 { n_rows } else { 1 });
    let floor = MIN_CUBE_LOG.saturating_sub(k_log);
    if natural > floor { natural } else { floor }
}

impl FlockId {
    /// Each packed witness's shape and `log2` of its batch, its table's height `2^taus`, in protocol order.
    ///
    /// The verifier's replay of the reductions reads these alone, and builds no circuit.
    pub fn batches(taus: &PerTable<usize>) -> [(Shape, usize); N_FLOCKS] {
        Self::ALL.map(|f| (f.shape(), taus[f.table()]))
    }

    /// The witness's batch, one instance per row of its table, also written into `window`, its committed column.
    ///
    /// The reduction keeps it, so it needs no second witness pass.
    pub(crate) fn instance(self, trace: &Trace, p: &RiscvProgram, window: &mut [F64]) -> Instance<'static> {
        let table = trace.table(self.table);
        match table.payloads {
            Payloads::None => self.instance_of(table.rows, |r| RowRef::plain(r), p, window),
            // Why: the witness walk takes a slice, so a payload is paired with its row first.
            _ => {
                let refs: Vec<RowRef> = (0..table.rows.len()).map(|i| table.row(i)).collect();
                self.instance_of(&refs, |r| *r, p, window)
            }
        }
    }

    /// The witness's batch from its table's rows, each seen through `view`.
    fn instance_of<S: Sync>(
        self,
        rows: &[S],
        view: impl for<'r> Fn(&'r S) -> RowRef<'r> + Sync,
        p: &RiscvProgram,
        window: &mut [F64],
    ) -> Instance<'static> {
        let (part, spec) = (self.part, self.table.spec());
        let n_blocks_log = spec.n_blocks_log(rows.len());
        assert_eq!(
            rows.len(),
            1 << n_blocks_log,
            "a table's rows fill its batch (cpu::filler)"
        );
        let circuit = self.circuit();
        let ports = self.table.class_table().ports(part);
        let n_inputs = circuit.n_input_words();
        let slots = spec.slots();
        // The row's input words, one per input port.
        let input_words = |row: &S, words: &mut [u64]| {
            let row = view(row);
            let at = p.fetch(row.row.index as usize);
            for (word, &port) in words.iter_mut().zip(ports) {
                *word = port.value(row, at, &slots);
            }
        };
        let fill = match (part, &spec.circuit) {
            (Part::Class, Some(class)) => class.fill,
            _ => Fill::Walk,
        };
        let witness = match fill {
            Fill::Walk => circuit.generate_witness_from(rows, &rows[0], n_blocks_log, input_words),
            Fill::Instance(instance) => {
                circuit.generate_witness_with(rows, &rows[0], n_blocks_log, |row, z, az, bz| {
                    let mut words = [0u64; MAX_INPUT_WORDS];
                    let words = &mut words[..n_inputs];
                    input_words(row, words);
                    instance(words, z, az, bz);
                })
            }
            // Eight rows share a native arithmetic call before their byte stripe is packed.
            Fill::Batch8(batch) => circuit.generate_witness_batched(rows, &rows[0], n_blocks_log, |rows, z, az, bz| {
                let mut words = [[0u64; MAX_INPUT_WORDS]; 8];
                for (row, words) in rows.into_iter().zip(&mut words) {
                    input_words(row, &mut words[..n_inputs]);
                }
                let inputs = std::array::from_fn(|i| &words[i][..n_inputs]);
                batch(&inputs, z, az, bz);
            }),
        };
        assert_eq!(window.len(), witness.z.len(), "the committed column is the wrong size");
        let stride = 1 << self.stride_log();
        // `F64` is `repr(transparent)` over `u64`, and the packing is bit `i` at
        // position `i` on both sides.
        const BATCH: usize = 1 << 10;
        parallel::chunks_mut_zip(window, &witness.z, stride * BATCH, |batch, dst, src| {
            for (j, src) in src.chunks_exact(stride).enumerate() {
                // What the circuit computed is what the interpreter did, or the bus
                // would carry one and flock prove the other.
                let row = view(&rows[batch * BATCH + j]);
                let at = p.fetch(row.row.index as usize);
                for (k, &port) in ports.iter().enumerate().skip(n_inputs) {
                    let expected = port.value(row, at, &slots);
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
        Instance {
            block: circuit.block(),
            n_blocks_log,
            witness,
        }
    }
}
