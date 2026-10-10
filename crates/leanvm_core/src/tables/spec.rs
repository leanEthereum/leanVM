//! Instruction-class specifications in protocol table order.

use super::{N_TABLES, TableId, Word};
use crate::rv::{Alu, Class, Ext, Hash, Ld, Load, Mul, Mulh, Shift, Store};
use crate::{class_flock, rv};

/// How a class uses RAM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ram {
    /// No memory access.
    None,
    /// One cell read, at the address the circuit computes.
    Read,
    /// One cell read and rewritten.
    Write,
    /// Sixteen hash block words, with four output words rewritten.
    Block,
    /// Nine extension-field limbs, with the destination's three limbs rewritten.
    Limbs,
}

impl Ram {
    /// The memory log's rows a row of the class takes.
    pub const fn accesses(self) -> usize {
        match self {
            Self::None => 0,
            Self::Read | Self::Write => 1,
            Self::Block => Hash::WORDS,
            Self::Limbs => Ext::LIMBS,
        }
    }
}

/// One instance's `z`, `A·z` and `B·z` from its input words, into zeroed buffers.
pub type InstanceWitness = fn(&[u64], &mut [u64], &mut [u64], &mut [u64]);

/// Eight instances' packed witness by native word arithmetic.
pub type BatchWitness = fn(&[&[u64]; 8], &mut [u64], &mut [u64], &mut [u64]);

/// How a class circuit's witness is generated.
#[derive(Clone, Copy, Debug)]
pub enum Fill {
    /// The generic walk of the gate list, 64 instances at a time.
    Walk,
    /// Word arithmetic one instance at a time, checked against the walk.
    Instance(InstanceWitness),
    /// Word arithmetic eight instances at a time, checked against the walk.
    Batch8(BatchWitness),
}

/// A class's flock circuit: its size, its ports, and how its witness is generated.
pub struct ClassCircuit {
    /// Base-two logarithm of the circuit's bits per instance.
    pub k_log: usize,

    /// The words the circuit reads, in port order.
    pub inputs: &'static [Word],

    /// The words the circuit gives, in port order after the inputs.
    pub outputs: &'static [Word],

    /// How the witness is generated.
    pub fill: Fill,
}

/// A class's operand circuit: what a class with no class circuit checks of its operands.
pub struct OperandCircuit {
    /// Base-two logarithm of the circuit's bits per instance.
    pub k_log: usize,

    /// The words the circuit reads, in port order.
    pub inputs: &'static [Word],

    /// The words the circuit gives, in port order after the inputs.
    pub outputs: &'static [Word],
}

/// Register accesses, memory shape, and circuit ports of one instruction class.
pub struct ClassSpec {
    /// Instruction class executed by this table.
    pub class: Class,

    /// Table name used in diagnostics and reports.
    pub name: &'static str,

    /// Whether branches and jumps move the successor by the circuit's jump.
    pub control: bool,

    /// Whether the second source register is read.
    pub reads_rs2: bool,

    /// Whether the destination register receives a result.
    pub writes_rd: bool,

    /// Whether the destination register supplies an address.
    pub reads_rd: bool,

    /// Memory accesses made after the register accesses.
    pub ram: Ram,

    /// Whether a doubleword is moved unchanged through a shared column.
    pub copies: bool,

    /// The class's flock circuit, or none for a class whose table proves it by identities (`ClassTable::identities`).
    pub circuit: Option<ClassCircuit>,

    /// The class's operand circuit, for a class with no class circuit.
    pub operands: Option<OperandCircuit>,
}

impl ClassSpec {
    /// Arithmetic, comparisons, logic, branches, and jumps.
    pub const ALU: Self = Self {
        class: Class::Alu,
        name: "ALU",
        control: true,
        reads_rs2: true,
        writes_rd: true,
        reads_rd: false,
        ram: Ram::None,
        copies: false,
        circuit: Some(ClassCircuit {
            k_log: 10,
            inputs: &[Word::V1, Word::V2, Word::Imm, Word::Flags, Word::Dt, Word::Pc4],
            outputs: &[Word::Out, Word::Jump],
            fill: Fill::Instance(Alu::witness),
        }),
        operands: None,
    };

    /// Byte, halfword, and word loads with extension to 64 bits.
    pub const LOAD: Self = Self {
        class: Class::Load,
        name: "LOAD",
        control: false,
        reads_rs2: false,
        writes_rd: true,
        reads_rd: false,
        ram: Ram::Read,
        copies: false,
        circuit: Some(ClassCircuit {
            k_log: 10,
            inputs: &[Word::V1, Word::Imm, Word::Flags, Word::Cell(0)],
            outputs: &[Word::Address, Word::Out],
            fill: Fill::Instance(Load::witness),
        }),
        operands: None,
    };

    /// Byte, halfword, and word stores into a memory cell.
    pub const STORE: Self = Self {
        class: Class::Store,
        name: "STORE",
        control: false,
        reads_rs2: true,
        writes_rd: false,
        reads_rd: false,
        ram: Ram::Write,
        copies: false,
        circuit: Some(ClassCircuit {
            k_log: 10,
            inputs: &[Word::V1, Word::V2, Word::Imm, Word::Flags, Word::Cell(0)],
            outputs: &[Word::Address, Word::CellNew(0)],
            fill: Fill::Instance(Store::witness),
        }),
        operands: None,
    };

    /// `ld`: the cell at `v1 + imm` is what `rd` receives.
    pub const LD: Self = Self {
        class: Class::Ld,
        name: "LD",
        control: false,
        reads_rs2: false,
        writes_rd: true,
        reads_rd: false,
        ram: Ram::Read,
        copies: true,
        circuit: Some(ClassCircuit {
            k_log: 8,
            inputs: &[Word::V1, Word::Imm],
            outputs: &[Word::Address],
            fill: Fill::Instance(Ld::witness),
        }),
        operands: None,
    };

    /// `sd`: `v2` is what the cell at `v1 + imm` receives.
    pub const SD: Self = Self {
        class: Class::Sd,
        name: "SD",
        control: false,
        reads_rs2: true,
        writes_rd: false,
        reads_rd: false,
        ram: Ram::Write,
        copies: true,
        circuit: Some(ClassCircuit {
            k_log: 8,
            inputs: &[Word::V1, Word::Imm],
            outputs: &[Word::Address],
            fill: Fill::Instance(Ld::witness),
        }),
        operands: None,
    };

    /// Logical and arithmetic shifts, including 32-bit word forms.
    pub const SHIFT: Self = Self {
        class: Class::Shift,
        name: "SHIFT",
        control: false,
        reads_rs2: true,
        writes_rd: true,
        reads_rd: false,
        ram: Ram::None,
        copies: false,
        circuit: Some(ClassCircuit {
            k_log: 10,
            inputs: &[Word::V1, Word::V2, Word::Imm, Word::Flags],
            outputs: &[Word::Out],
            fill: Fill::Instance(Shift::witness),
        }),
        operands: None,
    };

    /// Low half of a register product.
    pub const MUL: Self = Self {
        class: Class::Mul,
        name: "MUL",
        control: false,
        reads_rs2: true,
        writes_rd: true,
        reads_rd: false,
        ram: Ram::None,
        copies: false,
        circuit: Some(ClassCircuit {
            k_log: 12,
            inputs: &[Word::V1, Word::V2, Word::Flags],
            outputs: &[Word::Out],
            fill: if cfg!(all(target_arch = "x86_64", target_feature = "avx2")) {
                Fill::Batch8(Mul::witness_batch)
            } else {
                Fill::Walk
            },
        }),
        operands: None,
    };

    /// High half of a register product with signedness selectors.
    pub const MULH: Self = Self {
        class: Class::Mulh,
        name: "MULH",
        control: false,
        reads_rs2: true,
        writes_rd: true,
        reads_rd: false,
        ram: Ram::None,
        copies: false,
        circuit: Some(ClassCircuit {
            k_log: 13,
            inputs: &[Word::V1, Word::V2, Word::Flags],
            outputs: &[Word::Out],
            fill: Fill::Instance(Mulh::witness),
        }),
        operands: None,
    };

    /// Quotients and remainders with prover-supplied magnitude hints.
    pub const DIV: Self = Self {
        class: Class::Div,
        name: "DIV",
        control: false,
        reads_rs2: true,
        writes_rd: true,
        reads_rd: false,
        ram: Ram::None,
        copies: false,
        circuit: Some(ClassCircuit {
            k_log: 13,
            inputs: &[Word::V1, Word::V2, Word::Flags, Word::HintQ, Word::HintR],
            outputs: &[Word::Out, Word::Bad],
            fill: Fill::Walk,
        }),
        operands: None,
    };

    /// BLAKE2s compression over sixteen memory words, rewriting the four output words.
    pub const HASH: Self = Self {
        class: Class::Hash,
        name: "HASH",
        control: false,
        reads_rs2: true,
        writes_rd: false,
        reads_rd: false,
        ram: Ram::Block,
        copies: false,
        circuit: Some(ClassCircuit {
            k_log: 14,
            inputs: &[
                Word::V2,
                Word::Flags,
                Word::Cell(0),
                Word::Cell(1),
                Word::Cell(2),
                Word::Cell(3),
                Word::Cell(8),
                Word::Cell(9),
                Word::Cell(10),
                Word::Cell(11),
                Word::Cell(12),
                Word::Cell(13),
                Word::Cell(14),
                Word::Cell(15),
            ],
            outputs: &[Word::CellNew(4), Word::CellNew(5), Word::CellNew(6), Word::CellNew(7)],
            fill: Fill::Instance(rv::circuits::blake2s_witness),
        }),
        operands: None,
    };

    /// Extension-field multiplication, optionally accumulating or using a base-field operand.
    ///
    /// No class circuit: the limbs are committed columns, and the table's identities (`ClassTable::identities`) say the product.
    ///
    /// Its operand circuit splits the flags into their bits and computes the limbs' addresses.
    pub const EXT: Self = Self {
        class: Class::Ext,
        name: "EXT",
        control: false,
        reads_rs2: true,
        writes_rd: false,
        reads_rd: true,
        ram: Ram::Limbs,
        copies: false,
        circuit: None,
        operands: Some(OperandCircuit {
            k_log: 11,
            inputs: &[Word::V1, Word::V2, Word::Dest, Word::Flags],
            outputs: &[
                Word::FlagBit(0),
                Word::FlagBit(1),
                Word::LimbAddress(1),
                Word::LimbAddress(2),
                Word::LimbAddress(4),
                Word::LimbAddress(5),
                Word::LimbAddress(7),
                Word::LimbAddress(8),
            ],
        }),
    };

    /// Check that register accesses and copy semantics match the circuit ports.
    pub(super) fn assert_valid(&self) {
        // Invariant: a register access exists exactly when its value is a word of one of the table's circuits, or a column a doubleword load or store moves.
        let has = |word: Word| self.words().any(|w| w == word);
        assert_eq!(self.reads_rs2 && !self.copies, has(Word::V2), "{}: rs2 read", self.name);
        assert_eq!(
            self.writes_rd && !self.copies,
            has(Word::Out),
            "{}: rd write",
            self.name
        );
        assert_eq!(self.reads_rd, has(Word::Dest), "{}: rd read", self.name);
        assert!(
            !(self.reads_rd && self.writes_rd),
            "{}: rd is read or written, not both",
            self.name
        );
        // A class with branches and jumps gates the bytecode's offset in its circuit, and reads `pc + 4` for its indirect jump.
        assert!(
            self.control == (has(Word::Dt) && has(Word::Jump)) && self.control == has(Word::Pc4),
            "{}: control flow",
            self.name
        );
        // A doubleword load moves its cell to `rd`, a doubleword store `v2` to its cell, and its circuit gives the address alone.
        if self.copies {
            let moves = match self.ram {
                Ram::Read => self.writes_rd && !self.reads_rs2,
                Ram::Write => self.reads_rs2 && !self.writes_rd,
                Ram::None | Ram::Block | Ram::Limbs => false,
            };
            let ports = [Word::V1, Word::Imm, Word::Address];
            assert!(
                moves && !self.control && !self.reads_rd && self.ports().eq(ports),
                "{}: a copy",
                self.name
            );
        }
    }

    /// Smallest power-of-two height accepted by each of the table's circuits.
    ///
    /// A batch has at least eight instances and a zerocheck cube of at least 2^13 bits.
    pub const fn min_rows(&self) -> usize {
        1 << self.n_blocks_log(1)
    }

    /// `log2` of the batch proving `n_rows` of the table's rows: a power of two, at least flock's floor of eight instances and at
    /// least what the zerocheck's cube needs for each of the table's circuits.
    pub const fn n_blocks_log(&self, n_rows: usize) -> usize {
        let smallest = match (&self.circuit, &self.operands) {
            (Some(circuit), _) => circuit.k_log,
            (None, Some(operands)) => operands.k_log,
            (None, None) => panic!("a class has a class circuit or an operand circuit"),
        };
        class_flock::batch_log(smallest, n_rows)
    }

    /// The height the table is proven at when the run makes `rows` of its rows: the next power of two at or above its floor.
    pub const fn provable_height(&self, rows: usize) -> usize {
        let floor = self.min_rows();
        if rows > floor { rows.next_power_of_two() } else { floor }
    }

    /// Whether the table can be proven over `rows` rows: a power of two at or above its floor.
    pub const fn is_provable_height(&self, rows: usize) -> bool {
        rows.is_power_of_two() && rows >= self.min_rows()
    }

    /// Whether the class is a flock circuit; otherwise its table's identities prove it.
    pub const fn has_circuit(&self) -> bool {
        self.circuit.is_some()
    }

    /// The class circuit's port words, inputs then outputs: none for a class with no circuit.
    pub fn ports(&self) -> impl Iterator<Item = Word> + '_ {
        (self.circuit.iter())
            .flat_map(|c| c.inputs.iter().chain(c.outputs))
            .copied()
    }

    /// The operand circuit's port words, inputs then outputs: none for a class with a class circuit.
    pub fn operand_ports(&self) -> impl Iterator<Item = Word> + '_ {
        (self.operands.iter())
            .flat_map(|c| c.inputs.iter().chain(c.outputs))
            .copied()
    }

    /// Every word of the table's circuits: its class circuit's, then its operand circuit's.
    pub(super) fn words(&self) -> impl Iterator<Item = Word> + '_ {
        self.ports().chain(self.operand_ports())
    }
}

/// Bytecode slot binding a circuit's verdict to a public zero.
///
/// It follows all decoded instruction fields.
pub const BAD_SLOT: usize = 10;

/// Bytecode slot binding the exit selector.
pub const EXIT_SLOT: usize = 11;

/// Number of tables with a class circuit, which come first: table `t < N_CIRCUITS` has one, and its class circuit is
/// packed witness `t`.
///
/// Their bus forms are linear, so their columns are opened at the bus's point.
///
/// The tables past them prove identities of their own, in the table sumcheck.
pub const N_CIRCUITS: usize = {
    let mut n = 0;
    while n < N_TABLES && TableId::ALL[n].spec().has_circuit() {
        n += 1;
    }
    n
};

// The tables with a class circuit come first.
const _: () = {
    let mut t = N_CIRCUITS;
    while t < N_TABLES {
        assert!(
            !TableId::ALL[t].spec().has_circuit(),
            "the tables with a class circuit come first"
        );
        t += 1;
    }
};
