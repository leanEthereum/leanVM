//! Instruction-class specifications in protocol table order.

use super::Word;
use super::clock::Clock;
use crate::rv::{Class, Ext, Hash, Mul, Mulh};
use crate::{class_flock, rv};
use std::ops::Range;

/// How a class uses RAM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ram {
    /// No memory access.
    None,
    /// One cell read, in clock slot 2, at the address the circuit computes.
    Read,
    /// One cell read and rewritten.
    Write,
    /// Sixteen hash block words, with four output words rewritten.
    Block,
    /// Nine extension-field limbs, with the destination's three limbs rewritten.
    Limbs,
}

impl Ram {
    /// Clock slots occupied by this memory access shape.
    const fn slots(self) -> Range<u32> {
        match self {
            Self::None => 0..0,
            Self::Read | Self::Write => Clock::RAM_SLOT..Clock::RAM_SLOT + 1,
            Self::Block => Clock::block_slot(0)..Clock::block_slot(Hash::WORDS),
            Self::Limbs => Clock::limb_slot(0)..Clock::limb_slot(Ext::LIMBS),
        }
    }
}

/// One instance's `z`, `A·z` and `B·z` from its input words, into zeroed buffers.
pub type InstanceWitness = fn(&[u64], &mut [u64], &mut [u64], &mut [u64]);

/// Eight instances' packed witness by native word arithmetic.
pub type BatchWitness = fn(&[&[u64]; 8], &mut [u64], &mut [u64], &mut [u64]);

/// Register accesses, memory shape, and circuit ports of one instruction class.
pub struct ClassSpec {
    /// Instruction class executed by this table.
    pub class: Class,

    /// Table name used in diagnostics and reports.
    pub name: &'static str,

    /// Whether branches and jumps derive the successor and link value.
    pub control: bool,

    /// Whether the second source register is read, in clock slot 1.
    pub reads_rs2: bool,

    /// Whether the destination register receives a result, in clock slot 3.
    pub writes_rd: bool,

    /// Whether the destination register supplies an address, in clock slot 3.
    pub reads_rd: bool,

    /// Memory accesses made after the register accesses.
    pub ram: Ram,

    /// Whether a doubleword is moved unchanged through a shared column.
    pub copies: bool,

    /// Word-level witness generation, checked against the generic circuit walk.
    pub witness: Option<InstanceWitness>,

    /// Eight-instance witness generation when native arithmetic supports batching.
    pub batch_witness: Option<BatchWitness>,

    /// Base-two logarithm of the class circuit's bits per instance.
    pub k_log: usize,

    /// Circuit port words in order, with inputs before outputs.
    pub ports: &'static [Word],

    /// Number of input ports in the class circuit.
    pub n_inputs: usize,

    /// Base-two logarithm of the clock circuit's bits per instance.
    pub clock_k_log: usize,
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
        witness: None,
        batch_witness: None,
        k_log: 10,
        ports: &[Word::V1, Word::V2, Word::Imm, Word::Flags, Word::Out, Word::Taken],
        n_inputs: 4,
        clock_k_log: 9,
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
        witness: None,
        batch_witness: None,
        k_log: 10,
        ports: &[
            Word::V1,
            Word::Imm,
            Word::Flags,
            Word::Cell(0),
            Word::Address,
            Word::Out,
        ],
        n_inputs: 4,
        clock_k_log: 9,
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
        witness: None,
        batch_witness: None,
        k_log: 10,
        ports: &[
            Word::V1,
            Word::V2,
            Word::Imm,
            Word::Flags,
            Word::Cell(0),
            Word::Address,
            Word::CellNew(0),
        ],
        n_inputs: 5,
        clock_k_log: 9,
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
        witness: None,
        batch_witness: None,
        k_log: 8,
        ports: &[Word::V1, Word::Imm, Word::Address],
        n_inputs: 2,
        clock_k_log: 9,
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
        witness: None,
        batch_witness: None,
        k_log: 8,
        ports: &[Word::V1, Word::Imm, Word::Address],
        n_inputs: 2,
        clock_k_log: 9,
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
        witness: None,
        batch_witness: None,
        k_log: 10,
        ports: &[Word::V1, Word::V2, Word::Imm, Word::Flags, Word::Out],
        n_inputs: 4,
        clock_k_log: 9,
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
        witness: None,
        batch_witness: if cfg!(all(target_arch = "x86_64", target_feature = "avx2")) {
            Some(Mul::witness_batch)
        } else {
            None
        },
        k_log: 12,
        ports: &[Word::V1, Word::V2, Word::Flags, Word::Out],
        n_inputs: 3,
        clock_k_log: 9,
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
        witness: Some(Mulh::witness),
        batch_witness: None,
        k_log: 13,
        ports: &[Word::V1, Word::V2, Word::Flags, Word::Out],
        n_inputs: 3,
        clock_k_log: 9,
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
        witness: None,
        batch_witness: None,
        k_log: 13,
        ports: &[
            Word::V1,
            Word::V2,
            Word::Flags,
            Word::HintQ,
            Word::HintR,
            Word::Out,
            Word::Bad,
        ],
        n_inputs: 5,
        clock_k_log: 9,
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
        witness: Some(rv::circuits::blake2s_witness),
        batch_witness: None,
        k_log: 14,
        ports: &[
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
            Word::CellNew(4),
            Word::CellNew(5),
            Word::CellNew(6),
            Word::CellNew(7),
        ],
        n_inputs: 14,
        clock_k_log: 11,
    };

    /// Extension-field multiplication, optionally accumulating or using a base-field operand.
    pub const EXT: Self = Self {
        class: Class::Ext,
        name: "EXT",
        control: false,
        reads_rs2: true,
        writes_rd: false,
        reads_rd: true,
        ram: Ram::Limbs,
        copies: false,
        witness: None,
        batch_witness: None,
        k_log: 13,
        ports: &[
            Word::V1,
            Word::V2,
            Word::Dest,
            Word::Flags,
            Word::Cell(0),
            Word::Cell(1),
            Word::Cell(2),
            Word::Cell(3),
            Word::Cell(4),
            Word::Cell(5),
            Word::Cell(6),
            Word::Cell(7),
            Word::Cell(8),
            Word::CellNew(6),
            Word::CellNew(7),
            Word::CellNew(8),
            Word::LimbAddress(1),
            Word::LimbAddress(2),
            Word::LimbAddress(4),
            Word::LimbAddress(5),
            Word::LimbAddress(7),
            Word::LimbAddress(8),
            Word::LimbSeparator,
        ],
        n_inputs: 13,
        clock_k_log: 11,
    };

    /// Specifications in protocol order, shared by execution and proving.
    pub const ALL: [&'static Self; N_TABLES] = [
        &Self::ALU,
        &Self::LOAD,
        &Self::STORE,
        &Self::LD,
        &Self::SD,
        &Self::SHIFT,
        &Self::MUL,
        &Self::MULH,
        &Self::DIV,
        &Self::HASH,
        &Self::EXT,
    ];

    /// Check that register accesses and copy semantics match the circuit ports.
    pub(super) fn assert_valid(&self) {
        // Invariant: a register access exists exactly when its value is a circuit word, or a column a doubleword load or store moves.
        assert_eq!(
            self.reads_rs2 && !self.copies,
            self.ports.contains(&Word::V2),
            "{}: rs2 read",
            self.name
        );
        assert_eq!(
            self.writes_rd && !self.copies,
            self.ports.contains(&Word::Out),
            "{}: rd write",
            self.name
        );
        assert_eq!(
            self.reads_rd,
            self.ports.contains(&Word::Dest),
            "{}: rd read",
            self.name
        );
        assert!(
            !(self.reads_rd && self.writes_rd),
            "{}: rd is read or written, not both",
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
                moves && !self.control && !self.reads_rd && self.ports == ports,
                "{}: a copy",
                self.name
            );
        }
    }

    /// Indices of accessed registers, in previous-timestamp column order.
    ///
    /// The indices select the first source, second source, and destination register.
    pub const fn registers(&self) -> &'static [usize] {
        match (self.reads_rs2, self.writes_rd || self.reads_rd) {
            (true, true) => &[0, 1, 2],
            (true, false) => &[0, 1],
            (false, true) => &[0, 2],
            (false, false) => &[0],
        }
    }

    /// Accesses per row: the registers', then RAM's.
    pub const fn n_accesses(&self) -> usize {
        let ram = self.ram.slots();
        self.registers().len() + (ram.end - ram.start) as usize
    }

    /// Smallest power-of-two height accepted by both circuits.
    ///
    /// A batch has at least eight instances and a zerocheck cube of at least 2^13 bits.
    pub const fn min_rows(&self) -> usize {
        1 << class_flock::n_blocks_log(self, 1)
    }

    /// Whether the table can be proven over `rows` rows: a power of two at or above its floor.
    pub const fn is_provable_height(&self, rows: usize) -> bool {
        rows.is_power_of_two() && rows >= self.min_rows()
    }

    /// The clock slots of the row's accesses, in the order of their columns.
    pub fn slots(&self) -> Vec<u32> {
        self.registers()
            .iter()
            .map(|&i| Clock::REG_SLOTS[i])
            .chain(self.ram.slots())
            .collect()
    }

    /// The clock circuit's port words: the clock, each access's previous timestamp, then the step.
    pub fn clock_ports(&self) -> Vec<Word> {
        let prev = (0..self.n_accesses()).map(|i| Word::Prev(i as u8));
        std::iter::once(Word::Clock).chain(prev).chain([Word::Step]).collect()
    }
}

/// Bytecode slot binding a circuit's verdict to a public zero.
///
/// It follows all decoded instruction fields.
pub const BAD_SLOT: usize = 12;

/// Bytecode slot binding the exit selector.
pub const EXIT_SLOT: usize = 13;

/// Number of instruction tables in the proof layout.
pub const N_TABLES: usize = 11;
