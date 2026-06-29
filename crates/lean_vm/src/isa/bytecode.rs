//! Bytecode representation and management

use backend::*;

use crate::{DIMENSION, F, FileId, FunctionName, Hint, N_INSTRUCTION_COLUMNS, PUBLIC_INPUT_LEN, SourceLocation};

use super::Instruction;
use super::encoder::field_representation;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeEntry {
    pub hints: Box<[Hint]>, // executed before the instruction
    pub instruction: Instruction,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BytecodeDebugInfo {
    pub function_locations: BTreeMap<SourceLocation, FunctionName>,
    pub filepaths: BTreeMap<FileId, String>,
    pub source_code: BTreeMap<FileId, String>,
    /// Maps each pc to its source location
    pub pc_to_location: Vec<SourceLocation>,
}

/// `instructions_multilinear`, `hash`, and `ending_pc` must be checked at initialization to match `code`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bytecode {
    unpadded_size: usize,
    code: Vec<CodeEntry>,
    hint_name_to_index: BTreeMap<String, usize>,
    instructions_multilinear: Vec<F>,
    /// Public read-only values loaded after the fixed public input before execution.
    read_only_data: Vec<F>,
    starting_frame_memory: usize,
    ending_pc: usize, // always `code.len() - 1`
    hash: [F; DIGEST_ELEMS],
    debug_info: BytecodeDebugInfo,
}

impl Bytecode {
    pub fn new(
        code: Vec<CodeEntry>,
        unpadded_size: usize,
        starting_frame_memory: usize,
        hint_name_to_index: BTreeMap<String, usize>,
        debug_info: BytecodeDebugInfo,
    ) -> Self {
        assert!(
            code.len().is_power_of_two(),
            "bytecode must be padded to a power of two"
        );
        assert!(unpadded_size <= code.len());
        assert_eq!(debug_info.pc_to_location.len(), code.len());

        let encoded: Vec<[F; N_INSTRUCTION_COLUMNS]> =
            parallel::par_map_collect(code.len(), |i| field_representation(&code[i].instruction));
        let row_width = N_INSTRUCTION_COLUMNS.next_power_of_two();
        let mut instructions_multilinear = F::zero_vec(code.len() * row_width);
        for (row, fields) in instructions_multilinear.chunks_exact_mut(row_width).zip(&encoded) {
            row[..N_INSTRUCTION_COLUMNS].copy_from_slice(fields);
        }
        let hash = poseidon_hash_slice(&instructions_multilinear);
        let ending_pc = code.len() - 1;

        Self {
            unpadded_size,
            code,
            hint_name_to_index,
            instructions_multilinear,
            read_only_data: Vec::new(),
            starting_frame_memory,
            ending_pc,
            hash,
            debug_info,
        }
    }

    /// Number of instructions before padding to a power of two.
    #[inline]
    pub fn unpadded_size(&self) -> usize {
        self.unpadded_size
    }

    #[inline]
    pub fn code(&self) -> &[CodeEntry] {
        &self.code
    }

    #[inline]
    pub fn instructions_multilinear(&self) -> &[F] {
        &self.instructions_multilinear
    }

    /// Returns the absolute memory address at which the read-only segment begins.
    pub const fn read_only_data_start(&self) -> usize {
        PUBLIC_INPUT_LEN
    }

    /// Returns the public read-only values bound to this bytecode.
    pub fn read_only_data(&self) -> &[F] {
        &self.read_only_data
    }

    /// Attaches public read-only data and binds it into the bytecode hash.
    pub fn with_read_only_data(mut self, mut data: Vec<F>) -> Self {
        data.resize(data.len().next_multiple_of(DIGEST_ELEMS), F::ZERO);
        self.read_only_data = data;
        self.refresh_hash();
        self
    }

    /// Constructs the power-of-two public memory prefix checked by the proof.
    pub fn public_memory(&self, public_input: &[F; PUBLIC_INPUT_LEN]) -> Vec<F> {
        let mut memory = Vec::with_capacity(self.public_memory_len());
        memory.extend_from_slice(public_input);
        memory.extend_from_slice(&self.read_only_data);
        memory.resize(self.public_memory_len(), F::ZERO);
        memory
    }

    /// Returns the padded public-memory length without allocating the segment.
    pub fn public_memory_len(&self) -> usize {
        (PUBLIC_INPUT_LEN + self.read_only_data.len()).next_power_of_two()
    }

    /// Recomputes the Fiat-Shamir bytecode hash after read-only data changes.
    fn refresh_hash(&mut self) {
        let instruction_hash = poseidon_hash_slice(&self.instructions_multilinear);
        self.hash = if self.read_only_data.is_empty() {
            instruction_hash
        } else {
            let data_hash = poseidon_hash_slice(&self.read_only_data);
            poseidon16_compress_pair(&instruction_hash, &data_hash)
        };
    }

    #[inline]
    pub fn starting_frame_memory(&self) -> usize {
        self.starting_frame_memory
    }

    #[inline]
    pub fn ending_pc(&self) -> usize {
        self.ending_pc
    }

    /// Poseidon (sponge) hash of `instructions_multilinear`; binds the Fiat-Shamir transcript to the program.
    #[inline]
    pub fn hash(&self) -> &[F; DIGEST_ELEMS] {
        &self.hash
    }

    #[inline]
    pub fn n_hint_slots(&self) -> usize {
        self.hint_name_to_index.len()
    }

    #[inline]
    pub fn debug_info(&self) -> &BytecodeDebugInfo {
        &self.debug_info
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.code.len()
    }

    pub fn padded_size(&self) -> usize {
        self.size().next_power_of_two()
    }

    pub fn log_size(&self) -> usize {
        log2_ceil_usize(self.size())
    }

    pub fn hint_slot(&self, name: &str) -> usize {
        *self
            .hint_name_to_index
            .get(name)
            .unwrap_or_else(|| panic!("hint '{name}' is not declared by the program"))
    }

    pub fn cumulated_n_vars(&self) -> usize {
        self.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS)
    }

    pub fn bytecode_claim_size(&self) -> usize {
        (self.cumulated_n_vars() + 1) * DIMENSION
    }
}

impl Display for Bytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (pc, entry) in self.code.iter().enumerate() {
            for hint in entry.hints.iter() {
                if !matches!(hint, Hint::LocationReport { .. }) {
                    writeln!(f, "hint: {hint}")?;
                }
            }
            writeln!(f, "{pc:>4}: {}", entry.instruction)?;
        }
        Ok(())
    }
}
