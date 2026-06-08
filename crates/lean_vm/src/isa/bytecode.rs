//! Bytecode representation and management

use backend::*;

use crate::{DIMENSION, F, FileId, FunctionName, Hint, N_INSTRUCTION_COLUMNS, SourceLocation};

use super::Instruction;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeEntry {
    pub hints: Box<[Hint]>, // executed before the instruction
    pub instruction: Instruction,
}

/// `instructions_multilinear`, `hash`, and `ending_pc` must be checked at initialization to match `code`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bytecode {
    pub unpadded_size: usize,
    pub code: Vec<CodeEntry>, // assumed to be well-formed
    pub hint_name_to_index: BTreeMap<String, usize>,
    pub instructions_multilinear: Vec<F>,
    pub starting_frame_memory: usize,
    pub ending_pc: usize, // Must equal `code.len() - 1`.
    pub hash: [F; DIGEST_ELEMS],
    // debug
    pub function_locations: BTreeMap<SourceLocation, FunctionName>,
    pub filepaths: BTreeMap<FileId, String>,
    pub source_code: BTreeMap<FileId, String>,
    /// Maps each pc to its source location (for error reporting)
    pub pc_to_location: Vec<SourceLocation>,
}

impl Bytecode {
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
