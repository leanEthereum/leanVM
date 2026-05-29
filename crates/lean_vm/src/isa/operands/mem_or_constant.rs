use crate::core::F;
use crate::diagnostics::RunnerError;
use crate::execution::memory::MemoryAccess;
use backend::*;
use std::fmt::{Display, Formatter};

/// Represents a value that can be either a constant or memory location
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub enum MemOrConstant {
    /// Direct constant value
    Constant(F),
    /// Memory address relative to frame pointer: m[fp + offset]
    MemoryAfterFp {
        /// Offset from frame pointer
        offset: usize,
    },
}

impl MemOrConstant {
    pub const fn zero() -> Self {
        Self::Constant(F::ZERO)
    }

    pub const fn one() -> Self {
        Self::Constant(F::ONE)
    }

    /// Read the value from memory or return the constant
    pub fn read_value(&self, memory: &impl MemoryAccess, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::Constant(c) => Ok(*c),
            Self::MemoryAfterFp { offset } => memory.get(fp.checked_add(*offset).ok_or(RunnerError::OutOfMemory)?),
        }
    }

    /// Check if the value is unknown (would error when read)
    pub fn is_value_unknown(&self, memory: &impl MemoryAccess, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    /// Get the memory address (returns error for constants)
    pub fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::Constant(_) => Err(RunnerError::NotAPointer),
            Self::MemoryAfterFp { offset } => fp.checked_add(*offset).ok_or(RunnerError::OutOfMemory),
        }
    }
}

impl Display for MemOrConstant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constant(c) => write!(f, "{c}"),
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
        }
    }
}
