//! RISC-V (rv64im) as the VM sees it.
//!
//! The program is public, so each instruction word is decoded once, before any run.
//!
//! A table never decodes an instruction.
//! It reads the fields of the decoded entry instead.
//!
//! A run goes through four stages:
//!
//! - an ELF file, or the assembler, gives a guest's instruction words;
//! - decoding them gives a program of entries;
//! - a machine runs the program on its registers and memory;
//! - each executed instruction is one step, which becomes one table row.
//!
//! The parts, leaves first:
//!
//! - the address space: three regions of words at fixed bases;
//! - the registers and the exit convention;
//! - the instruction set: encodings, typed operations, classes, decoded entries;
//! - the semantics: what each class computes, as pure functions;
//! - the program and the interpreter that runs it;
//! - the circuits: each class's function as a Boolean gate list;
//! - the assembler and the ELF loader, which produce programs.

pub mod asm;
pub mod circuits;
pub mod elf;
pub mod machine;

mod entry;
mod instruction;
mod program;
mod region;
mod register;
mod semantics;

pub use circuits::ClassCircuit;
pub use elf::{ElfError, Guest};
pub use entry::{Class, Entry, Target};
pub use instruction::{BranchOp, ImmOp, Instruction, LoadOp, Opcode, RegOp, ShiftOp, StoreOp};
pub use machine::{Machine, Trap};
pub use program::{Program, ProgramError};
pub use region::Region;
pub use register::{Reg, RegisterFile, Syscall};
pub use semantics::{
    Alu, BlockAccess, Div, Hash, InstructionClass, Load, Mul, Mulh, Outcome, Shift, Store, WordAccess,
};
