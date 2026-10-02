//! The padding rows: what fills each table from its height up to the power of two it
//! is proven over (doc §sec:jagged).
//!
//! A table is proven over `2^tau` rows, at least flock's instance floor, while the run
//! fills only its first `height` of them. The rest repeat one row, which the bus leaves
//! out (its blocks take the identity there) and the commitment stores once
//! ([`crate::cpu::committed_rows`]). Flock still proves every row's instance, so that
//! row has to be an honest one: a no-op of the table's class at clock zero, on zero
//! registers, which the text carries for the purpose ([`append_noops`]).

use crate::rv::Class;
use crate::rv::asm::{Addi, Divu, Instruction, Lb, Mul, Mulhu, Opcode, Reg, Sb, Slli};
use crate::tables::{CLASSES, N_TABLES};

/// A no-op of `class`: every register is `x0`.
fn nop(class: Class) -> u32 {
    let instruction = match class {
        Class::Alu => Addi.encode(Reg::ZERO, Reg::ZERO, 0),
        // A load and a store of the byte at address zero, which nothing executes.
        Class::Load => Lb.encode(Reg::ZERO, Reg::ZERO, 0),
        Class::Store => Sb.encode(Reg::ZERO, Reg::ZERO, 0),
        Class::Shift => Slli.encode(Reg::ZERO, Reg::ZERO, 0),
        Class::Mul => Mul.encode(Reg::ZERO, Reg::ZERO, Reg::ZERO),
        Class::Mulh => Mulhu.encode(Reg::ZERO, Reg::ZERO, Reg::ZERO),
        Class::Div => Divu.encode(Reg::ZERO, Reg::ZERO, Reg::ZERO),
        // A compression of the block at address zero, which nothing executes.
        Class::Hash => Instruction::r(Opcode::Custom0, 0, 0, Reg::ZERO, Reg::ZERO, Reg::ZERO),
        Class::Illegal => unreachable!("no padding row of an illegal entry"),
    };
    instruction.bits()
}

/// Whether a text of `words` instructions still leaves room, inside the text region,
/// for the illegal word and the no-ops [`crate::cpu::Program::new`] appends, and for
/// the pad to a power of two ([`crate::rv::Program::new`]).
pub fn text_fits(words: usize) -> bool {
    words
        .checked_add(N_TABLES + 3)
        .and_then(usize::checked_next_power_of_two)
        .is_some_and(|total| total <= 1 << crate::rv::MAX_LOG_TEXT)
}

/// Append one no-op per table to `text`, returning where each landed: the entry its
/// padding rows read.
pub fn append_noops(text: &mut Vec<u32>) -> [usize; N_TABLES] {
    std::array::from_fn(|t| {
        text.push(nop(CLASSES[t].class));
        text.len() - 1
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_capacity_reserves_the_padding_entries() {
        let limit = (1 << crate::rv::MAX_LOG_TEXT) - N_TABLES - 3;
        assert!(text_fits(limit));
        assert!(!text_fits(limit + 1));
        assert!(!text_fits(usize::MAX));
        assert!(!text_fits(usize::MAX - N_TABLES - 3));
    }
}
