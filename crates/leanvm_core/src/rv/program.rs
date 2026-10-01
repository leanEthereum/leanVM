//! A decoded program: its text, its entry point, and its memory sizes.

use super::entry::{Entry, Target};
use super::region::Region;

/// A decoded program.
///
/// It is read-only once built, so what is proven is what was checked.
#[derive(Clone, Debug)]
pub struct Program {
    /// A power of two of entries, instruction `i` at the text's word `i`.
    ///
    /// The last slot is the halt slot.
    ///
    /// It and every slot past the supplied text are illegal.
    entries: Vec<Entry>,
    /// Where the run starts.
    entry_pc: u64,
    /// RAM's first words; the rest are zero.
    image: Vec<u64>,
    /// RAM holds 2^log_ram words.
    log_ram: usize,
    /// The advice holds 2^log_advice words.
    log_advice: usize,
}

/// Why words, an entry point and sizes form no program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ProgramError {
    /// The text leaves no room in its region for the padding and the halt slot.
    #[error("the text leaves no room for padding and the halt slot")]
    TextTooLarge,
    /// The entry point is misaligned, or outside the supplied text.
    #[error("the entry point is not an aligned instruction in the supplied text")]
    EntryPoint,
    /// RAM is smaller than its image, or larger than its region.
    #[error("RAM is too small for its image, or exceeds its region")]
    RamSize,
    /// The advice is larger than its region.
    #[error("the advice exceeds its region")]
    AdviceSize,
    /// A decoded entry breaks the bytecode table's rules.
    #[error("the decoded text contains a malformed entry")]
    MalformedEntry,
}

impl Program {
    /// Decode `text`, checking the entry point and the sizes first.
    ///
    /// A word rv64im does not define is kept as an illegal entry, which traps when reached.
    ///
    /// # Errors
    ///
    /// Returns the first rule the inputs break.
    pub fn new(
        text: &[u32],
        entry_pc: u64,
        image: Vec<u64>,
        log_ram: usize,
        log_advice: usize,
    ) -> Result<Self, ProgramError> {
        // Check the shape before allocating anything sized by it.
        Self::validate(text.len(), entry_pc, image.len(), log_ram, log_advice)?;

        // Decode each word at its own address.
        let mut entries: Vec<Entry> = text
            .iter()
            .enumerate()
            .map(|(i, &word)| Entry::decode(word, Region::TEXT.address(i)))
            .collect();

        // Pad to a power of two that leaves at least one illegal slot, then the halt slot.
        //
        //     [ text ... | illegal ... | halt ]
        entries.resize((text.len() + 2).next_power_of_two(), Entry::ILLEGAL);

        // The decoder only makes well-formed entries, which the bytecode table's rules restate.
        if !entries.iter().all(Entry::is_well_formed) {
            return Err(ProgramError::MalformedEntry);
        }
        Ok(Self {
            entries,
            entry_pc,
            image,
            log_ram,
            log_advice,
        })
    }

    /// Check a program's shape from its sizes alone.
    ///
    /// # Errors
    ///
    /// Returns the first rule the shape breaks.
    pub(crate) fn validate(
        text_words: usize,
        entry_pc: u64,
        image_words: usize,
        log_ram: usize,
        log_advice: usize,
    ) -> Result<(), ProgramError> {
        // The text, one illegal slot and the halt slot fit the region.
        if text_words > (1 << Region::TEXT.max_log_words()) - 2 {
            return Err(ProgramError::TextTooLarge);
        }

        // The entry point is an aligned instruction of the supplied text.
        let offset = entry_pc
            .checked_sub(Region::TEXT.base())
            .ok_or(ProgramError::EntryPoint)?;
        if !offset.is_multiple_of(4) || offset / 4 >= text_words as u64 {
            return Err(ProgramError::EntryPoint);
        }

        // RAM holds its image and fits its region; the advice fits its region.
        if log_ram > Region::RAM.max_log_words() || image_words > 1 << log_ram {
            return Err(ProgramError::RamSize);
        }
        if log_advice > Region::ADVICE.max_log_words() {
            return Err(ProgramError::AdviceSize);
        }
        Ok(())
    }

    /// The decoded text, the illegal padding and the halt slot included.
    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }

    /// The address of the first instruction run.
    pub const fn entry_pc(&self) -> u64 {
        self.entry_pc
    }

    /// RAM's initialized words; the rest of RAM starts at zero.
    pub fn image(&self) -> &[u64] {
        &self.image
    }

    /// The base-two logarithm of RAM's size in words.
    pub const fn log_ram(&self) -> usize {
        self.log_ram
    }

    /// The base-two logarithm of the advice's size in words.
    pub const fn log_advice(&self) -> usize {
        self.log_advice
    }

    /// The address of entry `index`.
    pub const fn pc_of(&self, index: usize) -> u64 {
        Region::TEXT.address(index)
    }

    /// The entry at `pc`.
    ///
    /// Returns `None` for an address that is misaligned or past the entries.
    pub fn index_of(&self, pc: u64) -> Option<usize> {
        let log_entries = self.entries.len().trailing_zeros() as usize;
        pc.is_multiple_of(4)
            .then(|| Region::TEXT.index(pc, log_entries))
            .flatten()
    }

    /// Where a run ends: the last slot, which is never executed.
    pub const fn halt_pc(&self) -> u64 {
        self.pc_of(self.entries.len() - 1)
    }

    /// Where entry `index` goes when its class takes the jump.
    ///
    /// Returns `None` for an entry with no fixed target.
    pub fn target_of(&self, index: usize) -> Option<u64> {
        match self.entries[index].target {
            Target::Next => None,
            Target::Abs(target) => Some(target),
            Target::Halt => Some(self.halt_pc()),
        }
    }

    /// The bytecode's jump field: a taken entry's target, XORed with `pc + 4`.
    ///
    /// Zero for an entry with no fixed target.
    ///
    /// The table then forms the next `pc` as `pc + 4 + taken * dt`, the sum in the field being XOR.
    pub fn dt_of(&self, index: usize) -> u64 {
        self.target_of(index)
            .map_or(0, |target| target ^ self.pc_of(index).wrapping_add(4))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::{MAX_LOG_ADVICE, MAX_LOG_RAM, MAX_LOG_TEXT, TEXT_BASE};
    use proptest::prelude::*;

    #[test]
    fn validate_refuses_each_broken_rule() {
        // One broken rule per row, every other input valid.
        for (words, entry, image, ram, advice, error) in [
            (0, TEXT_BASE, 0, 0, 0, ProgramError::EntryPoint),
            (1, 0, 0, 0, 0, ProgramError::EntryPoint),
            (1, TEXT_BASE + 2, 0, 0, 0, ProgramError::EntryPoint),
            (1, TEXT_BASE + 4, 0, 0, 0, ProgramError::EntryPoint),
            (1, u64::MAX, 0, 0, 0, ProgramError::EntryPoint),
            (usize::MAX, TEXT_BASE, 0, 0, 0, ProgramError::TextTooLarge),
            ((1 << MAX_LOG_TEXT) - 1, TEXT_BASE, 0, 0, 0, ProgramError::TextTooLarge),
            (1, TEXT_BASE, 2, 0, 0, ProgramError::RamSize),
            (1, TEXT_BASE, 0, usize::MAX, 0, ProgramError::RamSize),
            (1, TEXT_BASE, 0, MAX_LOG_RAM + 1, 0, ProgramError::RamSize),
            (1, TEXT_BASE, 0, 0, usize::MAX, ProgramError::AdviceSize),
            (1, TEXT_BASE, 0, 0, MAX_LOG_ADVICE + 1, ProgramError::AdviceSize),
        ] {
            assert_eq!(Program::validate(words, entry, image, ram, advice), Err(error));
        }

        // Every size at its largest is accepted, without allocating any of it.
        let largest = Program::validate(
            (1 << MAX_LOG_TEXT) - 2,
            TEXT_BASE,
            1 << MAX_LOG_RAM,
            MAX_LOG_RAM,
            MAX_LOG_ADVICE,
        );
        assert_eq!(largest, Ok(()));
    }

    proptest! {
        #[test]
        fn any_words_decode_to_a_padded_well_formed_text(text in proptest::collection::vec(any::<u32>(), 1..=16), raw_entry in any::<usize>()) {
            // Fixture: random words, and an entry point on one of them.
            let entry = TEXT_BASE + 4 * (raw_entry % text.len()) as u64;
            let program = Program::new(&text, entry, vec![], 0, 0).unwrap();

            // A power of two of well-formed entries.
            let entries = program.entries();
            prop_assert!(entries.len().is_power_of_two());
            prop_assert!(entries.iter().all(Entry::is_well_formed));

            // Each word decoded at its own address, then illegal padding to the end.
            for (i, &word) in text.iter().enumerate() {
                prop_assert_eq!(entries[i], Entry::decode(word, program.pc_of(i)));
            }
            prop_assert!(entries[text.len()..].iter().all(|&e| e == Entry::ILLEGAL));
        }

        #[test]
        fn index_of_inverts_pc_of(len in 1usize..64, raw in any::<usize>(), delta in 1u64..4) {
            // Fixture: a text of `len` no-ops.
            let program = Program::new(&vec![0x13; len], TEXT_BASE, vec![], 0, 0).unwrap();
            let index = raw % program.entries().len();

            // Each slot's address maps back to it; a misaligned one maps nowhere.
            prop_assert_eq!(program.index_of(program.pc_of(index)), Some(index));
            prop_assert_eq!(program.index_of(program.pc_of(index) + delta), None);
        }
    }

    #[test]
    fn index_of_refuses_addresses_outside_the_text() {
        // Fixture: one instruction, padded to four slots.
        let program = Program::new(&[0x13], TEXT_BASE, vec![], 0, 0).unwrap();
        assert_eq!(program.entries().len(), 4);

        // Below the text, past its last slot, and far away.
        for pc in [TEXT_BASE - 4, TEXT_BASE + 16, 0, u64::MAX - 3] {
            assert_eq!(program.index_of(pc), None, "{pc:#x}");
        }
    }
}
