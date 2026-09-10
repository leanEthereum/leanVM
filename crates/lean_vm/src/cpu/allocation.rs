//! Experimental witness allocation in public intervals. This does not establish ZK.

use std::ops::Range;

#[derive(Clone, Debug)]
pub struct AllocationLayout {
    runs: Vec<Range<u32>>,
    slot: u32,
}

impl AllocationLayout {
    /// Ordered, disjoint, slot-aligned half-open intervals. All other addresses
    /// are unavailable to allocation, but direct accesses are not checked here.
    pub fn new(runs: Vec<Range<u32>>, slot: u32) -> Self {
        assert!(slot.is_power_of_two() && !runs.is_empty());
        assert!(
            runs.iter().all(|run| {
                run.start < run.end && run.start % slot == 0 && run.end % slot == 0 && run.end <= 1 << 28
            })
        );
        assert!(runs.windows(2).all(|pair| pair[0].end <= pair[1].start));
        Self { runs, slot }
    }

    /// Next-fit allocation, counting even an empty object as one slot. No object
    /// is reclaimed. Failure does not advance the cursor.
    pub fn allocate(&self, cursor: &mut u32, size: u32) -> Option<u32> {
        let rounded = size.max(1).checked_add(self.slot - 1)? & !(self.slot - 1);
        for run in &self.runs {
            let start = (*cursor).max(run.start).checked_add(self.slot - 1)? & !(self.slot - 1);
            let end = start.checked_add(rounded)?;
            if end <= run.end {
                *cursor = end;
                return Some(start);
            }
        }
        None
    }

    pub(crate) fn first(&self) -> u32 {
        self.runs[0].start
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next_fit_preserves_gaps_and_failed_cursor() {
        let layout = AllocationLayout::new(vec![256..1024, 2048..2816], 256);
        let mut cursor = 0;
        assert_eq!(layout.allocate(&mut cursor, 257), Some(256));
        assert_eq!(layout.allocate(&mut cursor, 257), Some(2048));
        assert_eq!(layout.allocate(&mut cursor, 0), Some(2560));
        assert_eq!(layout.allocate(&mut cursor, 1), None);
        assert_eq!(cursor, 2816);
        assert_eq!(layout.allocate(&mut cursor, u32::MAX), None);
        assert_eq!(cursor, 2816);
    }

    #[test]
    fn exclusive_end_does_not_grow_memory() {
        use std::collections::HashMap;

        use crate::cpu::{DerefMode, Op, Program, hints::RHint};
        use primitives::field::{F192, g_pow};

        let mut code = vec![
            Op::Set { o: 3, k: F192::ONE },
            Op::Deref {
                o1: 2,
                o2: 511,
                o3: 3,
                mode: DerefMode::Cell,
            },
            Op::Set {
                o: 4,
                k: F192::from(g_pow(7)),
            },
            Op::Jump { oc: 3, od: 4, of: 3 },
        ];
        code.resize(8, Op::Set { o: 0, k: F192::ZERO });
        let mut program = Program::assemble(code, HashMap::from([(1, vec![RHint::Alloc { ptr: 2, size: 512 }])]), 5);
        let runs = std::iter::once(((1 << 17) - 512)..(1 << 17)).collect();
        program.set_allocation_layout(AllocationLayout::new(runs, 256));
        let execution = program.execute([F192::ZERO; 2]);
        assert_eq!(execution.mem.len(), 1 << 17);
        assert_eq!(execution.mem[(1 << 17) - 1], F192::ONE);
        assert!(execution.unconstrained_reads.is_empty());
    }

    #[test]
    #[should_panic(expected = "entry frame overlaps")]
    fn public_inputs_are_reserved_even_with_an_empty_entry_frame() {
        use crate::cpu::{Op, Program};
        use primitives::field::F192;

        let mut program = Program::from_bytecode(vec![Op::Set { o: 0, k: F192::ZERO }; 2], 0);
        let runs = std::iter::once(0..256).collect();
        program.set_allocation_layout(AllocationLayout::new(runs, 256));
    }
}
