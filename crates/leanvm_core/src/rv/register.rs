//! The integer registers, the register file and the exit convention.

/// An integer register, `x0` to `x31`.
///
/// The type makes a register impossible to confuse with an immediate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Reg(u8);

impl Reg {
    /// `x0`: always reads zero.
    pub const ZERO: Self = Self(0);
    /// `x1`: the return address.
    pub const RA: Self = Self(1);
    /// `x2`: the stack pointer.
    pub const SP: Self = Self(2);
    /// `x3`: the global pointer.
    pub const GP: Self = Self(3);
    /// `x4`: the thread pointer.
    pub const TP: Self = Self(4);
    /// `x5`: a temporary.
    pub const T0: Self = Self(5);
    /// `x6`: a temporary.
    pub const T1: Self = Self(6);
    /// `x7`: a temporary.
    pub const T2: Self = Self(7);
    /// `x8`: a saved register, also the frame pointer.
    pub const S0: Self = Self(8);
    /// `x9`: a saved register.
    pub const S1: Self = Self(9);
    /// `x10`: an argument, and the first return value.
    pub const A0: Self = Self(10);
    /// `x11`: an argument, and the second return value.
    pub const A1: Self = Self(11);
    /// `x12`: an argument.
    pub const A2: Self = Self(12);
    /// `x13`: an argument.
    pub const A3: Self = Self(13);
    /// `x14`: an argument.
    pub const A4: Self = Self(14);
    /// `x15`: an argument.
    pub const A5: Self = Self(15);
    /// `x16`: an argument.
    pub const A6: Self = Self(16);
    /// `x17`: an argument, and the system call number.
    pub const A7: Self = Self(17);
    /// `x18`: a saved register.
    pub const S2: Self = Self(18);
    /// `x19`: a saved register.
    pub const S3: Self = Self(19);
    /// `x20`: a saved register.
    pub const S4: Self = Self(20);
    /// `x21`: a saved register.
    pub const S5: Self = Self(21);
    /// `x22`: a saved register.
    pub const S6: Self = Self(22);
    /// `x23`: a saved register.
    pub const S7: Self = Self(23);
    /// `x24`: a saved register.
    pub const S8: Self = Self(24);
    /// `x25`: a saved register.
    pub const S9: Self = Self(25);
    /// `x26`: a saved register.
    pub const S10: Self = Self(26);
    /// `x27`: a saved register.
    pub const S11: Self = Self(27);
    /// `x28`: a temporary.
    pub const T3: Self = Self(28);
    /// `x29`: a temporary.
    pub const T4: Self = Self(29);
    /// `x30`: a temporary.
    pub const T5: Self = Self(30);
    /// `x31`: a temporary.
    pub const T6: Self = Self(31);

    /// The register holding the system call number at `ecall`.
    pub const SYSCALL: Self = Self::A7;

    /// The registers whose final values are the run's public output.
    pub const OUTPUTS: [Self; 4] = [Self::A0, Self::A1, Self::A2, Self::A3];

    /// The number of integer registers.
    pub const COUNT: usize = 32;

    /// Register `x{index}`.
    ///
    /// Returns `None` for an index of 32 or more.
    pub const fn new(index: u8) -> Option<Self> {
        if (index as usize) < Self::COUNT {
            Some(Self(index))
        } else {
            None
        }
    }

    /// The register's number, below 32.
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// The register file: `x0` to `x31`, then the sink, then unused cells up to a power of two.
///
/// The sink is the cell an instruction with no destination writes.
///
/// No instruction reads it, so a write to `x0` goes there and `x0` stays zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisterFile([u64; RegisterFile::CELLS]);

impl RegisterFile {
    /// The sink's cell, right after the last register.
    pub const SINK: u8 = Reg::COUNT as u8;

    /// The cells: the registers and the sink, rounded up to a power of two.
    pub const CELLS: usize = (Reg::COUNT + 1).next_power_of_two();

    /// The base-two logarithm of the cells.
    pub const LOG_CELLS: usize = Self::CELLS.trailing_zeros() as usize;

    /// A register file of zeros, as a run starts.
    pub fn new() -> Self {
        Self([0; Self::CELLS])
    }

    /// Every cell.
    pub fn cells(&self) -> &[u64; Self::CELLS] {
        &self.0
    }

    /// The value of register `r`.
    pub fn get(&self, r: Reg) -> u64 {
        self.0[r.index()]
    }

    /// Write `value` to register `r`.
    pub fn set(&mut self, r: Reg, value: u64) {
        self.0[r.index()] = value;
    }

    /// The value of cell `cell`, as a decoded entry names it.
    pub(super) fn read(&self, cell: u8) -> u64 {
        self.0[cell as usize]
    }

    /// Write `value` to cell `cell`, and return what it held.
    pub(super) fn replace(&mut self, cell: u8, value: u64) -> u64 {
        std::mem::replace(&mut self.0[cell as usize], value)
    }
}

impl Default for RegisterFile {
    fn default() -> Self {
        Self::new()
    }
}

/// A system call: what `ecall` asks for, by the number in its syscall register.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Syscall {
    /// End the run, its output in the output registers.
    Exit,
}

impl Syscall {
    /// The call's number, as on Linux.
    pub const fn number(self) -> u64 {
        match self {
            Self::Exit => 93,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::arbitrary::Arbitrary;
    use proptest::strategy::{Map, Strategy};
    use std::ops::Range;

    /// Any register, for property tests.
    impl Arbitrary for Reg {
        type Parameters = ();
        type Strategy = Map<Range<u8>, fn(u8) -> Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (0u8..32).prop_map(Self)
        }
    }

    #[test]
    fn new_accepts_exactly_the_32_registers() {
        // x0..x31 round-trip through their index.
        for index in 0..32u8 {
            assert_eq!(Reg::new(index).map(Reg::index), Some(index as usize));
        }

        // Cell 32 is the sink, which is no register.
        assert_eq!(Reg::new(32), None);
        assert_eq!(Reg::new(u8::MAX), None);
    }
}
