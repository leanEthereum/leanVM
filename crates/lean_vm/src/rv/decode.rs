//! The decoder: a 32-bit word at `pc` to its [`Entry`]. Anything rv64im does not
//! define, a reserved encoding included, is [`Entry::ILLEGAL`].

use super::{Class, Entry, SINK, Target, alu, div, hash, load, mul, mulh, shift, store};

/// Sign-extend the low `bits` bits of `x`.
fn sext(x: u32, bits: u32) -> u64 {
    (((x as u64) << (64 - bits)) as i64 >> (64 - bits)) as u64
}

fn entry(class: Class, flags: u64, a1: u32, a2: u32, rd: u32, imm: u64) -> Entry {
    Entry {
        class,
        flags,
        a1: a1 as u8,
        a2: a2 as u8,
        ad: if rd == 0 { SINK } else { rd as u8 },
        imm,
        target: Target::Next,
        link: false,
        jalr: false,
    }
}

pub fn decode(word: u32, pc: u64) -> Entry {
    let (opcode, rd, f3) = (word & 0x7f, (word >> 7) & 31, (word >> 12) & 7);
    let (rs1, rs2, f7) = ((word >> 15) & 31, (word >> 20) & 31, word >> 25);
    let imm_i = sext(word >> 20, 12);
    let imm_s = sext((f7 << 5) | rd, 12);
    let imm_b = sext(
        ((word >> 31) << 12) | (((word >> 7) & 1) << 11) | (((word >> 25) & 0x3f) << 5) | (((word >> 8) & 0xf) << 1),
        13,
    );
    let imm_u = sext(word & 0xffff_f000, 32);
    let imm_j = sext(
        ((word >> 31) << 20)
            | (((word >> 12) & 0xff) << 12)
            | (((word >> 20) & 1) << 11)
            | (((word >> 21) & 0x3ff) << 1),
        21,
    );
    // A register-register and a register-immediate instruction are one entry: the
    // first has no immediate, the second reads `x0`.
    let reg = |class, flags| entry(class, flags, rs1, rs2, rd, 0);
    let imm = |class, flags, imm| entry(class, flags, rs1, 0, rd, imm);

    match opcode {
        // LUI and AUIPC: the constant, added to `x0`.
        0x37 => entry(Class::Alu, 0, 0, 0, rd, imm_u),
        0x17 => entry(Class::Alu, 0, 0, 0, rd, pc.wrapping_add(imm_u)),
        // JAL
        0x6f => Entry {
            target: Target::Abs(pc.wrapping_add(imm_j)),
            link: true,
            ..entry(Class::Alu, alu::ALWAYS, 0, 0, rd, 0)
        },
        // JALR
        0x67 if f3 == 0 => Entry {
            link: true,
            jalr: true,
            ..imm(Class::Alu, alu::CLEAR_BIT0, imm_i)
        },
        // Branches
        0x63 => {
            let when = match f3 {
                0 => alu::BR_EQ,
                1 => alu::BR_NE,
                4 => alu::BR_LT,
                5 => alu::BR_GE,
                6 => alu::BR_LTU,
                7 => alu::BR_GEU,
                _ => return Entry::ILLEGAL,
            };
            Entry {
                target: Target::Abs(pc.wrapping_add(imm_b)),
                ..entry(Class::Alu, alu::SUB | when, rs1, rs2, 0, 0)
            }
        }
        // Loads
        0x03 => {
            let flags = match f3 {
                0..=2 => load::SIGNED | f3 as u64,
                // A 64-bit load has no extension.
                3 => 3,
                4..=6 => (f3 - 4) as u64,
                _ => return Entry::ILLEGAL,
            };
            imm(Class::Load, flags, imm_i)
        }
        // Stores
        0x23 if f3 <= 3 => entry(Class::Store, f3 as u64 & store::LOG_WIDTH, rs1, rs2, 0, imm_s),
        // Register-immediate
        0x13 => match f3 {
            0 => imm(Class::Alu, 0, imm_i),
            2 => imm(Class::Alu, alu::SUB | alu::SEL_LT, imm_i),
            3 => imm(Class::Alu, alu::SUB | alu::SEL_LTU, imm_i),
            4 => imm(Class::Alu, alu::SEL_XOR, imm_i),
            6 => imm(Class::Alu, alu::SEL_OR, imm_i),
            7 => imm(Class::Alu, alu::SEL_AND, imm_i),
            // The shift amount has six bits, so the function field is the other six.
            1 if word >> 26 == 0 => imm(Class::Shift, 0, (word >> 20 & 63) as u64),
            5 if word >> 26 == 0 => imm(Class::Shift, shift::RIGHT, (word >> 20 & 63) as u64),
            5 if word >> 26 == 0x10 => imm(Class::Shift, shift::RIGHT | shift::ARITH, (word >> 20 & 63) as u64),
            _ => Entry::ILLEGAL,
        },
        // Register-immediate, 32-bit: a shift amount of five bits.
        0x1b => match (f3, f7) {
            (0, _) => imm(Class::Alu, alu::WORD, imm_i),
            (1, 0) => imm(Class::Shift, shift::WORD, rs2 as u64),
            (5, 0) => imm(Class::Shift, shift::WORD | shift::RIGHT, rs2 as u64),
            (5, 0x20) => imm(Class::Shift, shift::WORD | shift::RIGHT | shift::ARITH, rs2 as u64),
            _ => Entry::ILLEGAL,
        },
        // Register-register
        0x33 => match (f7, f3) {
            (0, 0) => reg(Class::Alu, 0),
            (0x20, 0) => reg(Class::Alu, alu::SUB),
            (0, 1) => reg(Class::Shift, 0),
            (0, 2) => reg(Class::Alu, alu::SUB | alu::SEL_LT),
            (0, 3) => reg(Class::Alu, alu::SUB | alu::SEL_LTU),
            (0, 4) => reg(Class::Alu, alu::SEL_XOR),
            (0, 5) => reg(Class::Shift, shift::RIGHT),
            (0x20, 5) => reg(Class::Shift, shift::RIGHT | shift::ARITH),
            (0, 6) => reg(Class::Alu, alu::SEL_OR),
            (0, 7) => reg(Class::Alu, alu::SEL_AND),
            (1, 0) => reg(Class::Mul, 0),
            (1, 1) => reg(Class::Mulh, mulh::SIGNED_1 | mulh::SIGNED_2),
            (1, 2) => reg(Class::Mulh, mulh::SIGNED_1),
            (1, 3) => reg(Class::Mulh, 0),
            (1, 4) => reg(Class::Div, div::SIGNED),
            (1, 5) => reg(Class::Div, 0),
            (1, 6) => reg(Class::Div, div::SIGNED | div::REM),
            (1, 7) => reg(Class::Div, div::REM),
            _ => Entry::ILLEGAL,
        },
        // Register-register, 32-bit
        0x3b => match (f7, f3) {
            (0, 0) => reg(Class::Alu, alu::WORD),
            (0x20, 0) => reg(Class::Alu, alu::SUB | alu::WORD),
            (0, 1) => reg(Class::Shift, shift::WORD),
            (0, 5) => reg(Class::Shift, shift::WORD | shift::RIGHT),
            (0x20, 5) => reg(Class::Shift, shift::WORD | shift::RIGHT | shift::ARITH),
            (1, 0) => reg(Class::Mul, mul::WORD),
            (1, 4) => reg(Class::Div, div::WORD | div::SIGNED),
            (1, 5) => reg(Class::Div, div::WORD),
            (1, 6) => reg(Class::Div, div::WORD | div::SIGNED | div::REM),
            (1, 7) => reg(Class::Div, div::WORD | div::REM),
            _ => Entry::ILLEGAL,
        },
        // FENCE: a no-op, whatever its other fields hold.
        0x0f if f3 == 0 => entry(Class::Alu, 0, 0, 0, 0, 0),
        // The BLAKE2s precompile: the block at rs1, the counter in rs2, no destination.
        hash::OPCODE if f7 == 0 && rd == 0 && f3 <= 1 => {
            entry(Class::Hash, if f3 == 1 { hash::FINAL } else { 0 }, rs1, rs2, 0, 0)
        }
        // ECALL: a jump to the halt slot. EBREAK and the CSR instructions are illegal.
        0x73 if word == 0x73 => Entry {
            target: Target::Halt,
            ..entry(Class::Alu, alu::ALWAYS, 0, 0, 0, 0)
        },
        _ => Entry::ILLEGAL,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every entry the decoder can produce is well formed, over a sweep dense in the
    /// fields that select an instruction.
    #[test]
    fn decoded_entries_are_well_formed() {
        for opcode in 0..128u32 {
            for f3 in 0..8u32 {
                for top in 0..(1u32 << 12) {
                    let word = opcode | (f3 << 12) | (top << 20) | (0x15 << 7) | (0x0a << 15);
                    let e = decode(word, super::super::TEXT_BASE);
                    assert!(e.is_well_formed(), "{word:#010x} decodes to {e:?}");
                }
            }
        }
    }

    /// The encodings RV64 reserves among the shifts, and what is not rv64im at all.
    #[test]
    fn reserved_encodings_are_illegal() {
        let illegal = [
            0x0400_1013u32, // SLLI with a function bit set
            0x0200_101b,    // SLLIW with bit 5 of the amount
            0x0200_501b,    // SRLIW with bit 5 of the amount
            0x4200_501b,    // SRAIW with bit 5 of the amount
            0x0010_0073,    // EBREAK
            0x3000_2073,    // CSRRS mstatus
            0x0000_100f,    // FENCE.I
            0x0000_0000,
            0xffff_ffff,
            0x0000_7003,          // a load of width 7
            0x0000_4023,          // a store of width 4
            0x0000_2063,          // a branch with function 2
            0x0000_1067,          // JALR with a nonzero function
            0x0000_208b,          // BLAKE2S with function 2
            0x0000_008b | 5 << 7, // BLAKE2S with a destination
            0x0200_000b,          // BLAKE2S with a function-7 bit set
        ];
        for word in illegal {
            assert_eq!(decode(word, 0), Entry::ILLEGAL, "{word:#010x}");
        }
        // SRAI by 63 is legal on RV64.
        assert_eq!(decode(0x43f5_5513, 0).class, Class::Shift);
    }
}
