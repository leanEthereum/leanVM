//! RISC-V programs, proven and checked by both verifiers.

use super::python_verifier::PythonStatement;
use leanvm_core::cpu::{Program, ProveError};
use leanvm_core::pcs::Rate;
use leanvm_core::rv::Region;
use leanvm_core::rv::asm::*;

const STEPS: u64 = 1000;

/// Fibonacci mod 2^64, iteratively, and the output it proves: `a0 = F(STEPS)`.
pub fn fibonacci() -> (Program, [u64; 4]) {
    let text = Asm::new()
        .li(Reg::A0, 0)
        .li(Reg::A1, 1)
        .li(Reg::T0, STEPS)
        .label("loop")
        .r(Add, Reg::A2, Reg::A0, Reg::A1)
        .i(Addi, Reg::A0, Reg::A1, 0)
        .i(Addi, Reg::A1, Reg::A2, 0)
        .i(Addi, Reg::T0, Reg::T0, -1)
        .branch(Bne, Reg::T0, Reg::ZERO, "loop")
        .li(Reg::A1, 0)
        .li(Reg::A2, 0)
        .exit()
        .finish();
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..STEPS {
        (a, b) = (b, a.wrapping_add(b));
    }
    (
        Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program"),
        [a, 0, 0, 0],
    )
}

fn proves_and_verifies(tag: &str, program: &Program, expected: [u64; 4]) {
    proves_and_verifies_with(tag, program, &[], expected);
}

fn proves_and_verifies_with(tag: &str, program: &Program, advice: &[u64], expected: [u64; 4]) {
    let (proof, output, _) = program.prove(advice, Rate::MIN).expect("the run halts");
    assert_eq!(output, expected);
    let raw = program.verify_to_raw(&output, &proof).expect("honest proof verifies");
    PythonStatement::new(tag, program, &output).assert_accepts(&raw);

    // The proof is about this output.
    let mut wrong = output;
    wrong[0] ^= 1;
    assert!(program.verify(&wrong, &proof).is_err());
}

#[test]
fn fibonacci_proves_and_verifies() {
    let (program, output) = fibonacci();
    proves_and_verifies("fibonacci", &program, output);
}

/// Every instruction of the `ALU` class at least once: the arithmetic and its 32-bit
/// forms, the comparisons, the logic, the constants, all six branches taken and not,
/// and a call and return.
#[test]
fn alu_instructions_prove_and_verify() {
    let mut a = Asm::new();
    // Constants `li` builds without a shift, which is another class's.
    a.li(Reg::S0, 0xffff_ffff_8000_0001)
        .li(Reg::S1, 0x7fff_ffff)
        .r(Add, Reg::A0, Reg::S0, Reg::S1)
        .r(Sub, Reg::A1, Reg::S0, Reg::S1)
        .r(Addw, Reg::A2, Reg::S1, Reg::S1)
        .r(Subw, Reg::A3, Reg::S0, Reg::S1)
        .i(Addiw, Reg::A4, Reg::S1, 1)
        .r(Slt, Reg::T0, Reg::S0, Reg::S1)
        .r(Sltu, Reg::T1, Reg::S0, Reg::S1)
        .i(Slti, Reg::T2, Reg::S0, -1)
        .i(Sltiu, Reg::A5, Reg::S1, -1)
        .r(And, Reg::A6, Reg::S0, Reg::S1)
        .r(Or, Reg::A6, Reg::A6, Reg::T0)
        .r(Xor, Reg::A6, Reg::A6, Reg::T1)
        .i(Andi, Reg::T0, Reg::S1, 0x555)
        .i(Ori, Reg::T0, Reg::T0, -0x800)
        .i(Xori, Reg::T0, Reg::T0, 0x2aa)
        .r(Add, Reg::A0, Reg::A0, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::T2)
        .r(Add, Reg::A0, Reg::A0, Reg::A5)
        .lui(Reg::T0, 0xfffff)
        .auipc(Reg::T1, 0x12345)
        .r(Add, Reg::A1, Reg::A1, Reg::T0)
        .r(Add, Reg::A1, Reg::A1, Reg::T1);
    // Each branch twice, operands swapped, so that one of the two is taken. A branch
    // taken skips an increment of a4.
    for (i, op) in BranchOp::ALL.into_iter().enumerate() {
        for (j, (x, y)) in [(Reg::S0, Reg::S1), (Reg::S1, Reg::S0)].into_iter().enumerate() {
            let label: &'static str = Box::leak(format!("skip{i}{j}").into_boxed_str());
            a.branch(op, x, y, label).i(Addi, Reg::A4, Reg::A4, 1).label(label);
        }
    }
    a.jal(Reg::RA, "double")
        .jal(Reg::RA, "double")
        .li(Reg::A3, 0)
        .exit()
        .label("double")
        .r(Add, Reg::A2, Reg::A2, Reg::A2)
        .r(Add, Reg::A4, Reg::A4, Reg::A4)
        .jalr(Reg::ZERO, Reg::RA, 0);
    let program = Program::new(&a.finish(), Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
    let expected = leanvm_core::rv::Machine::new(program.rv(), &[])
        .run()
        .expect("the run halts");
    assert_ne!(expected, [0; 4]);
    proves_and_verifies("alu", &program, expected);
}

/// Every load and store, through a stack frame and over the program's image: a
/// bubble sort of eight words in place, then a checksum of the sorted bytes read back
/// at every width, signed and not.
#[test]
fn loads_and_stores_prove_and_verify() {
    const LOG_RAM: usize = 6;
    const DATA: u64 = Region::RAM.base();
    let image = vec![5u64, 3, 0xffff_ffff_ffff_fff9, 1, 8, 0x8877_6655_4433_2211, 7, 4];
    let mut a = Asm::new();
    a.li(Reg::SP, Region::RAM.base() + (8 << LOG_RAM))
        .li(Reg::A0, DATA)
        .jal(Reg::RA, "sort")
        .li(Reg::T0, DATA)
        .load(Ld, Reg::A0, 56, Reg::T0)
        .load(Lw, Reg::T1, 56, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::T1)
        .load(Lwu, Reg::T1, 60, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::T1)
        .load(Lh, Reg::T1, 62, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::T1)
        .load(Lhu, Reg::T1, 58, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::T1)
        .load(Lb, Reg::T1, 63, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::T1)
        .load(Lbu, Reg::T1, 57, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::T1)
        // Narrow stores into the first sorted word.
        .store(Sb, Reg::T1, 1, Reg::T0)
        .store(Sh, Reg::T1, 2, Reg::T0)
        .store(Sw, Reg::T1, 4, Reg::T0)
        .load(Ld, Reg::A1, 0, Reg::T0)
        .exit()
        .label("sort")
        .i(Addi, Reg::SP, Reg::SP, -16)
        .store(Sd, Reg::RA, 8, Reg::SP)
        .li(Reg::T2, 7)
        .label("outer")
        .i(Addi, Reg::T0, Reg::A0, 0)
        .i(Addi, Reg::T1, Reg::T2, 0)
        .label("inner")
        .load(Ld, Reg::A2, 0, Reg::T0)
        .load(Ld, Reg::A3, 8, Reg::T0)
        .branch(Bgeu, Reg::A3, Reg::A2, "ordered")
        .store(Sd, Reg::A3, 0, Reg::T0)
        .store(Sd, Reg::A2, 8, Reg::T0)
        .label("ordered")
        .i(Addi, Reg::T0, Reg::T0, 8)
        .i(Addi, Reg::T1, Reg::T1, -1)
        .branch(Bne, Reg::T1, Reg::ZERO, "inner")
        .i(Addi, Reg::T2, Reg::T2, -1)
        .branch(Bne, Reg::T2, Reg::ZERO, "outer")
        .load(Ld, Reg::RA, 8, Reg::SP)
        .i(Addi, Reg::SP, Reg::SP, 16)
        .jalr(Reg::ZERO, Reg::RA, 0);
    let program = Program::new(&a.finish(), Region::TEXT.base(), image, LOG_RAM, 0).expect("valid instruction program");
    let expected = leanvm_core::rv::Machine::new(program.rv(), &[])
        .run()
        .expect("the run halts");
    proves_and_verifies("memory", &program, expected);
}

/// Every shift and every multiplication, registers and immediates, 64-bit and 32-bit
/// forms, folded into the output.
#[test]
fn shifts_and_multiplications_prove_and_verify() {
    let mut a = Asm::new();
    a.li(Reg::S0, 0x8765_4321_fedc_ba98).li(Reg::S1, 0xffff_ffff_0000_0025);
    for (i, op) in [Sll, Srl, Sra, Sllw, Srlw, Sraw, Mul, Mulh, Mulhsu, Mulhu, Mulw]
        .into_iter()
        .enumerate()
    {
        a.r(op, Reg::T0, Reg::S0, Reg::S1)
            .r(Xor, Reg::A0, Reg::A0, Reg::T0)
            .i(Addi, Reg::A1, Reg::A1, i as i32 + 1)
            .r(Add, Reg::A1, Reg::A1, Reg::T0);
    }
    for (op, amount) in [(Slli, 63), (Srli, 1), (Srai, 40), (Slliw, 31), (Srliw, 0), (Sraiw, 17)] {
        a.shift(op, Reg::T0, Reg::S0, amount)
            .r(Xor, Reg::A2, Reg::A2, Reg::T0)
            .r(Sub, Reg::A3, Reg::A3, Reg::T0);
    }
    let program =
        Program::new(&a.exit().finish(), Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
    let expected = leanvm_core::rv::Machine::new(program.rv(), &[])
        .run()
        .expect("the run halts");
    assert!(expected.iter().all(|&word| word != 0));
    proves_and_verifies("shift-mul", &program, expected);
}

/// Every division and remainder, 64-bit and 32-bit, on operands of both signs, by zero,
/// and the one that overflows.
#[test]
fn divisions_prove_and_verify() {
    let mut a = Asm::new();
    let operands = [
        (0x8765_4321_fedc_ba98u64, 0xffff_ffff_ffff_ff85u64),
        (1_000_000_007, 13),
        (5, 0),
        (i64::MIN as u64, u64::MAX),
        (0xffff_ffff_8000_0000, 0xffff_ffff_ffff_ffff),
    ];
    for (n, d) in operands {
        a.li(Reg::S0, n).li(Reg::S1, d);
        for op in [Div, Divu, Rem, Remu, Divw, Divuw, Remw, Remuw] {
            a.r(op, Reg::T0, Reg::S0, Reg::S1)
                .r(Xor, Reg::A0, Reg::A0, Reg::T0)
                .r(Add, Reg::A1, Reg::A1, Reg::T0)
                .r(Sub, Reg::A2, Reg::A2, Reg::A1);
        }
    }
    let program =
        Program::new(&a.exit().finish(), Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
    let expected = leanvm_core::rv::Machine::new(program.rv(), &[])
        .run()
        .expect("the run halts");
    proves_and_verifies("div", &program, expected);
}

#[test]
fn blake2s_precompile_proves_and_verifies() {
    use leanvm_core::rv::Hash;
    // Hash 100 bytes in two compressions, using a block 128 bytes into RAM.
    const BLOCK: u64 = Region::RAM.base() + 128;
    let data: Vec<u8> = (0..100u32).map(|i| (i * 37 + 11) as u8).collect();
    let words = |bytes: &[u8]| -> Vec<u64> {
        let mut padded = bytes.to_vec();
        padded.resize(64, 0);
        padded
            .chunks(8)
            .map(|w| u64::from_le_bytes(w.try_into().unwrap()))
            .collect()
    };
    let iv: Vec<u64> = primitives::hash::PARAM_IV
        .chunks(2)
        .map(|w| w[0] as u64 | (w[1] as u64) << 32)
        .collect();
    // The image: the block (its chaining value seeded, its message the first 64 bytes),
    // then the second message block.
    let mut image = vec![0u64; ((BLOCK - Region::RAM.base()) / 8) as usize];
    image.extend(&iv);
    image.extend([0; 4]);
    image.extend(words(&data[..64]));
    image.extend(words(&data[64..]));
    let second = BLOCK + 128;

    let mut a = Asm::new();
    a.li(Reg::S0, BLOCK).li(Reg::S1, 64).blake2s(Reg::S0, Reg::S1, false);
    for k in 0..4 {
        a.load(Ld, Reg::T0, (Hash::OUT + 8 * k) as i32, Reg::S0)
            .store(Sd, Reg::T0, (Hash::H + 8 * k) as i32, Reg::S0);
    }
    a.li(Reg::T1, second);
    for k in 0..8 {
        a.load(Ld, Reg::T0, 8 * k, Reg::T1)
            .store(Sd, Reg::T0, (Hash::M + 8 * k as u64) as i32, Reg::S0);
    }
    a.li(Reg::S1, data.len() as u64).blake2s(Reg::S0, Reg::S1, true);
    for (i, reg) in [Reg::A0, Reg::A1, Reg::A2, Reg::A3].into_iter().enumerate() {
        a.load(Ld, reg, (Hash::OUT + 8 * i as u64) as i32, Reg::S0);
    }
    let program =
        Program::new(&a.exit().finish(), Region::TEXT.base(), image, 7, 0).expect("valid instruction program");
    let expected: [u64; 4] = words(&primitives::hash::hash(&data))[..4].try_into().unwrap();
    proves_and_verifies("blake2s", &program, expected);

    // A block pointer that is no word address traps, like a misaligned load.
    let text = Asm::new()
        .li(Reg::S0, BLOCK + 4)
        .blake2s(Reg::S0, Reg::ZERO, true)
        .exit()
        .finish();
    let program = Program::new(&text, Region::TEXT.base(), vec![], 7, 0).expect("valid instruction program");
    assert_eq!(
        program.prove(&[], Rate::MIN).err(),
        Some(ProveError::Trap(leanvm_core::rv::Trap::Misaligned {
            pc: Region::TEXT.base() + 8,
            address: BLOCK + 4
        }))
    );
}

/// The advice region: words the prover supplies, read and written like RAM, which the
/// statement says nothing about, so one program proves a different output per advice.
#[test]
fn advice_proves_and_verifies() {
    const LOG_ADVICE: usize = 3;
    let mut a = Asm::new();
    a.li(Reg::T0, Region::ADVICE.base())
        .load(Ld, Reg::A0, 0, Reg::T0)
        .load(Ld, Reg::T1, 8, Reg::T0)
        .r(Add, Reg::A0, Reg::A0, Reg::T1)
        .load(Lw, Reg::A1, 20, Reg::T0)
        .store(Sd, Reg::A0, 56, Reg::T0)
        .load(Ld, Reg::A2, 56, Reg::T0)
        .li(Reg::A3, 0)
        .exit();
    let program =
        Program::new(&a.finish(), Region::TEXT.base(), vec![], 2, LOG_ADVICE).expect("valid instruction program");
    for advice in [
        vec![3, 4, 0xdead_beef_0000_0005u64],
        vec![u64::MAX, 1, 0xffff_ffff_ffff_ffff, 9, 9, 9, 9, 9],
    ] {
        let expected = [
            advice[0].wrapping_add(advice[1]),
            (advice[2] >> 32) as i32 as i64 as u64,
            advice[0].wrapping_add(advice[1]),
            0,
        ];
        proves_and_verifies_with("advice", &program, &advice, expected);
    }
    // Past the region is nowhere, like past RAM.
    let text = Asm::new()
        .li(Reg::T0, Region::ADVICE.base() + (8 << LOG_ADVICE))
        .load(Ld, Reg::A0, 0, Reg::T0)
        .exit()
        .finish();
    let program = Program::new(&text, Region::TEXT.base(), vec![], 2, LOG_ADVICE).expect("valid instruction program");
    assert!(matches!(
        program.prove(&[], Rate::MIN).err(),
        Some(ProveError::Trap(leanvm_core::rv::Trap::Unmapped { .. }))
    ));
}

/// A run that traps has no proof, and says why.
#[test]
fn a_trap_is_reported() {
    let text = Asm::new().word(0x0010_0073).exit().finish();
    let program = Program::new(&text, Region::TEXT.base(), vec![], 2, 0).expect("valid instruction program");
    assert_eq!(
        program.prove(&[], Rate::MIN).err(),
        Some(ProveError::Trap(leanvm_core::rv::Trap::Illegal {
            pc: Region::TEXT.base()
        }))
    );
}
