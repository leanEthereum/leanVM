//! RISC-V programs, proven and checked by both verifiers.

use super::python_verifier::PythonStatement;
use lean_vm::cpu::{Program, prove, verify, verify_to_raw};
use lean_vm::rv::asm::*;
use lean_vm::rv::{ADVICE_BASE, RAM_BASE, TEXT_BASE};

const STEPS: u64 = 1000;

/// Fibonacci mod 2^64, iteratively, and the output it proves: `a0 = F(STEPS)`.
pub fn fibonacci() -> (Program, [u64; 4]) {
    let text = Asm::new()
        .li(A0, 0)
        .li(A1, 1)
        .li(T0, STEPS)
        .label("loop")
        .r("add", A2, A0, A1)
        .i("addi", A0, A1, 0)
        .i("addi", A1, A2, 0)
        .i("addi", T0, T0, -1)
        .branch("bne", T0, ZERO, "loop")
        .li(A1, 0)
        .li(A2, 0)
        .exit()
        .finish();
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..STEPS {
        (a, b) = (b, a.wrapping_add(b));
    }
    (Program::new(&text, TEXT_BASE, vec![], 2, 0), [a, 0, 0, 0])
}

fn proves_and_verifies(tag: &str, program: &Program, input: [u64; 4], expected: [u64; 4]) {
    proves_and_verifies_with(tag, program, input, &[], expected);
}

fn proves_and_verifies_with(tag: &str, program: &Program, input: [u64; 4], advice: &[u64], expected: [u64; 4]) {
    let (proof, output, _) = prove(program, input, advice, 1).expect("the run halts");
    assert_eq!(output, expected);
    let raw = verify_to_raw(program, &input, &output, &proof).expect("honest proof verifies");
    PythonStatement::new(tag, program, &input, &output).assert_accepts(&raw);

    // The proof is about this input and this output.
    for (wrong_input, wrong_output) in [(1, 0), (0, 1)] {
        let (mut input, mut output) = (input, output);
        input[0] ^= wrong_input;
        output[0] ^= wrong_output;
        assert!(verify(program, &input, &output, &proof).is_err());
    }
}

#[test]
fn fibonacci_proves_and_verifies() {
    let (program, output) = fibonacci();
    proves_and_verifies("fibonacci", &program, [0; 4], output);
}

/// Every instruction of the `ALU` class at least once: the arithmetic and its 32-bit
/// forms, the comparisons, the logic, the constants, all six branches taken and not,
/// and a call and return.
#[test]
fn alu_instructions_prove_and_verify() {
    let mut a = Asm::new();
    // Constants `li` builds without a shift, which is another class's.
    a.li(S0, 0xffff_ffff_8000_0001)
        .li(S1, 0x7fff_ffff)
        .r("add", A0, S0, S1)
        .r("sub", A1, S0, S1)
        .r("addw", A2, S1, S1)
        .r("subw", A3, S0, S1)
        .i("addiw", A4, S1, 1)
        .r("slt", T0, S0, S1)
        .r("sltu", T1, S0, S1)
        .i("slti", T2, S0, -1)
        .i("sltiu", A5, S1, -1)
        .r("and", A6, S0, S1)
        .r("or", A6, A6, T0)
        .r("xor", A6, A6, T1)
        .i("andi", T0, S1, 0x555)
        .i("ori", T0, T0, -0x800)
        .i("xori", T0, T0, 0x2aa)
        .r("add", A0, A0, T0)
        .r("add", A0, A0, T2)
        .r("add", A0, A0, A5)
        .lui(T0, 0xfffff)
        .auipc(T1, 0x12345)
        .r("add", A1, A1, T0)
        .r("add", A1, A1, T1);
    // Each branch twice, operands swapped, so that one of the two is taken. A branch
    // taken skips an increment of a4.
    for (i, op) in ["beq", "bne", "blt", "bge", "bltu", "bgeu"].into_iter().enumerate() {
        for (j, (x, y)) in [(S0, S1), (S1, S0)].into_iter().enumerate() {
            let label: &'static str = Box::leak(format!("skip{i}{j}").into_boxed_str());
            a.branch(op, x, y, label).i("addi", A4, A4, 1).label(label);
        }
    }
    a.jal(RA, "double")
        .jal(RA, "double")
        .li(A3, 0)
        .exit()
        .label("double")
        .r("add", A2, A2, A2)
        .r("add", A4, A4, A4)
        .jalr(ZERO, RA, 0);
    let program = Program::new(&a.finish(), TEXT_BASE, vec![], 2, 0);
    let expected = lean_vm::rv::Machine::new(&program.rv, [0; 4], &[])
        .run(1 << 20)
        .expect("the run halts");
    assert_ne!(expected, [0; 4]);
    proves_and_verifies("alu", &program, [0; 4], expected);
}

/// Every load and store, through a stack frame and over the program's image: a
/// bubble sort of eight words in place, then a checksum of the sorted bytes read back
/// at every width, signed and not, and the public input folded in.
#[test]
fn loads_and_stores_prove_and_verify() {
    const LOG_RAM: usize = 6;
    const DATA: u64 = RAM_BASE + 8 * 4;
    let image = vec![5u64, 3, 0xffff_ffff_ffff_fff9, 1, 8, 0x8877_6655_4433_2211, 7, 4];
    let mut a = Asm::new();
    a.li(SP, RAM_BASE + (8 << LOG_RAM))
        .li(A0, DATA)
        .jal(RA, "sort")
        .li(T0, DATA)
        .load("ld", A0, 56, T0)
        .load("lw", T1, 56, T0)
        .r("add", A0, A0, T1)
        .load("lwu", T1, 60, T0)
        .r("add", A0, A0, T1)
        .load("lh", T1, 62, T0)
        .r("add", A0, A0, T1)
        .load("lhu", T1, 58, T0)
        .r("add", A0, A0, T1)
        .load("lb", T1, 63, T0)
        .r("add", A0, A0, T1)
        .load("lbu", T1, 57, T0)
        .r("add", A0, A0, T1)
        // Narrow stores into the first sorted word, then the public input.
        .store("sb", T1, 1, T0)
        .store("sh", T1, 2, T0)
        .store("sw", T1, 4, T0)
        .load("ld", A1, 0, T0)
        .li(T0, RAM_BASE)
        .load("ld", A2, 0, T0)
        .load("ld", A3, 24, T0)
        .exit()
        .label("sort")
        .i("addi", SP, SP, -16)
        .store("sd", RA, 8, SP)
        .li(T2, 7)
        .label("outer")
        .i("addi", T0, A0, 0)
        .i("addi", T1, T2, 0)
        .label("inner")
        .load("ld", A2, 0, T0)
        .load("ld", A3, 8, T0)
        .branch("bgeu", A3, A2, "ordered")
        .store("sd", A3, 0, T0)
        .store("sd", A2, 8, T0)
        .label("ordered")
        .i("addi", T0, T0, 8)
        .i("addi", T1, T1, -1)
        .branch("bne", T1, ZERO, "inner")
        .i("addi", T2, T2, -1)
        .branch("bne", T2, ZERO, "outer")
        .load("ld", RA, 8, SP)
        .i("addi", SP, SP, 16)
        .jalr(ZERO, RA, 0);
    let program = Program::new(&a.finish(), TEXT_BASE, image, LOG_RAM, 0);
    let input = [0x1111, 0x2222, 0x3333, 0x4444];
    let expected = lean_vm::rv::Machine::new(&program.rv, input, &[])
        .run(1 << 20)
        .expect("the run halts");
    assert_eq!(expected[2..], [0x1111, 0x4444], "the public input is RAM's first words");
    proves_and_verifies("memory", &program, input, expected);
}

/// Every shift and every multiplication, registers and immediates, 64-bit and 32-bit
/// forms, folded into the output.
#[test]
fn shifts_and_multiplications_prove_and_verify() {
    let mut a = Asm::new();
    a.li(S0, 0x8765_4321_fedc_ba98).li(S1, 0xffff_ffff_0000_0025);
    for (i, op) in [
        "sll", "srl", "sra", "sllw", "srlw", "sraw", "mul", "mulh", "mulhsu", "mulhu", "mulw",
    ]
    .into_iter()
    .enumerate()
    {
        a.r(op, T0, S0, S1)
            .r("xor", A0, A0, T0)
            .i("addi", A1, A1, i as i32 + 1)
            .r("add", A1, A1, T0);
    }
    for (op, amount) in [
        ("slli", 63),
        ("srli", 1),
        ("srai", 40),
        ("slliw", 31),
        ("srliw", 0),
        ("sraiw", 17),
    ] {
        a.i(op, T0, S0, amount).r("xor", A2, A2, T0).r("sub", A3, A3, T0);
    }
    let program = Program::new(&a.exit().finish(), TEXT_BASE, vec![], 2, 0);
    let expected = lean_vm::rv::Machine::new(&program.rv, [0; 4], &[])
        .run(1 << 20)
        .expect("the run halts");
    assert!(expected.iter().all(|&word| word != 0));
    proves_and_verifies("shift-mul", &program, [0; 4], expected);
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
        a.li(S0, n).li(S1, d);
        for op in ["div", "divu", "rem", "remu", "divw", "divuw", "remw", "remuw"] {
            a.r(op, T0, S0, S1)
                .r("xor", A0, A0, T0)
                .r("add", A1, A1, T0)
                .r("sub", A2, A2, A1);
        }
    }
    let program = Program::new(&a.exit().finish(), TEXT_BASE, vec![], 2, 0);
    let expected = lean_vm::rv::Machine::new(&program.rv, [0; 4], &[])
        .run(1 << 20)
        .expect("the run halts");
    proves_and_verifies("div", &program, [0; 4], expected);
}

/// BLAKE2s of 100 bytes through the precompile: two compressions of the block at
/// `RAM_BASE + 128`, the chaining value copied forward between them and the second
/// message block loaded from the image, checked against the host's hash.
#[test]
fn blake2s_precompile_proves_and_verifies() {
    use lean_vm::rv::hash::{H, M, OUT};
    const BLOCK: u64 = RAM_BASE + 128;
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
    let mut image = vec![0u64; ((BLOCK - RAM_BASE) / 8 - 4) as usize];
    image.extend(&iv);
    image.extend([0; 4]);
    image.extend(words(&data[..64]));
    image.extend(words(&data[64..]));
    let second = BLOCK + 128;

    let mut a = Asm::new();
    a.li(S0, BLOCK).li(S1, 64).blake2s(S0, S1, false);
    for k in 0..4 {
        a.load("ld", T0, (OUT + 8 * k) as i32, S0)
            .store("sd", T0, (H + 8 * k) as i32, S0);
    }
    a.li(T1, second);
    for k in 0..8 {
        a.load("ld", T0, 8 * k, T1)
            .store("sd", T0, (M + 8 * k as u64) as i32, S0);
    }
    a.li(S1, data.len() as u64).blake2s(S0, S1, true);
    for (i, reg) in [A0, A1, A2, A3].into_iter().enumerate() {
        a.load("ld", reg, (OUT + 8 * i as u64) as i32, S0);
    }
    let program = Program::new(&a.exit().finish(), TEXT_BASE, image, 7, 0);
    let expected: [u64; 4] = words(&primitives::hash::hash(&data))[..4].try_into().unwrap();
    proves_and_verifies("blake2s", &program, [0; 4], expected);

    // A block pointer that is no word address traps, like a misaligned load.
    let text = Asm::new().li(S0, BLOCK + 4).blake2s(S0, ZERO, true).exit().finish();
    let program = Program::new(&text, TEXT_BASE, vec![], 7, 0);
    assert_eq!(
        prove(&program, [0; 4], &[], 1).err(),
        Some(lean_vm::rv::Trap::Misaligned {
            pc: TEXT_BASE + 8,
            address: BLOCK + 4
        })
    );
}

/// The advice region: words the prover supplies, read and written like RAM, which the
/// statement says nothing about, so one program proves a different output per advice.
#[test]
fn advice_proves_and_verifies() {
    const LOG_ADVICE: usize = 3;
    let mut a = Asm::new();
    a.li(T0, ADVICE_BASE)
        .load("ld", A0, 0, T0)
        .load("ld", T1, 8, T0)
        .r("add", A0, A0, T1)
        .load("lw", A1, 20, T0)
        .store("sd", A0, 56, T0)
        .load("ld", A2, 56, T0)
        .li(A3, 0)
        .exit();
    let program = Program::new(&a.finish(), TEXT_BASE, vec![], 2, LOG_ADVICE);
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
        proves_and_verifies_with("advice", &program, [0; 4], &advice, expected);
    }
    // Past the region is nowhere, like past RAM.
    let text = Asm::new()
        .li(T0, ADVICE_BASE + (8 << LOG_ADVICE))
        .load("ld", A0, 0, T0)
        .exit()
        .finish();
    let program = Program::new(&text, TEXT_BASE, vec![], 2, LOG_ADVICE);
    assert!(matches!(
        prove(&program, [0; 4], &[], 1).err(),
        Some(lean_vm::rv::Trap::Unmapped { .. })
    ));
}

/// A run that traps has no proof, and says why.
#[test]
fn a_trap_is_reported() {
    let text = Asm::new().word(0x0010_0073).exit().finish();
    let program = Program::new(&text, TEXT_BASE, vec![], 2, 0);
    assert_eq!(
        prove(&program, [0; 4], &[], 1).err(),
        Some(lean_vm::rv::Trap::Illegal { pc: TEXT_BASE })
    );
}
