//! `keccak(head, out, words=run)`: Keccak-256 (the EVM's `keccak256`) of whole
//! cells, one block up to 128 bytes and the 136-byte-rate sponge past that, where
//! odd blocks start mid-cell and lane 16 carries message data. Every case is
//! checked against [`primitives::keccak::keccak256`] by execution, and the
//! multi-block shapes the SPHINCS+ verifier hashes are also proven.

use lean_compiler::{compile, parse};
use lean_vm::cpu::{prove, verify};
use primitives::field::F192;

/// One message cell as the test writes it: a hinted data cell, a known zero, or
/// the all-ones constant.
#[derive(Clone, Copy)]
enum Cell {
    Data(usize),
    Zero,
    Ones,
}

fn cell_value(data: &[F192], c: Cell) -> F192 {
    match c {
        Cell::Data(i) => data[i],
        Cell::Zero => F192::ZERO,
        Cell::Ones => F192::new(u64::MAX, u64::MAX, 0),
    }
}

fn cell_bytes(v: F192) -> [u8; 16] {
    let mut out = [0; 16];
    out[..8].copy_from_slice(&v.c0.to_le_bytes());
    out[8..].copy_from_slice(&v.c1.to_le_bytes());
    out
}

fn data_cells(n: usize) -> Vec<F192> {
    (0..n as u64)
        .map(|i| {
            F192::new(
                i.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x0123,
                (i + 7).wrapping_mul(0xC2B2_AE3D_27D4_EB4F),
                0,
            )
        })
        .collect()
}

/// A program hashing `head ‖ words(data[w0..w1])` with the digest as its public
/// output, and that digest computed natively.
fn case(head: &[Cell], words: Option<(usize, usize)>, heap_words: bool) -> (String, Vec<F192>, [F192; 2]) {
    let n_data = head
        .iter()
        .filter_map(|c| if let Cell::Data(i) = c { Some(i + 1) } else { None })
        .chain(words.map(|(_, hi)| hi))
        .max()
        .unwrap_or(0)
        .max(1);
    let data = data_cells(n_data);
    let mut bytes = Vec::new();
    for c in head {
        bytes.extend(cell_bytes(cell_value(&data, *c)));
    }
    if let Some((lo, hi)) = words {
        for v in &data[lo..hi] {
            bytes.extend(cell_bytes(*v));
            bytes.extend([0u8; 16]);
        }
    }
    let d = primitives::keccak::keccak256(&bytes);
    let word = |o: usize| u64::from_le_bytes(d[o..o + 8].try_into().unwrap());
    let digest = [F192::new(word(0), word(8), 0), F192::new(word(16), word(24), 0)];

    let head_src: Vec<String> = head
        .iter()
        .map(|c| match c {
            Cell::Data(i) => format!("data[GEN ** {i}]"),
            Cell::Zero => "0".into(),
            Cell::Ones => format!("{}", u128::MAX),
        })
        .collect();
    let mut src =
        format!("def main():\n    data = HeapBuf(GEN ** {n_data})\n    hint_witness(data[0:{n_data}], \"data\")\n");
    let words_kw = match words {
        None => String::new(),
        Some((lo, hi)) if heap_words => format!(", words=data[{lo}:{hi}]"),
        Some((lo, hi)) => {
            src.push_str(&format!("    ws = StackBuf({})\n", hi - lo));
            for k in 0..hi - lo {
                src.push_str(&format!("    ws[{k}] = data[GEN ** {}]\n", lo + k));
            }
            ", words=ws".into()
        }
    };
    src.push_str(&format!(
        "    out = StackBuf(2)\n    keccak([{}], out{words_kw})\n    p = 1\n    p[1] = out[0]\n    p[GEN] = out[1]\n    return\n",
        head_src.join(", ")
    ));
    (src, data, digest)
}

fn run(head: &[Cell], words: Option<(usize, usize)>, heap_words: bool, prove_it: bool) {
    let (src, data, digest) = case(head, words, heap_words);
    let mut program = compile(&parse(&src).unwrap_or_else(|e| panic!("{e}\n{src}")));
    program.set_witness("data", vec![data]);
    let execution = program.execute(digest);
    assert!(execution.unconstrained_reads.is_empty(), "{src}");
    let wrong = [digest[0] + F192::ONE, digest[1]];
    assert!(
        std::panic::catch_unwind(|| program.execute(wrong)).is_err(),
        "a wrong digest must not execute:\n{src}"
    );
    if prove_it {
        let (proof, _) = prove(&program, digest, lean_vm::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &digest, &proof).expect("keccak proof verifies");
    }
}

use Cell::{Data, Ones, Zero};

/// The single-block shapes: `F` (96 bytes) and `H` (128, the padding byte in lane 16).
#[test]
fn single_block_hashes() {
    run(&[Data(0), Zero, Data(1), Data(2), Data(3), Zero], None, false, false);
    run(
        &[Data(0), Zero, Data(1), Data(2), Data(3), Zero, Data(4), Zero],
        None,
        false,
        false,
    );
    run(&[Data(0)], None, false, false);
    run(&[Data(0), Zero], Some((1, 4)), false, false);
}

/// `H_msg`: 112 bytes, one block, the all-ones domain word first.
#[test]
fn message_digest_shape() {
    run(
        &[Ones, Ones, Data(0), Data(1), Data(2), Data(3), Data(4)],
        None,
        false,
        true,
    );
}

/// A head alone past one block: 160 bytes, two blocks, a constant cell split
/// across lane 16.
#[test]
fn two_block_head() {
    let head = [
        Data(0),
        Zero,
        Data(1),
        Zero,
        Data(2),
        Zero,
        Data(3),
        Data(4),
        Ones,
        Ones,
    ];
    run(&head, None, false, true);
}

/// The FORS roots (672 bytes, the last block's padding byte in lane 16) and a WOTS
/// key (1184 bytes), words from a stack run and from a heap slice.
#[test]
fn compression_shapes() {
    let prefix = [Data(0), Zero, Data(1), Data(2)];
    run(&prefix, Some((3, 22)), false, true);
    run(&prefix, Some((3, 38)), true, true);
    run(&prefix, Some((3, 38)), false, false);
}

/// Dense messages at and around the block boundaries: 144 bytes, exactly two and
/// four blocks (the last block all padding), and odd cell counts.
#[test]
fn dense_messages_across_block_boundaries() {
    for n in [9usize, 16, 17, 18, 25, 34, 35, 51] {
        let head: Vec<Cell> = (0..n).map(Data).collect();
        run(&head, None, false, false);
    }
    let mixed: Vec<Cell> = (0..20)
        .map(|i| {
            if i % 3 == 0 {
                Zero
            } else if i % 5 == 0 {
                Ones
            } else {
                Data(i)
            }
        })
        .collect();
    run(&mixed, None, false, false);
}

/// A cell that enters only as split lanes is never read whole by the opcode; a
/// top limb there must still fail execution rather than be dropped from the
/// hash. (The split's `K` check is what pins a *hinted* limb; honest witness
/// generation cannot poke that hint, so this case only covers the input.)
#[test]
fn a_split_cell_must_be_canonical() {
    // Block 1 starts mid cell 8, so cells 8 and 9 enter as lanes.
    let head: Vec<Cell> = (0..10).map(Data).collect();
    let (src, mut data, digest) = case(&head, None, false);
    let program = |data: Vec<F192>| {
        let mut p = compile(&parse(&src).unwrap());
        p.set_witness("data", vec![data]);
        p
    };
    assert!(program(data.clone()).execute(digest).unconstrained_reads.is_empty());
    data[9].c2 = 1;
    let p = program(data);
    assert!(std::panic::catch_unwind(|| p.execute(digest)).is_err());
}
