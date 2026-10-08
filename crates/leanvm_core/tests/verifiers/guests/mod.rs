//! Rust guests (`programs/*/guest`), from their ELF files: compiled by `rustc` for
//! `riscv64im-unknown-none-elf`, loaded, run, proven, and checked by the native verifier.
//! The files are built by `programs/build.sh` and checked in, the target needing a
//! nightly toolchain.

use leanvm::{ElfError, Guest, Machine, Program, ProvenRun, Prover, Rate, Region};
use leanvm_guest::PublicValues;
use primitives::hash::{digest_words, hash};

/// The output of a guest committing `values` in order.
fn committed(values: &[&[u64]]) -> [u64; 4] {
    let mut public = PublicValues::new();
    for &word in values.iter().copied().flatten() {
        public.commit(&word);
    }
    public.digest()
}

fn proves_and_verifies(tag: &str, elf: &[u8], advice: &[u64], expected: [u64; 4]) {
    let program = Program::from_elf(elf).expect("a guest");
    let ran = Machine::new(program.rv(), advice).run().expect("the run halts");
    assert_eq!(ran, expected, "{tag}: the interpreter");

    let ProvenRun {
        proof, output, stats, ..
    } = Prover::new(Rate::MIN).prove(&program, advice).expect("the run halts");
    assert_eq!(output, expected);
    // Measuring a run reports what proving it does, without the proof.
    assert_eq!(program.measure(advice), Ok(stats.clone()), "{tag}: measure");
    program.verify(output, &proof).expect("honest proof verifies");
    let mut wrong = *output.words();
    wrong[3] ^= 1;
    assert!(program.verify(wrong.into(), &proof).is_err());
    println!(
        "{tag}: {} instructions, {}",
        program.rv().entries().len(),
        stats.details()
    );
}

#[test]
fn fibonacci_guest() {
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..5000 {
        (a, b) = (b, a.wrapping_add(b));
    }
    proves_and_verifies(
        "fibonacci",
        include_bytes!("../../../../../programs/fibonacci/fibonacci.elf"),
        &[5000],
        committed(&[&[5000, a]]),
    );
}

/// BLAKE2s-256 in plain Rust on the VM, against the prover's own BLAKE2s: shifts,
/// rotations, 32-bit arithmetic, byte loads and stores, a message that is not a whole
/// number of blocks.
#[test]
fn blake2s_guest() {
    let length = 150u64;
    let message: Vec<u8> = (0..length).map(|i| (i % 251) as u8).collect();
    proves_and_verifies(
        "blake2s",
        include_bytes!("../../../../../programs/blake2s/blake2s.elf"),
        &[length],
        committed(&[&[length], &digest_words(&hash(&message))]),
    );
}

/// The same digest through the `blake2s` instruction, from the runtime's hasher: the
/// precompile as a guest reaches it, on a message of several blocks.
#[test]
fn hash_guest() {
    let length = 1000u64;
    let message: Vec<u8> = (0..length).map(|i| (i % 251) as u8).collect();
    proves_and_verifies(
        "hash",
        include_bytes!("../../../../../programs/hash/hash.elf"),
        &[length],
        committed(&[&[length], &digest_words(&hash(&message))]),
    );
}

/// The lengths a block-based hash gets wrong: nothing, one byte, and the exact
/// multiples of the block either side. Proving each would cost minutes, so these run on
/// the interpreter, which is what the proofs above are checked against anyway.
#[test]
fn the_hash_guests_agree_with_the_host_at_every_block_boundary() {
    let guests = [
        (
            "blake2s",
            include_bytes!("../../../../../programs/blake2s/blake2s.elf").as_slice(),
        ),
        (
            "hash",
            include_bytes!("../../../../../programs/hash/hash.elf").as_slice(),
        ),
    ];
    for (name, elf) in guests {
        let program = Program::from_elf(elf).expect("a guest");
        for length in [0u64, 1, 55, 63, 64, 65, 127, 128, 129, 256] {
            let message: Vec<u8> = (0..length).map(|i| (i % 251) as u8).collect();
            let expected = committed(&[&[length], &digest_words(&hash(&message))]);
            let ran = Machine::new(program.rv(), &[length])
                .run()
                .unwrap_or_else(|trap| panic!("{name} on {length} bytes: {trap}"));
            assert_eq!(ran, expected, "{name} on {length} bytes");
        }
    }
}

/// A digest of a message only the prover has: the advice region, read through the
/// runtime, and the precompile on it.
#[test]
fn preimage_guest() {
    let message: Vec<u8> = (0..300u32).map(|i| (i * 7 + 3) as u8).collect();
    let mut advice = vec![message.len() as u64];
    advice.extend(message.chunks(8).map(|chunk| {
        let mut word = [0u8; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        u64::from_le_bytes(word)
    }));
    proves_and_verifies(
        "preimage",
        include_bytes!("../../../../../programs/preimage/preimage.elf"),
        &advice,
        committed(&[&digest_words(&hash(&message))]),
    );
}

/// Multiplications and divisions as `rustc` emits them, 128-bit arithmetic included.
#[test]
fn numbers_guest() {
    let (base, exponent, modulus) = (0x1234_5678_9abc_def1u64, 65_537u64, 0xffff_ffff_0000_0001u64);
    let pow_mod = {
        let (mut result, mut b, mut e) = (1u128, base as u128 % modulus as u128, exponent);
        while e > 0 {
            if e & 1 == 1 {
                result = result * b % modulus as u128;
            }
            b = b * b % modulus as u128;
            e >>= 1;
        }
        result as u64
    };
    let gcd = {
        let (mut a, mut b) = (base, modulus);
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    let signed = (base as i64).wrapping_neg() / (exponent as i64 | 1);
    let mixed = ((base as i32) / (exponent as i32 | 1)) as i64 % 1000;
    proves_and_verifies(
        "numbers",
        include_bytes!("../../../../../programs/numbers/numbers.elf"),
        &[base, exponent, modulus],
        committed(&[&[base, exponent, modulus], &[pow_mod, gcd, signed as u64, mixed as u64]]),
    );
}

/// What is not a guest is refused by name, not run.
#[test]
fn malformed_elf_files_are_refused() {
    let elf = include_bytes!("../../../../../programs/fibonacci/fibonacci.elf");
    assert!(Guest::from_elf(elf).is_ok());
    assert!(Guest::from_elf(&elf[..40]).is_err(), "a truncated header");
    for (at, value, what) in [
        (4usize, 1u8, "32-bit"),
        (16, 3, "a PIE"),
        (18, 62, "x86-64"),
        (48, 1, "compressed"),
    ] {
        let mut bad = elf.to_vec();
        bad[at] = value;
        assert!(Guest::from_elf(&bad).is_err(), "{what}");
    }

    // A file is read into buffers the size of what it says it holds, so what it says has
    // to be bounded by what it carries: a segment at the top of a region would otherwise
    // allocate the whole region, gigabytes from a few kilobytes. The two headers a
    // malformed file can wrap are checked too, since a wrapped address reads a field the
    // header never pointed at.
    let word_at = |file: &[u8], at: usize| u64::from_le_bytes(file[at..at + 8].try_into().unwrap());
    let phoff = word_at(elf, 32) as usize;
    for (field, value, what) in [
        (
            16,
            Region::TEXT.base() + (4 << 20),
            "a segment past what the file carries",
        ),
        (16, Region::TEXT.base() - 4, "a segment below the text"),
        (16, Region::TEXT.base() + 1, "a segment that is no instruction address"),
    ] {
        let mut bad = elf.to_vec();
        bad[phoff + field..phoff + field + 8].copy_from_slice(&value.to_le_bytes());
        assert!(Guest::from_elf(&bad).is_err(), "{what}");
    }
    let mut wrapped = elf.to_vec();
    wrapped[40..48].copy_from_slice(&u64::MAX.to_le_bytes()); // the section headers' offset
    assert!(Guest::from_elf(&wrapped).is_err(), "a wrapped section-header address");
}

#[test]
fn malformed_elf_layouts_are_refused() {
    let elf = include_bytes!("../../../../../programs/fibonacci/fibonacci.elf");
    let word_at = |at: usize| u64::from_le_bytes(elf[at..at + 8].try_into().unwrap());
    let ph = word_at(32) as usize;
    let data = ph + 56;
    let bss = data + 56;
    let text_len = word_at(ph + 32);
    let sh = word_at(40) as usize;
    let n_sections = u16::from_le_bytes(elf[60..62].try_into().unwrap()) as usize;
    let sym = (0..n_sections)
        .map(|i| sh + i * 64)
        .find(|&at| u32::from_le_bytes(elf[at + 4..at + 8].try_into().unwrap()) == 2)
        .expect("fixture has symbols");
    let guest = Guest::from_elf(elf).unwrap();

    for (at, width, value, reason) in [
        (20, 4, 2, ElfError::UnsupportedHeader),
        (52, 2, 63, ElfError::UnsupportedHeader),
        (48, 4, 8, ElfError::UnsupportedFlags { flags: 8 }),
        (54, 2, 0, ElfError::UnsupportedHeader),
        (54, 2, 55, ElfError::UnsupportedHeader),
        (58, 2, 63, ElfError::UnsupportedHeader),
        (24, 8, 0, ElfError::EntryPoint { entry: 0 }),
        (
            24,
            8,
            Region::RAM.base(),
            ElfError::EntryPoint {
                entry: Region::RAM.base(),
            },
        ),
        (
            24,
            8,
            Region::TEXT.base() + 2,
            ElfError::EntryPoint {
                entry: Region::TEXT.base() + 2,
            },
        ),
        (
            24,
            8,
            Region::TEXT.base() + text_len,
            ElfError::EntryPoint {
                entry: Region::TEXT.base() + text_len,
            },
        ),
        (ph + 40, 8, text_len - 1, ElfError::MalformedSegment),
        (ph + 48, 8, 3, ElfError::MalformedSegment),
        (ph + 8, 8, word_at(ph + 8) + 1, ElfError::MalformedSegment),
        (data + 40, 8, word_at(data + 40) + 8, ElfError::MalformedSegment),
        (bss + 40, 8, 8 << guest.log_ram, ElfError::RamSize),
        (sym + 56, 8, 1, ElfError::MalformedSymbols),
        (sym + 32, 8, word_at(sym + 32) - 1, ElfError::MalformedSymbols),
    ] {
        let mut bad = elf.to_vec();
        bad[at..at + width].copy_from_slice(&value.to_le_bytes()[..width]);
        assert_eq!(Guest::from_elf(&bad), Err(reason), "offset {at}");
    }

    // Executable BSS is zero-filled memory, not a file-backed entry instruction.
    let mut bad = elf.to_vec();
    bad[ph + 40..ph + 48].copy_from_slice(&(text_len + 4).to_le_bytes());
    bad[24..32].copy_from_slice(&(Region::TEXT.base() + text_len).to_le_bytes());
    assert_eq!(
        Guest::from_elf(&bad),
        Err(ElfError::EntryPoint {
            entry: Region::TEXT.base() + text_len
        })
    );

    // A complete instruction inside the executable segment may be another entry.
    let mut other_entry = elf.to_vec();
    other_entry[24..32].copy_from_slice(&(Region::TEXT.base() + 4).to_le_bytes());
    let loaded = Guest::from_elf(&other_entry).unwrap();
    assert_eq!(loaded.entry_pc, Region::TEXT.base() + 4);
    assert_eq!(loaded.text, guest.text);
    assert_eq!(loaded.image, guest.image);
}

#[test]
fn elf_metadata_is_not_part_of_the_program_identity() {
    let elf = include_bytes!("../../../../../programs/fibonacci/fibonacci.elf");
    let program = Program::from_elf(elf).unwrap();
    let mut metadata = elf.to_vec();
    metadata[9..16].fill(0xa5);
    let same = Program::from_elf(&metadata).unwrap();
    assert_eq!(program.digest(), same.digest());
    assert_eq!(program.rv().entries(), same.rv().entries());
    assert_eq!(program.rv().image(), same.rv().image());
}
