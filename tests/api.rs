use leanvm::asm::*;
use leanvm::*;

/// `a0 <- F(n) mod 2^64`, `n` being the first word of the public input, by a loop that
/// keeps its two numbers on the stack.
fn fibonacci() -> Program {
    const LOG_RAM: usize = 4;
    let text = Asm::new()
        .li(SP, RAM_BASE + (8 << LOG_RAM) - 16)
        .li(T0, RAM_BASE)
        .load("ld", T0, 0, T0)
        .i("addi", T1, ZERO, 1)
        .store("sd", ZERO, 0, SP)
        .store("sd", T1, 8, SP)
        .label("loop")
        .load("ld", A0, 0, SP)
        .load("ld", A1, 8, SP)
        .r("add", A2, A0, A1)
        .store("sd", A1, 0, SP)
        .store("sd", A2, 8, SP)
        .i("addi", T0, T0, -1)
        .branch("bne", T0, ZERO, "loop")
        .load("ld", A0, 0, SP)
        .li(A1, 0)
        .li(A2, 0)
        .exit()
        .finish();
    Program::new(&text, TEXT_BASE, vec![], LOG_RAM, 0)
}

/// The `preimage` guest (see `guests/`): it hashes the message the prover puts in the
/// advice and returns the digest, so one program, one input and two advices give two
/// statements. Its rows cover the tables `fibonacci` does not: `HASH`, and the advice's
/// side of memory.
fn preimage(message: &[u8]) -> (Program, Vec<u64>, [u64; 4]) {
    let program = Program::from_elf(include_bytes!("../guests/elf/preimage.elf")).expect("a guest");
    let mut advice = vec![message.len() as u64];
    advice.extend(message.chunks(8).map(|chunk| {
        let mut word = [0u8; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        u64::from_le_bytes(word)
    }));
    let digest = primitives::hash::hash(message);
    let expected = std::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap()));
    (program, advice, expected)
}

#[test]
fn public_api_end_to_end() {
    setup_prover();
    let program = fibonacci();
    let input = [90, 0, 0, 0];

    // 1. Prove, then onto the wire and back to a receiver.
    let (proof, output, _) = prove(&program, input, &[], MIN_LOG_INV_RATE).expect("the run halts");
    assert_eq!(output, [2_880_067_194_370_816_120, 0, 0, 0]);
    let bytes = bincode::serialize(&proof).unwrap();
    let received: Proof = bincode::deserialize(&bytes).unwrap();
    verify(&program, &input, &output, &received).unwrap();

    // 2. The proof is about this input and this output, and no other.
    let (mut wrong_input, mut wrong_output) = (input, output);
    wrong_input[0] += 1;
    wrong_output[0] += 1;
    assert!(verify(&program, &wrong_input, &output, &received).is_err());
    assert!(verify(&program, &input, &wrong_output, &received).is_err());

    // 3. One proof is one arena phase: the first proof outlives the second's phase.
    let (second, _, _) = prove(&program, input, &[], MIN_LOG_INV_RATE).expect("the run halts");
    verify(&program, &input, &output, &second).unwrap();
    verify(&program, &input, &output, &received).unwrap();
    // 4. The same, over a guest whose rows include the hash table and the advice: with
    // the arena engaged, a buffer that outlived its phase would show up here as a proof
    // that stops verifying, and nowhere else (the verifier tests run the arena off).
    for message in [b"leanVM".as_slice(), b""] {
        let (guest, advice, digest) = preimage(message);
        let (proof, output, _) = prove(&guest, [0; 4], &advice, MIN_LOG_INV_RATE).expect("the run halts");
        assert_eq!(output, digest, "the guest hashed the advice");
        verify(&guest, &[0; 4], &output, &proof).unwrap();
        // The advice is the prover's alone: it is no part of what the verifier is told.
        verify(&guest, &[0; 4], &output, &proof).unwrap();
    }

    let stats = zk_alloc::stats();
    assert!(stats.phases >= 2, "expected one phase per proof, got {stats:?}");
    assert!(stats.peak_bytes > 0, "no buffer reached the arena: {stats:?}");
    assert_eq!(
        stats.overflow, 0,
        "a slab overflowed into the system allocator: {stats:?}"
    );
}
