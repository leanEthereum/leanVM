use leanvm::asm::*;
use leanvm::*;

/// `a0 <- F(n) mod 2^64`, `n` being the first word of the program's image, by a loop
/// that keeps its two numbers on the stack.
fn fibonacci(n: u64) -> Program {
    const LOG_RAM: usize = 4;
    let text = Asm::new()
        .li(Reg::SP, RAM_BASE + (8 << LOG_RAM) - 16)
        .li(Reg::T0, RAM_BASE)
        .load(Ld, Reg::T0, 0, Reg::T0)
        .i(Addi, Reg::T1, Reg::ZERO, 1)
        .store(Sd, Reg::ZERO, 0, Reg::SP)
        .store(Sd, Reg::T1, 8, Reg::SP)
        .label("loop")
        .load(Ld, Reg::A0, 0, Reg::SP)
        .load(Ld, Reg::A1, 8, Reg::SP)
        .r(Add, Reg::A2, Reg::A0, Reg::A1)
        .store(Sd, Reg::A1, 0, Reg::SP)
        .store(Sd, Reg::A2, 8, Reg::SP)
        .i(Addi, Reg::T0, Reg::T0, -1)
        .branch(Bne, Reg::T0, Reg::ZERO, "loop")
        .load(Ld, Reg::A0, 0, Reg::SP)
        .li(Reg::A1, 0)
        .li(Reg::A2, 0)
        .exit()
        .finish();
    Program::new(&text, TEXT_BASE, vec![n], LOG_RAM, 0).expect("valid instruction program")
}

/// The `preimage` guest (see `programs/`): it hashes the message the prover puts in the
/// advice and commits the digest, so one program and two advices give two statements. Its rows cover the tables `fibonacci` does not: `HASH`, and the advice's
/// side of memory.
fn preimage(message: &[u8]) -> (Program, Vec<u64>, [u64; 4]) {
    let program = Program::from_elf(include_bytes!("../../../programs/preimage/preimage.elf")).expect("a guest");
    let mut advice = vec![message.len() as u64];
    advice.extend(message.chunks(8).map(|chunk| {
        let mut word = [0u8; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        u64::from_le_bytes(word)
    }));
    let digest = primitives::hash::hash(message);
    let digest: [u64; 4] = std::array::from_fn(|i| u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap()));
    // The output is the digest of what the guest committed: the message's digest.
    let mut public = leanvm_guest::PublicValues::new();
    public.commit(&digest);
    (program, advice, public.digest())
}

#[test]
fn public_api_end_to_end() {
    let prover = Prover::new();
    let program = fibonacci(90);

    // 1. Prove, then onto the wire and back to a receiver.
    let Proved { proof, output, .. } = prover.prove(&program, &[], Rate::MIN).expect("the run halts");
    assert_eq!(output, [2_880_067_194_370_816_120, 0, 0, 0]);
    let received = Proof::from_bytes(&proof.to_bytes()).expect("a proof's own bytes");
    verify(&program, &output, &received).unwrap();

    // 2. The proof is about this program and this output, and no other.
    let mut wrong_output = output;
    wrong_output[0] += 1;
    assert!(matches!(
        verify(&fibonacci(91), &output, &received),
        Err(Error::Verify(_))
    ));
    assert!(matches!(
        verify(&program, &wrong_output, &received),
        Err(Error::Verify(_))
    ));

    // 3. One proof is one arena phase: the first proof outlives the second's phase.
    let second = prover.prove(&program, &[], Rate::MIN).expect("the run halts");
    verify(&program, &output, &second.proof).unwrap();
    verify(&program, &output, &received).unwrap();
    // 4. The same, over a guest whose rows include the hash table and the advice: with
    // the arena engaged, a buffer that outlived its phase would show up here as a proof
    // that stops verifying, and nowhere else (the verifier tests run the arena off).
    for message in [b"leanVM".as_slice(), b""] {
        let (guest, advice, digest) = preimage(message);
        let Proved { proof, output, .. } = prover.prove(&guest, &advice, Rate::MIN).expect("the run halts");
        assert_eq!(output, digest, "the guest hashed the advice");
        // The advice is the prover's alone: it is no part of what the verifier is told.
        verify(&guest, &output, &proof).unwrap();
    }

    // 5. A proof of another protocol version is refused, as are bytes that are no proof.
    let bytes = received.to_bytes();
    let mut bumped = bytes.clone();
    bumped[4] += 1;
    let found = u16::from_le_bytes([bumped[4], bumped[5]]);
    assert_eq!(Proof::from_bytes(&bumped), Err(Error::UnsupportedVersion { found }));
    let mut magic = bytes.clone();
    magic[0] ^= 1;
    assert_eq!(Proof::from_bytes(&magic), Err(Error::MalformedProof));
    assert_eq!(Proof::from_bytes(&bytes[..bytes.len() - 1]), Err(Error::MalformedProof));
    assert_eq!(
        Proof::from_bytes(&[bytes.as_slice(), &[0]].concat()),
        Err(Error::MalformedProof)
    );

    // 6. What the caller gets wrong is an error, not a panic.
    assert_eq!(Rate::new(0), Err(InvalidRate { log_inv_rate: 0 }));
    assert!(Rate::new(Rate::MAX.log_inv_rate() + 1).is_err());
    let one_word =
        Program::new(&Asm::new().exit().finish(), TEXT_BASE, vec![], 0, 0).expect("valid instruction program");
    assert_eq!(
        prover.prove(&one_word, &[1, 2], Rate::MIN).map(|_| ()),
        Err(Error::AdviceTooLong { max: 1, got: 2 })
    );
    assert_eq!(Program::from_elf(b"\x7fELF").map(|_| ()), Err(ElfError::Truncated));

    let stats = zk_alloc::stats();
    assert!(stats.phases >= 2, "expected one phase per proof, got {stats:?}");
    assert!(stats.peak_bytes > 0, "no buffer reached the arena: {stats:?}");
    assert_eq!(
        stats.overflow, 0,
        "a slab overflowed into the system allocator: {stats:?}"
    );
}
