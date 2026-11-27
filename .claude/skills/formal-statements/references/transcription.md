# Transcription: Rust, the guest and doc/leanvm into Lean

Transcribed content (the verifier, the ISA, the executor, hash inputs, encodings, protocol parameters, the guest's bytecode) appears in the hypotheses of the soundness theorems. A paraphrase makes the theorem about a different machine. The rule: **copy, do not paraphrase.**

## Before you write

- Read the source at the commit the change targets. In this repository the Lean and the Rust land together: the source is the Rust in `crates/` and `guests/` at the same commit (`formal/AGENTS.md`, "The repository").
- Find every item the definition depends on, not just the function you transcribe: its constants, its helpers, the types it reads, the checks its caller makes before calling it.
- Cite by name: the Rust item (`crates/verifier/src/whir.rs`'s `verify_whir`, say), the guest function, the `doc/leanvm` section label. Never a line number.

## While you write

- Keep the source's structure: one Lean definition per Rust function where that is reasonable (`Statement/Verifier/` is a file per file of `crates/verifier/src`), its names in Lean's case (`foo_bar` is `fooBar`), its order of operations.
- A deviation needs a license: name the property that makes it equal to the source (a field identity, a list lemma) and make sure it holds in the target structure, not just in the reals. Dropping a "redundant" term, reordering operations or fixing an apparent bug is not licensed.
- Step comments: mark each step of the source in a `--` comment above the line that computes it, and say where the Lean departs from the source's steps and why.
- A suspected bug in the Rust is a finding. Report it with the Rust item and the Lean declaration; do not edit either side to make them agree.

## Pitfalls in this repository

Fields:

- `K = GF(2^64)` and `E = K[y]/(y^2 + x*y + 1)` have characteristic 2: `x + x = 0`, `2 = 0`, `-x = x`, subtraction is addition. A formula transcribed from a prime-field paper may carry a sign or a factor 2 that is not there in the Rust; a hypothesis such as `(2 : K) ≠ 0` is false.
- A word of `E` has two limbs, `E.limb : Fin 2 → K`, and a numeral index wraps: `x.limb 2` elaborates and reads limb `0`. Write limbs `0` and `1` only.
- Multiplication in `K` is carry-less; an integer identity does not transfer.

Bytes, limbs and order:

- Byte order, limb order and lane order follow the Rust exactly. Keccak lanes are little-endian 64-bit words (`Statement/Keccak.lean`).
- Sizes, padding and padding rows: copy the Rust's lengths and how it pads (a table padded to a power of two, a message padded to a block). An off-by-one in a size is a different statement.

Fiat-Shamir and the verifier:

- Every value the Rust observes into the transcript, in the Rust's order, and only those. A value that rode the proof stream is bound when it is read; it is not observed again (root `AGENTS.md`, "Security and Fiat-Shamir").
- Labels and domain separators are copied byte for byte.
- Grinding: the Rust takes the smallest valid nonce, except where the root `AGENTS.md` names an exception. Transcribe which nonce the verifier accepts, not how the prover finds it.
- Every check of the Rust verifier is a check in the Lean verifier, in the same place. Reading the proof (a Merkle path's position and sizes, the stream's length) also pins values: transcribe those reads as the Rust does them.
- The opening's terminal point is rotated before the basis is evaluated (root `AGENTS.md`, "The guest"); every other read of the point stays in round order.

Lean traps:

- An `!` accessor, `panic!` or `getD` returns a default where the Rust would fail. Use the Rust's outcome (an `Option`, an `Except`, a rejection) unless the Rust has the same default.
- Junk values: `x / 0 = 0` and `n - m = 0` for `m > n` in `ℕ`, out-of-range indexing. Make sure the source never reaches them, or that it computes the same value there.
- Prefer structural recursion and folds to `Id.run do` loops with mutable variables, so the proofs follow the definition. A recursive definition the kernel cannot unfold (`partial def`) cannot be reasoned about.

## The evidence that it matches

Differential tests compare the Lean with the Rust (commands in `formal/AGENTS.md`, "Commands"): `scripts/fuzz-verifier.py` (the verifier on mutated proofs), `scripts/wire-diff.py` (the wire encoding), `scripts/prover-diff.py` (the statement's prover against both verifiers), `lake exe scheme-vectors` (the schemes' verifiers on the crates' vectors) and `guest-diff` (the guest's hints). They are evidence, not proof: they show agreement on what they sample. A pinned value in the tests must come from the Rust or the specification, never from the Lean under test.
