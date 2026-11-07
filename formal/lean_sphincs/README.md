# leanSPHINCS security in Lean 4

**`FORS.h26_layered` proves that leanSPHINCS, the scheme of [`crates/signatures/src/lean_sphincs`](../../crates/signatures/src/lean_sphincs) specified in [`doc/lean_sphincs`](../../doc/lean_sphincs), has 127 bits of classical SUF-CMA security in the random-oracle model, up to 1,182,000,000 signatures.** [Axioms.lean](FORS/Axioms.lean) pins it to `propext`, `Classical.choice` and `Quot.sound` with `#guard_msgs`, and checks that no declaration of the library depends on another axiom. Every numeric certificate is checked by the kernel.

The statement is [Main.lean](FORS/Main.lean) and the game [Statement.lean](FORS/Statement.lean). The secret key is a uniform 32-byte `SK.seed` (`Seeded.keygen`), from which `Seeded.keygenFromSeed` derives `PK.seed`, `SK.prf` and every secret, and the adversary gets the public key, the random oracle and a signing oracle running the deterministic signer `Seeded.sign`. It wins if the final `Concrete.verify` accepts its pair, the pair is not one the signing oracle returned, and the signing oracle answered at most `N` requests, repeats included. `Secure127` says that for every `q ≥ 1` and every adversary whose experiment makes at most `q` hash calls on every outcome, the probability of winning is at most `q / 2^127`. The count includes every call of the experiment: key generation (the two hashes deriving `PK.seed` and `SK.prf` included), the signer and the final verification.

Also proved: a signature the signer returns verifies (`Completeness.correct`), a signature serializes to 7,740 bytes (`Configurations.size_h26_layered_k24`), and an accepted verification costs exactly 515 Keccak-f permutations (`Configurations.keccak256_h26_layered_k24`), the crate's `lean_sphincs::SIG_SIZE` and `lean_sphincs::VERIFY_PERMUTATIONS`.

## The model and the Rust code

[Scheme.lean](FORS/Scheme.lean) is the functional model, generic in `Params` (the height, the layers, the FORS shape and the signature limit) and instantiated at `.layered 26 3 8 24 10 1182000000`: three layers of 10 + 8 + 8, FORS of 24 trees of height 10. Its bytes are the crate's, in FIPS 205's layout: `PK.seed`, the first 16 bytes of `H(leanSPHINCS ‖ SK.seed ‖ 0)`, and `SK.prf = H(leanSPHINCS ‖ SK.seed ‖ 1)` (`keySeedInput`: the 11 ASCII bytes of `leanSPHINCS`, the 32 bytes of `SK.seed`, one domain byte); every addressed input `PK.seed ‖ ADRS ‖ payload`, ADRS being FIPS 205's 32-byte address of big-endian words (layer, tree, type, key pair, chain or height, hash or index); one `PRF(PK.seed, SK.seed, ADRS)` call per secret; the randomizer `R`, the first 16 bytes of `H(SK.prf ‖ PK.seed ‖ M')` with `M' = 0x00 ‖ 11 ‖ leanSPHINCS ‖ M`; the two `H_msg` calls on `R ‖ PK.seed ‖ PK.root ‖ M ‖ BE_32(i)`, the message unframed, read as FIPS 205's Algorithm 19; each FORS tree hashed to its root and `T_k` of the roots; the encodings with their big-endian counter last, the `2^32` bound on counters, and the serialization. This was checked by reading both sides; it is not a mechanized refinement of the Rust.

The model's signer keeps a grinding loop: it also derives a step from the second half of the randomizer hash and tries `R`, `R + step`, ... until the index lands in the kept subtree of the top layer. Key generation builds the whole top layer (`Params.full`, required of every configuration), so every index lands and the signer signs at `R`, as the crate does; the loop's test, which reads the first digest call's low bits rather than the index, never decides anything. The two signers compute the same signature in the same order: the digest, the FORS opening and its public key recovered from the opening, then the layers from the bottom up, each a counter search and, on success, the chain values, the path and, below the top layer, the root recovered from the signature as the verifier recovers it, stopping at the first failed search. On every run the Lean signer makes no more hash calls than the Rust signer, which also rebuilds the top tree before it signs, so the bound, whose budget `q` counts the Lean signer's calls, holds for the crate's signer with the same `q`.

## The proof

| Modules | What they do |
| --- | --- |
| [Scheme/](FORS/Scheme) | the model's lemmas: bytes and domains, the digest, the layout, correctness, verification costs |
| [Seed/](FORS/Seed), [Reduction/](FORS/Reduction) | the oracle internalized, the seed eliminated from the game |
| [ScanSigner/](FORS/ScanSigner), [GraphView/](FORS/GraphView), [LazyRun/](FORS/LazyRun) | the signer's hash calls, their cost, and the run sampled lazily |
| [Classification/](FORS/Classification) | what an accepted forgery must contain |
| [SmallBudget/](FORS/SmallBudget), [LargeBudget/](FORS/LargeBudget) | the two routes, for small and for large query budgets |
| [CoverBound/](FORS/CoverBound), [CoverPotential/](FORS/CoverPotential), [Base/](FORS/Base) | the bound on covering every FORS tree, and the potentials |
| [Certificates/](FORS/Certificates), [Lifetimes.lean](FORS/Lifetimes.lean) | the kernel-checked certificates of this configuration (`decide +kernel`), and the theorem they give |

## Build

```sh
cd formal/lean_sphincs
lake exe cache get
lake build
```
