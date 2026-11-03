# leanSPHINCS security in Lean 4

**`FORS.h26_layered` proves that leanSPHINCS, the scheme of [`crates/signatures/src/lean_sphincs`](../../crates/signatures/src/lean_sphincs) specified in [`doc/lean_sphincs`](../../doc/lean_sphincs), has 127 bits of classical SUF-CMA security in the random-oracle model, up to 1,182,000,000 signatures.** [Axioms.lean](FORS/Axioms.lean) pins it to `propext`, `Classical.choice` and `Quot.sound` with `#guard_msgs`, and checks that no declaration of the library depends on another axiom. Every numeric certificate is checked by the kernel.

The statement is [Main.lean](FORS/Main.lean) and the game [Statement.lean](FORS/Statement.lean). A uniform 32-byte seed `S0` generates the key (`Seeded.keygen`): its hash `S = H(leanSPHINCS ‖ S0)` is the scheme seed, from which `Seeded.keygenFromSeed` derives the public parameter and every secret, and the adversary gets the public key, the random oracle and a signing oracle running the deterministic signer `Seeded.sign`. It wins if the final `Concrete.verify` accepts its pair, the pair is not one the signing oracle returned, and the signing oracle answered at most `N` requests, repeats included. `Secure127` says that for every `q ≥ 1` and every adversary whose experiment makes at most `q` hash calls on every outcome, the probability of winning is at most `q / 2^127`. The count includes every call of the experiment: key generation (the hash that derives `S` included), the signer and the final verification.

Also proved: a signature the signer returns verifies (`Completeness.correct`), a signature serializes to 7,740 bytes (`Configurations.size_h26_layered_k24`), and an accepted verification costs exactly 492 Keccak-f permutations (`Configurations.keccak256_h26_layered_k24`), which are `lean_sphincs::SIG_SIZE` and `lean_sphincs::VERIFY_PERMUTATIONS`.

## The model and the Rust code

[Scheme.lean](FORS/Scheme.lean) is the functional model, generic in `Params` (the height, the layers, the FORS shape and the signature limit) and instantiated at `.layered 26 3 8 24 10 1182000000`: three layers of 10 + 8 + 8, FORS of 24 trees of height 10. Its bytes are the crate's: the scheme seed `S = H(leanSPHINCS ‖ S0)` (`schemeSeedInput`, the 11 ASCII bytes of `leanSPHINCS` then the 32 bytes of `S0`, the whole 32-byte output kept), the 16-byte address with its layer and tree, every hash domain, the seed derivations (two secrets per hash), the randomizer `R = Th(P, A(7), S ‖ m)`, the two digest calls and the field offsets, the FORS addresses, the encodings with their counter last, the `2^32` bound on counters, and the serialization. This was checked by reading both sides, and below the scheme seed by the crate's known-answer test; it is not a mechanized refinement of the Rust.

The model's signer is written for every shape: it also derives a step from the second half of the randomizer hash and tries `R`, `R + step`, ... until the index lands in a kept subtree. A layered key keeps every index, so it signs at `R`, as the crate does. The two signers compute the same signature but not with the same hash calls: the Lean signer recomputes what the Rust signer reuses, and the budget `q` counts the calls of the Lean signer.

## The proof

| Modules | What they do |
| --- | --- |
| [Scheme/](FORS/Scheme) | the model's lemmas: bytes and domains, the digest, the layout, correctness, verification costs |
| [Seed/](FORS/Seed), [Reduction/](FORS/Reduction) | the oracle internalized, the scheme seed replaced by a uniform one ([SchemeSeed.lean](FORS/Reduction/SchemeSeed.lean)), the seed eliminated from the game |
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
