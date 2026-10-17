# leanSPHINCS security in Lean 4

**`Sphincs.Lifetimes.requestedSecurity` proves that leanSPHINCS, the scheme of [`crates/sphincs`](../../crates/sphincs) specified in [`doc/sphincs`](../../doc/sphincs), has 127 bits of classical SUF-CMA security in the random-oracle model, at every subtree height below.** [Axioms.lean](Sphincs/Axioms.lean) pins every public theorem to `propext`, `Classical.choice` and `Quot.sound` with `#guard_msgs`. There is no `sorry` and no `native_decide`.

The game is [StatementDet.lean](Sphincs/StatementDet.lean). A uniform 32-byte seed generates the key (`Seeded.keygenFromSeed`), and the adversary gets the public key, the random oracle and a signing oracle running the deterministic signer `Seeded.sign`. It wins if the final `Concrete.verify` accepts its pair, the pair is not one the signing oracle returned, and the signing oracle answered at most `N` requests, repeats included. `HasClassicalSecurityBitsDet 127` says that for every `q ≥ 1` and every adversary whose experiment makes at most `q` hash calls on every outcome, the probability of winning is at most `q / 2^127`. The count includes every call of the experiment: key generation, the signer and the final verification. Private sampling is free, and running time and memory are unbounded.

## Lifetimes

A key keeps one subtree of height `b` of the height-26 tree (`doc/sphincs` explains the pruning). Each row is one theorem of [Lifetimes.lean](Sphincs/Lifetimes.lean):

| b | signatures N | key generation, hash calls | key generation, permutations |
| ---: | ---: | ---: | ---: |
| 26 | 1,383,000,000 | 15,166,603,264 | 15,703,474,176 |
| 20 | 26,030,000 | 236,978,188 | 245,366,796 |
| 14 | 480,900 | 3,702,808 | 3,833,880 |
| 13 | 247,000 | 1,851,418 | 1,916,954 |
| 12 | 126,900 | 925,724 | 958,492 |
| 10 | 33,490 | 231,456 | 239,648 |
| 8 | 8,830 | 57,892 | 59,940 |

The hash calls are `226 · 2^b + 2 (26 − b)` (`Security.Prefix.hashCalls_keygenFromSeed`): per one-time key 32 derivations of chain starts, 192 chain steps and the leaf, then the `2^b − 1` nodes of the subtree, the `26 − b` surrogate siblings, the `26 − b` nodes above the subtree and the public parameter. In permutations of the leanVM hash, one per started 128-byte block, a one-time leaf hashes 1,056 bytes and costs 9, so the total is `234 · 2^b + 2 (26 − b)`.

Also proved: for every hash function and every subtree height, a signature the signer returns verifies (`Completeness.correct`), a signature serializes to 4,276 bytes (`signature_size`), and an accepted verification costs exactly 268 permutations of the leanVM hash, one per started 128-byte block, and no signature more (`Cost.verification_permutations`, `Cost.verification_permutations_le`), which is `sphincs::VERIFY_PERMUTATIONS`.

## The model and the Rust code

[Scheme.lean](Sphincs/Scheme.lean) is the functional model. Its bytes are the crate's: the 16-byte address and every hash domain, the seed derivations (two chain starts per hash), the randomizer base `R0 = Th(P, A(7, 0, 0), seed ‖ m)` and the attempts `R0 + i`, the 234-bit message digest and its field offsets, the codeword table (`codewordCodes`, the rule of `doc/sphincs`), the kept subtree (the first 8 bytes of `P` mod `2^(26−b)`), the 2^32 bounds on randomizer and counter attempts, and the serialization. This was checked by reading both sides; it is not a mechanized refinement of the Rust.

The two signers compute the same signature, but not with the same hash calls. The Lean signer recomputes the forest for its key and again for the opening, and hashes the digest once more after its loop, where the Rust signer reuses what it computed. The budget `q` of the theorem counts the calls of the Lean signer.

## Build

```sh
cd formal/sphincs
lake exe cache get
lake build
```

[PROOF.md](PROOF.md) describes the route, the codeword table, the hash inputs, the signer's hash-call counts, and the scripts that generate the kernel-checked certificates.

## Libraries

| Library                    | What it is                                                                                                                                                                                                                                |
| -------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [Sphincs](Sphincs)         | The scheme and its proof.                                                                                                                                                                                                                 |
| [SphincsFors](SphincsFors) | The modules of the proof of the FORS variant of leanSPHINCS that `Sphincs` imports.                                                                                                                                                       |
| [SphincsBase](SphincsBase) | The modules that `Sphincs` and `SphincsFors` import from the candidates' copy of the proof of leanVM's earlier SPHINCS instance (whose hash domains it renumbers): scheme-independent tooling (uniform tables, query caps, chain bounds). |

The three come from [leanXMSS-leanSPHINCS-candidates](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/tree/134a0b638a3a5041f5abdebaed72569ed560619d/formal/sphincs) at commit `134a0b6`, where they are named `LeanForest`, `LeanSphincs` and `SphincsSecurity` and where the rest of the FORS proof is. Only the modules `Sphincs` reaches are here, renamed and otherwise unchanged but for `VerificationCost.lean`, which counts the leanVM hash's 128-byte blocks where the candidates count SHA3's 136-byte rate (267 permutations there, the 1,056-byte one-time leaf being 8 permutations of SHA3 and 9 blocks here), and for a doc comment of `Lifetimes.lean`, of `LifetimeCertificates.lean` and of the script that writes it.
