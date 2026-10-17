# leanSPHINCS security in Lean 4

**`Sphincs.Lifetimes.requestedSecurity` proves that leanSPHINCS, the scheme of [`crates/signatures/src/lean_sphincs`](../../crates/signatures/src/lean_sphincs) specified in [`doc/lean_sphincs`](../../doc/lean_sphincs), has 127 bits of classical SUF-CMA security in the random-oracle model, at every subtree height below.** [Axioms.lean](Sphincs/Axioms.lean) pins every public theorem to `propext`, `Classical.choice` and `Quot.sound` with `#guard_msgs`. There is no `sorry` and no `native_decide`.

The game is [StatementDet.lean](Sphincs/StatementDet.lean). A uniform 32-byte seed `S0` generates the key (`Seeded.keygenFromSeed`: the scheme seed `S = H(leanSPHINCS ‖ S0)`, then everything from `S`), and the adversary gets the public key, the random oracle and a signing oracle running the deterministic signer `Seeded.sign`. It wins if the final `Concrete.verify` accepts its pair, the pair is not one the signing oracle returned, and the signing oracle answered at most `N` requests, repeats included. `HasClassicalSecurityBitsDet 127` says that for every `q ≥ 1` and every adversary whose experiment makes at most `q` hash calls on every outcome, the probability of winning is at most `q / 2^127`. The count includes every call of the experiment: key generation, the signer and the final verification. Private sampling is free, and running time and memory are unbounded.

## Lifetimes

A key keeps one subtree of height `b` of the height-26 tree (`doc/lean_sphincs` explains the pruning). Each row is one theorem of [Lifetimes.lean](Sphincs/Lifetimes.lean):

|    b |  signatures N | key generation, hash calls | key generation, compressions |
| ---: | ------------: | -------------------------: | ---------------------------: |
|   26 | 1,383,000,000 |             15,166,603,265 |               16,240,345,089 |
|   20 |    26,030,000 |                236,978,189 |                  253,755,405 |
|   14 |       480,900 |                  3,702,809 |                    3,964,953 |
|   13 |       247,000 |                  1,851,419 |                    1,982,491 |
|   12 |       126,900 |                    925,725 |                      991,261 |
|   10 |        33,490 |                    231,457 |                      247,841 |
|    8 |         8,830 |                     57,893 |                       61,989 |

The hash calls are `226 · 2^b + 2 (26 − b) + 1` (`Security.Prefix.hashCalls_keygenFromSeed`): the scheme seed, then per one-time key 32 derivations of chain starts, 192 chain steps and the leaf, then the `2^b − 1` nodes of the subtree, the `26 − b` surrogate siblings, the `26 − b` nodes above the subtree and the public parameter. In BLAKE2s compressions, a one-time leaf hashes 1,056 bytes and costs 17 and the scheme seed's 43 bytes cost 1, so the total is `242 · 2^b + 2 (26 − b) + 1`.

Also proved: for every hash function and every subtree height, a signature the signer returns verifies (`Completeness.correct`), a signature serializes to 4,276 bytes (`signature_size`), and an accepted verification costs exactly 307 compressions and no signature costs more (`Cost.verification_compressions`, `Cost.verification_compressions_le`).

## The model and the Rust code

[Scheme.lean](Sphincs/Scheme.lean) is the functional model. Its bytes are the crate's: the scheme seed `S = H(leanSPHINCS ‖ S0)` (`schemeSeedInput`, 43 bytes), the 16-byte address and every hash domain, the seed derivations (two chain starts per hash), the randomizer base `R0 = Th(P, A(7, 0, 0), S ‖ m)` and the attempts `R0 + i`, the 234-bit message digest and its field offsets, the codeword table (`codewordCodes`, the rule of `doc/lean_sphincs`), the kept subtree (the first 8 bytes of `P` mod `2^(26−b)`), the 2^32 bounds on randomizer and counter attempts, and the serialization. This was checked by reading both sides; it is not a mechanized refinement of the Rust.

The two signers compute the same signature, but not with the same hash calls. The Lean signer recomputes the forest for its key and again for the opening, and hashes the digest once more after its loop, where the Rust signer reuses what it computed and keeps the BLAKE2s state after the digest's first block. The budget `q` of the theorem counts the calls of the Lean signer.

## Build

```sh
cd formal/lean_sphincs
lake exe cache get
lake build
```

[PROOF.md](PROOF.md) describes the route, the codeword table, the hash inputs, the signer's hash-call counts, and the scripts that generate the kernel-checked certificates.

## Libraries

| Library                    | What it is                                                                                                                                                                                                                                |
| -------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [Sphincs](Sphincs)         | The scheme and its proof.                                                                                                                                                                                                                 |
| [SphincsFors](SphincsFors) | The modules of the proof of the FORS variant of leanSPHINCS that `Sphincs` imports.                                                                                                                                                       |
| [SphincsBase](SphincsBase) | The modules that `Sphincs` and `SphincsFors` import from the candidates' copy of the proof of leanVM's earlier leanSPHINCS instance (whose hash domains it renumbers): scheme-independent tooling (uniform tables, query caps, chain bounds). |

The three come from [leanXMSS-leanSPHINCS-candidates](https://github.com/TomWambsgans/leanXMSS-leanSPHINCS-candidates/tree/cc0648feb5b686ba1447678120e401f7b78098f7/formal/lean_sphincs) at commit `cc0648f`, where they are named `LeanForest`, `LeanSphincs` and `SphincsSecurity` and where the rest of the FORS proof is. Only the modules `Sphincs` reaches are here, renamed and otherwise unchanged but for one comment of `LifetimeCertificates.lean` and of the script that writes it.
