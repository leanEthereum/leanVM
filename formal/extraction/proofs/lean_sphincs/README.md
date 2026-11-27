# leanSPHINCS's `verify`, proved from its extraction

The Rust `verify` of `crates/lean_sphincs`, as hax extracts it, is leanSPHINCS verification as the statement defines it (`formal/Statement/LeanSphincs.lean`), the function the end statement's unforgeability is about:

```lean
theorem verify_eq_verifyWithKeccak (pk : lean_sphincs.scheme.LeanSphincsPublicKey)
    (m : Array Std.U8 32#usize) (sig : lean_sphincs.scheme.LeanSphincsSignature) :
    lean_sphincs.scheme.verify pk m sig =
      ok (verifyWithKeccak (toPublicKey pk) (toMessage m) (toSignature sig))
```

It says two things: `verify` returns on every input (no panic, no overflow, no index out of range), and what it returns is the statement's verdict on the values its arguments stand for. It has no hypothesis: every function on the path is extracted with its body, down to the Keccak-f[1600] permutation.

Along the way the statement's own Keccak is checked against another specification: `keccak256_eq_reference` (`KeccakSpec.lean`) shows its Keccak-256 is the FIPS 202 sponge KECCAK[512] with Keccak's original padding, as [hash-specs](https://github.com/Verified-zkEVM/hash-specs) defines it on bits.

```sh
formal/extraction/hax.sh extract                       # the extraction is generated, not committed
(cd formal/extraction/proofs/lean_sphincs && lake build)
```

`hax.sh check` builds it after the extractions, scans it for escapes and compares the theorem's axioms with the three below.

## Layout

| file | what it proves |
| --- | --- |
| `Defs.lean` | how a Rust value stands for a statement value, and each function's theorem as a `Prop` |
| `Common.lean` | the library models the extraction calls, as equations; bytes read as numbers |
| `Permutation.lean` | `keccak_f`, the 24 rounds on `u64` lanes, is hash-specs' Keccak-f[1600] on lanes |
| `KeccakSpec.lean` | the statement's Keccak-f[1600] and Keccak-256 are hash-specs', and so FIPS 202's |
| `Sponge.lean` | `absorb` and `digest_of`, given what `keccak_f` computes |
| `Keccak.lean` | the three composed: `keccak_f` is the statement's Keccak-f[1600] |
| `Hasher.lean` | `keccak256::Hasher` computes Keccak-256, given `absorb` and `digest_of` (`SpongeSpec`) |
| `Hash.lean` | `th`, the addresses and their words |
| `Digest.lean` | `h_msg`, `digest_fields`, `message_digest` |
| `Wots.lean` | `OtsKey::of_index`, `chain`, `codeword`, `encode`, `wots_leaf` |
| `Trees.lean` | `path_root`, `tree_root`, `fors_root` |
| `Verify.lean` | `path_range`, the loop over the layers, `verify` given the theorems above |
| `Theorem.lean` | the composition |

## What it rests on

`#print axioms verify_eq_verifyWithKeccak` gives `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no `native_decide`, no `bv_decide`, no option set, and no hypothesis.

- **The patches.** The theorem is about the patched Rust (`crates/{lean_sphincs,keccak256}/proofs/*/patches/pre`), not the committed Rust. `hax.sh test` runs the crates' tests on the patched source; nothing in Lean relates the two.
- **Which permutation.** `keccak256` has one `permute` for x86-64 and one for every other architecture, and on a CPU with AVX-512 a third, in AVX-512 intrinsics, for a single state. The extraction is of the second, on every host. The x86-64 body and the AVX-512 one are not covered.
- **The toolchain and its models.** Charon, Aeneas (here a fork, pinned in `lakefile.toml`, for Lean v4.36.0), the hax Lean library's models of `core`, and `CoreModelsExt`.
- **How Rust values are read.** `toPublicKey`, `toMessage` and `toSignature` (`Defs.lean`) are definitions to be read, not proved. They are total and `toDigest` is injective, so distinct Rust inputs are distinct statement inputs. The byte encodings (`from_bytes`, `to_bytes`) are not covered.
- **hash-specs**, as a pivot only: the Rust permutation and the statement's are each proved equal to its Keccak-f on lanes, so its definitions do not enter what the theorem says.

## What the proofs found

No disagreement between the Rust and the statement: byte and bit orders, the address layout, the digest's fields, the codeword and its sum, the chains, the folds and the layer paths all match. What the work did turn up is about the approach:

1. **The verified `verify` is not the shipped `verify`.** Every loop on its path is patched: `path_range`, `of_index`, `codeword`'s sum and `h_msg` are rewritten to indexed loops, and `tree_fold` and `fors_recover` are replaced by `tree_root` and `fors_root`, new functions that drop the visitor. The second is not a mechanical rewrite. The link to the committed Rust is the test suite.
2. **`debug_assert!` is extracted as a hard assertion.** `chain` panics in the model when `start + steps >= CHAIN_LEN`; a release build has no such check. The proof shows it cannot fire from `verify`, so nothing is lost here, but a function proved "total" in the model can be stricter than the binary, and one that is not total in the model may still run in release.
3. **What was opaque was so for want of a model, not for difficulty.** `absorb` and `digest_of` needed a two-line indexed-loop patch each, and the permutation's rounds extract as written once the vector lane types are left out. Two things around them did need a patch: the choice of `permute` under `cfg(target_arch)`, and two trait methods with default bodies Aeneas rejects, which make the whole trait instance untranslatable unless they move to a trait of their own.
4. **A hand-written model is on the path.** `Ord::min` in `Hasher::update` resolves to `core.cmp.Ord.min` in `CoreModelsExt/Core.lean`. It is right for this use, and it is trusted.
5. **A library model differs in shape from the Rust.** `u64::rotate_left` is modelled as `(x << m) ^ (x >> (64 - m))`, an XOR where the definition has an OR, with `m = 0` a case of its own; the two agree because the halves share no bit. And `to_le_bytes` is a closure over the byte index where `to_be_bytes` is a primitive.
6. **The statement's Keccak agrees with FIPS 202's.** No difference in rotation offsets, π, round constants, padding (the one byte `0x81` at 135 remaining bytes included) or output.
7. **Library models are heavier than the Rust.** `array::repeat` builds a sequence and removes its head `N` times, `copy_from_slice` is a `mapM` of `clone`, `as_flattened` fails past `usize::MAX` bytes, constants are computations that have to be proved to return. Each had to be given an equation before use (`Common.lean`); none was found wrong.
8. **The mutable-borrow return of `update` matters.** `Hasher::update` returns `&mut Self`, which Aeneas gives as a value and a back-function. The proofs need that function to be the identity, which it is in the extraction; an assumption placed on an opaque `update` would have to say so.
9. **Reduction is a hazard.** A hypothesis whose type is a `match` on the statement's verifier makes Lean's linters and `omega` try to evaluate Keccak. The proofs keep such terms generalized. Rewriting under a `usize` literal's bound proof silently does nothing in places, hence the `erw`s.
10. **Two hypotheses of `Defs.lean` are unused.** `k.layer.val < 2 ^ 32` in `KeyAdrsSpec` and `TreeAdrsSpec`: the Rust's `as u32` truncates and so does the statement's address.
11. **`wots_leaf`'s codeword is unconstrained.** `WotsLeafSpec` speaks of the leaf alone, which is all `verify` uses.
12. **Width.** Nothing depends on `usize` being 64 bits; the proofs use `2^32 <= usize::MAX + 1` at most.
