# leanSPHINCS's `verify`, proved from its extraction

The Rust `verify` of `crates/lean_sphincs`, as hax extracts it, is leanSPHINCS verification as the statement defines it (`formal/Statement/LeanSphincs.lean`), the function the end statement's unforgeability is about:

```lean
theorem verify_eq_verifyWithKeccak (S : SpongeSpec LeanVM.Semantics.keccakF1600)
    (pk : lean_sphincs.scheme.LeanSphincsPublicKey) (m : Array Std.U8 32#usize)
    (sig : lean_sphincs.scheme.LeanSphincsSignature) :
    lean_sphincs.scheme.verify pk m sig =
      ok (verifyWithKeccak (toPublicKey pk) (toMessage m) (toSignature sig))
```

It says two things: `verify` returns on every input (no panic, no overflow, no index out of range), and what it returns is the statement's verdict on the values its arguments stand for.

```sh
formal/extraction/hax.sh extract                       # the extraction is generated, not committed
(cd formal/extraction/proofs/lean_sphincs && lake build)
```

`hax.sh check` builds it after the extractions, scans it for escapes and compares the theorem's axioms with the five below.

## Layout

| file | what it proves |
| --- | --- |
| `Defs.lean` | how a Rust value stands for a statement value, and each function's theorem as a `Prop` |
| `Common.lean` | the library models the extraction calls, as equations; bytes read as numbers |
| `Hasher.lean` | `keccak256::Hasher` computes Keccak-256, given `absorb` and `digest_of` (`SpongeSpec`) |
| `Hash.lean` | `th`, the addresses and their words |
| `Digest.lean` | `h_msg`, `digest_fields`, `message_digest` |
| `Wots.lean` | `OtsKey::of_index`, `chain`, `codeword`, `encode`, `wots_leaf` |
| `Trees.lean` | `path_root`, `tree_root`, `fors_root` |
| `Verify.lean` | `path_range`, the loop over the layers, `verify` given the theorems above |
| `Theorem.lean` | the composition |

## What it rests on

`#print axioms verify_eq_verifyWithKeccak` gives `propext`, `Classical.choice`, `Quot.sound`, `keccak256.absorb` and `keccak256.digest_of`. No `sorry`, no `native_decide`, no `bv_decide`, no option set.

- **`SpongeSpec`, the hypothesis.** `keccak256::absorb` XORs a rate block into the state and applies Keccak-f[1600], and `digest_of` reads the first 32 bytes off the state. Both are opaque in the extraction (axioms with no body), so the hypothesis cannot be discharged in Lean. Everything above them is proved: the hasher's buffering, `block_of`, the padding of `final_block`, the rate.
- **The patches.** The theorem is about the patched Rust (`crates/{lean_sphincs,keccak256}/proofs/*/patches/pre`), not the committed Rust. `hax.sh test` runs the crates' tests on the patched source; nothing in Lean relates the two.
- **The toolchain and its models.** Charon, Aeneas (here a fork, pinned in `lakefile.toml`, for Lean v4.36.0), the hax Lean library's models of `core`, and `CoreModelsExt`.
- **How Rust values are read.** `toPublicKey`, `toMessage` and `toSignature` (`Defs.lean`) are definitions to be read, not proved. They are total and `toDigest` is injective, so distinct Rust inputs are distinct statement inputs. The byte encodings (`from_bytes`, `to_bytes`) are not covered.
- **The portable path.** The extraction is of the code with hardware features off.

## What the proofs found

No disagreement between the Rust and the statement: byte and bit orders, the address layout, the digest's fields, the codeword and its sum, the chains, the folds and the layer paths all match. What the work did turn up is about the approach:

1. **The verified `verify` is not the shipped `verify`.** Every loop on its path is patched: `path_range`, `of_index`, `codeword`'s sum and `h_msg` are rewritten to indexed loops, and `tree_fold` and `fors_recover` are replaced by `tree_root` and `fors_root`, new functions that drop the visitor. The second is not a mechanical rewrite. The link to the committed Rust is the test suite.
2. **`debug_assert!` is extracted as a hard assertion.** `chain` panics in the model when `start + steps >= CHAIN_LEN`; a release build has no such check. The proof shows it cannot fire from `verify`, so nothing is lost here, but a function proved "total" in the model can be stricter than the binary, and one that is not total in the model may still run in release.
3. **Opaque items are uninterpreted, not specified.** `absorb` and `digest_of` are opaque because Aeneas does not translate `iter_mut().zip(..)` and `as_chunks_mut`, not because they are hard: an indexed-loop patch of each would leave only the permutation (`lanes::permute`, per-architecture) assumed.
4. **A hand-written model is on the path.** `Ord::min` in `Hasher::update` resolves to `core.cmp.Ord.min` in `CoreModelsExt/Core.lean`. It is right for this use, and it is trusted.
5. **Library models are heavier than the Rust.** `array::repeat` builds a sequence and removes its head `N` times, `copy_from_slice` is a `mapM` of `clone`, `as_flattened` fails past `usize::MAX` bytes, constants are computations that have to be proved to return. Each had to be given an equation before use (`Common.lean`); none was found wrong.
6. **The mutable-borrow return of `update` matters.** `Hasher::update` returns `&mut Self`, which Aeneas gives as a value and a back-function. The proofs need that function to be the identity, which it is in the extraction; an assumption placed on an opaque `update` would have to say so.
7. **Reduction is a hazard.** A hypothesis whose type is a `match` on the statement's verifier makes Lean's linters and `omega` try to evaluate Keccak. The proofs keep such terms generalized. Rewriting under a `usize` literal's bound proof silently does nothing in places, hence the `erw`s.
8. **Two hypotheses of `Defs.lean` are unused.** `k.layer.val < 2 ^ 32` in `KeyAdrsSpec` and `TreeAdrsSpec`: the Rust's `as u32` truncates and so does the statement's address.
9. **`wots_leaf`'s codeword is unconstrained.** `WotsLeafSpec` speaks of the leaf alone, which is all `verify` uses.
10. **Width.** Nothing depends on `usize` being 64 bits; the proofs use `2^32 <= usize::MAX + 1` at most.
