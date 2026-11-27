# leanXMSS's `verify`, proved from its extraction

The Rust `verify` of `crates/lean_xmss`, as hax extracts it, is leanXMSS verification as the statement defines it (`formal/Statement/LeanXmss.lean`), the function the end statement's unforgeability is about:

```lean
theorem verify_eq_verifyWithKeccak (pk : lean_xmss.scheme.LeanXmssPublicKey)
    (m : Array Std.U8 32#usize) (sig : lean_xmss.scheme.LeanXmssSignature) :
    lean_xmss.scheme.verify pk m sig =
      ok (verifyWithKeccak (toPublicKey pk) (toMessage m) (toSignature sig))
```

It says two things: `verify` returns on every input (no panic, no overflow, no index out of range), and what it returns is the statement's verdict on the values its arguments stand for. It has no hypothesis: every function on the path is extracted with its body, down to the Keccak-f[1600] permutation.

```sh
formal/extraction/hax.sh extract                       # the extraction is generated, not committed
(cd formal/extraction/proofs/lean_xmss && lake build)
```

`hax.sh check` builds it after the extractions, scans it for escapes and compares the theorem's axioms with the three below.

## Layout

| file | what it proves |
| --- | --- |
| `Defs.lean` | how a Rust key and signature stand for the statement's |
| `Common.lean` | `u32::to_le_bytes` and `u128::to_le_bytes`, as the statement's `littleEndianBytes` |
| `Popcount.lean` | `u128::count_ones`, a loop in the library's model, and the digit sum two of them give |
| `Hash.lean` | `address`, `hasher`, `th`, `th_digests` |
| `Wots.lean` | `layer_hi`, `tweak`, `Tweak::step`, `chain`, `chain_ends`, `is_codeword`, `codeword`, `message_digest`, `wots_leaf` |
| `Verify.lean` | `node`, `layer_root_unwatched`, `layer_index`, `verify`, given the hasher |
| `Theorem.lean` | the composition, with the hasher proved |
| `Injective.lean` | `toPublicKey` and `toSignature` are injective |

The hasher, the permutation under it, the Merkle fold `keccak256::path_root` and the Rust library models both schemes' proofs step through are in `../keccak256` (`Keccak256Proofs`), which this package and `../lean_sphincs` require. The lemmas here are stated over any permutation `π` the hasher computes Keccak-256 over (`HasherSpec π`); `Theorem.lean` gives them the one proved, `hasherSpec_of_sponge spongeSpec`.

## How Rust values are read

`toPublicKey`, `toMessage` and `toSignature` are definitions to be read, not proved:

- a `[u8; 16]` (a digest, the public parameter, a randomizer) is the `BitVec 128` whose `littleEndianBytes 16` are its bytes (`toDigest`), and a message `[u8; 32]` the `BitVec 256` likewise (`toMessage`);
- the public key is its `merkle_root` and its `public_param`, in the statement's order `⟨root, parameter⟩`;
- the signature's `leaf_index: u32` is the statement's `LeafIndex`, a number below `2^32`, with the same value; `bottom` is the statement's layer `0` and `top` its layer `1`; a layer's `chain_values[i]` and `path[z]` are the statement's `chainValues i` and `authenticationPath z`.

They are total, and injective (`toDigest_inj`, `toMessage_inj`, `toPublicKey_inj`, `toSignature_inj`): distinct Rust inputs are distinct statement inputs.

## What it rests on

`#print axioms verify_eq_verifyWithKeccak` gives `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no `native_decide`, no `bv_decide`, no option set, and no hypothesis.

- **The patches.** The theorem is about the patched Rust (`crates/{lean_xmss,keccak256}/proofs/*/patches/pre`), not the committed Rust. Nothing in Lean relates the two. What does is tests, which `hax.sh test` runs on the patched source: the patch ships a test of each item it rewrites or adds against the code it replaced (`layer_root_unwatched` against `layer_root` with a counting visitor and `verify` against the source's `verify`, on real signatures and tampered ones; `chain_ends` against the batched form), and its heading records the deliberate break of the rewrite each was seen to fail on. That is agreement on the inputs tried, not a proof. leanXMSS has one patch, and the proof needed no change to what it extracts.
- **Which permutation.** As for leanSPHINCS: the extraction is of `keccak256`'s portable `permute`, on every host. The x86-64 body and the AVX-512 one are not covered.
- **The toolchain and its models.** Charon, Aeneas (here a fork, pinned in `lakefile.toml`, for Lean v4.36.0), the hax Lean library's models of `core`, and `CoreModelsExt`.
- **hash-specs**, as a pivot only, inside `Keccak256Proofs`.

## What is not covered

- **The `verify` a `std` build runs.** With the `std` feature, `chain_ends` walks the chains in batches through `th_digests_many` and `keccak256::hash_many`, whose body is per-host SIMD. The patch gives every build the `no_std` form, a `from_fn` of `chain` per chain. That the two agree is the claim of a test, not a theorem: the patch keeps the batched form for tests only, as `chain_ends_batched`, and `chain_ends_matches_the_batched_one` compares the two on both layers, with every digit value on every chain and on a real signature's codeword (`hax.sh test` runs `cargo test -p lean_xmss` on the patched source).
- **The visitor.** `verify` calls `layer_root` with a visitor that does nothing; the patch calls `layer_root_unwatched`, the same fold through `keccak256::path_root`, which has no visitor parameter. `layer_root` itself, which the aggregation crate's hints (`crates/aggregation/src/hints.rs`) and `from_cache_bytes` call, is not what is proved.
- **Everything but verification**: key generation, signing (`wots_sign`, the randomizer grinding of `least_trial`), the trees and their cache, and the byte encodings (`to_bytes`, `from_bytes`, serde). A signature is the Rust struct, not its 2404 bytes.

## To do: EthLib's specification

The theorem's right-hand side is leanVM's own statement, `formal/Statement/LeanXmss.lean`. [#885](https://github.com/leanEthereum/leanVM/pull/885) replaces that statement by [EthLib](https://github.com/ethereum/EthLib)'s. When it lands, this theorem is to be restated against EthLib's verifier and the proofs repaired. `../lean_sphincs/README.md` says how EthLib's specifications differ in shape: bytes for little-endian bit vectors, `Vector` for functions on `Fin`, a hash on bytes for a permutation with the sponge around it.

## What the proofs found

No disagreement between the Rust and the statement: the address layout, the byte orders, the layers' flag, the digest's digits and their sum, the chains and their step addresses, the leaf, the path fold with its node indices, and the two layers' key indices all match. What the work did turn up:

1. **No patch was needed for the proof.** `chain` is `(start..start + steps).fold(..)` with a closure, `chain_ends` and `codeword` are `from_fn`s of closures, and `codeword` goes through `bool::then`. All are proved as extracted, with the fold and `from_fn` lemmas leanSPHINCS's proofs already had. The one patch is the one the extraction needs.
2. **`debug_assert!` is extracted as a hard assertion**, three times on the path: `tweak` (`t < 32 && hi < 1 << 24`), `Tweak::step` (`step < 8`) and `chain` (`start + steps < CHAIN_LEN`). A release build has none of them. The proof shows none can fire from `verify`. Likewise `layer as u32 * TOP` in `layer_hi` and the shift in `layer_index` panic in the model where a release build wraps or masks; `verify` calls them with layers 0 and 1 only.
3. **Of `tweak`'s two asserted bounds, the address needs one.** `address` agrees with the statement's `addressBytes` for every `hi` and every `step`: the Rust keeps three bytes of `hi` and, the shift being on a `u8`, three bits of `step`, as the statement's 24-bit and 3-bit fields do. It needs `t < 32`: above that the Rust ORs the type's high bits into the step's, where the statement keeps five bits of the type. Every type on the path is a constant below 13.
4. **The layers' flag is an OR in the Rust and a sum in the statement.** `layer_hi` is `field | (layer * 2^23)`, `layerHi` is `field + 2^23 * layer`. They agree when bit 23 of `field` is clear. In verification `field` is 0 or a tree level, at most 16. In key generation it is a chain pair below 29. The statement would differ from the Rust at a `field` of `2^23` or more, which no call makes.
5. **`count_ones` has a body.** The hax library models `u128::count_ones` as a loop over a `Range<u32>`: 128 shifts and masks. Its `next` had no specification for `u32` (`range_next_spec_u32`, here), and `is_codeword` calls it twice. The digit sum is then arithmetic: `popcount(d & LOW) + 2 * popcount(d & !LOW)` over 128 bits is the sum of all 64 base-4 digits, which is the statement's sum of the first 58 only because the test `d >> 116 == 0` comes first. `LOW = u128::MAX / 3` is a checked division in the model, and is `0b0101…01`.
6. **The two directions of little-endian bytes are modelled differently.** `u128::from_le_bytes` is a primitive (Aeneas's `BitVec.fromLEBytes`); `to_le_bytes` is a `from_fn` of a closure that shifts by `8 * i % 128`. Each had to be given an equation (`Common.lean`); neither was found wrong.
7. **`wots_leaf`'s and `layer_root`'s codeword is unconstrained.** The theorems speak of the leaf and the root, which is all `verify` uses. The codeword they also return, which `layer_root`'s other callers read, is not specified here.
8. **Casts that could truncate do not.** `e as usize` needs `usize` of 32 bits or more; `j as u32` in the node closure is exact because a node's index is at most its key's, a `u32`; `level as u32` is at most 16. Nothing depends on `usize` being 64 bits.
9. **The statement's totalizations are never reached.** `walkChain` gives `0` past the last step and `treeFold` reads a sibling `0` past the height. `verify` walks `3 - x_i` steps from `x_i ≤ 3` and folds exactly 16 levels, so neither default is part of what is proved equal.
10. **Constants are computations.** `CHAIN_LEN`, `V`, `TOP` and `LOW` are extracted as `RustM` values (a shift, a subtraction, a division that could fail) and have to be proved to return before use.
