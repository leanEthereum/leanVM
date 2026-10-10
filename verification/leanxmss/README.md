# leanXMSS guest verification

A Lean 4 proof that the leanXMSS guest (`programs/leanxmss/guest`) verifies signatures exactly as the Ethereum XMSS specification ([`ethereum/cryptography-specs`](https://github.com/ethereum/cryptography-specs/tree/d1331f02e308fe6d0aedda8601e4d5b0fc360318/EthCryptographySpecs/Xmss), `EthCryptographySpecs/Xmss`) does, and that its `main` commits exactly the claims of the valid signatures its advice holds.

The guest's Rust source is translated to Lean by [Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas); the proofs are about that translation.

## What is proven

`LeanxmssProofs/Verify.lean`, for every public key, leaf index, message and signature:

- `verify_spec`: the guest's `verify` returns, and never panics, `Ok(())` when the specification's `verify` accepts, `Err(InvalidEncoding)` when the specification's target-sum encoding finds no digits, and `Err(InvalidMerklePath)` otherwise.
- `verify_ok_iff`: the guest's `verify` returns `Ok(())` if and only if the specification's `verify` returns `true`.

The guest holds values as little-endian 64-bit words and the specification as bytes; `LeanxmssProofs/Statement.lean` maps one to the other (a value's words' bytes are its bytes), and `LeanxmssProofs/Words.lean` proves these maps onto (`publicKey_onto`, `signature_onto`, `message_onto`, `randomness_onto`, `epoch_onto`; one to one is `Statement.bytes_inj`), so the theorems cover every input of the specification.

On the way, each part of verification is proven equal to the specification's:

| Guest (`lib.rs`) | Specification | Lemma |
| --- | --- | --- |
| `tweak` | `makeTweak` | `Tweak.lean`: `tweak_spec` |
| `tweak_hash` | `tweakHash` | `Hash.lean`: `tweak_hash_spec` |
| `encode`, `Digits::get`, `Digits::sum` | `wotsEncode` (both spare bits zero, digits summing to 195) | `Encoding.lean`: `encode_spec` |
| `Chains::walk`, `wots_leaf` | `chain`, `otsRecover`, `otsLeaf` | `Leaf.lean`: `wots_leaf_spec` |
| `merkle_root`, `merkle_node` | `computeRoot`, `climbStep`, `merkleNode` | `Merkle.lean`: `merkle_root_spec` |

`LeanxmssProofs/Main.lean`, for every advice (a list of words):

- `main_spec`: a run of `main` succeeds exactly when the advice holds a count `n` and `n` entries of 160 words (key, leaf index, message, signature, read as `main` reads them), each with a leaf index below `2^32` and a signature the specification's `verify` accepts; it then commits, in order, each entry's claim: the key's root and public parameter, the leaf index (the whole word read), and the message. The run's output is the BLAKE2s digest of the committed words (`output`), as `PublicValues` computes it.
- `main_terminates`: a run commits or panics.

`scripts/Axioms.lean` prints the axioms each theorem rests on.

## Status

Everything above is proven except one lemma: `encode_spec` (`Encoding.lean`), the target-sum encoding, is stated and used but still has a `sorry`, with two of its sub-lemmas (`fold6`, `fold12`, the last two folds of `Digits::sum`'s field-wise digit sum). So `verify_spec`, `verify_ok_iff`, `main_spec` and `main_terminates` rest on it (`scripts/Axioms.lean` shows `sorryAx` for them and for nothing else); `tweak_hash_spec`, `wots_leaf_spec`, `merkle_root_spec` and the `Words.lean` theorems are complete. Proven toward it: `Digits::get` (`get_ok`) and the first step of `Digits::sum` (`land_even`, `land_odd`). What remains: the two folds, relating the digest's words to the specification's `digestWord`, `padded` to the guest's top-bit test, and the 42-term `onTarget` sum to `Digits::sum`. A monolithic `bv_decide` of the SWAR identity does not finish in 10 minutes.

## What is trusted

- **Charon and Aeneas**: that the Lean translation in `Leanxmss/Types.lean` and `Leanxmss/Funs.lean` means what the Rust means (with Rust's debug semantics: an overflowing `+` or a shift past the width is a panic; the proofs show none happens).
- **The closure patch** (`scripts/patch_closures.py`): five rewrites of the translation of the guest's three closures, which make it type-check. Aeneas translates each closure body correctly but types its trait instance with the `FnOnce`/`FnMut` model of its library, which has no room for the final value of a mutable borrow a closure takes or captures ([aeneas#1046](https://github.com/AeneasVerif/aeneas/issues/1046), [aeneas#961](https://github.com/AeneasVerif/aeneas/issues/961)). The patch routes those values: the final `Stream` to `hash_with`, the closure's next state to its caller. Each rewrite is explained in the script.
- **The SDK models** (`Leanxmss/FunsExternal.lean`, `Leanxmss/TypesExternal.lean`): the guest calls the SDK's `Template::new`, `Template::write`, `Template::digest`, `Template::chain`, `Stream::write` and `hash_with`, whose bodies are raw pointers, `MaybeUninit` and inline assembly that Aeneas does not translate. Charon translates the guest against `shim/` instead, a crate with the same names and signatures and no bodies, and these functions are opaque: each has a Lean model, the function it is meant to compute, over the message bytes it builds. A template is its `8 W` message bytes and its digest is BLAKE2s-256 of them; `write` splices a value's little-endian bytes in at a byte offset, panicking unless aligned and inside the message; `chain` writes the counter and the value and takes the first two words of the digest, once per counter; `hash_with` is BLAKE2s-256 of the words its closure writes. BLAKE2s-256 is the specification's own `Blake2s.hash`. The shim differs from `sdk/` in two signatures only: its `Stream` holds no borrow (`sdk/`'s holds the block it writes, which Aeneas cannot pass to a closure), and its `Plain` trait names a value's size, alignment and bytes, so that one model of `write` covers every type.
- **The VM and the SDK below the models**: that the `blake2s` custom instruction is RFC 7693's compression function, that `sdk/`'s templates, streams and `precompile.rs`'s hand-written chain loop compose it into BLAKE2s-256 as the models say, and the RISC-V semantics. Tests back this: `sdk/src/blake2s.rs`'s check the SDK's hashing (the portable compression in place of the instruction) against a reference BLAKE2s, and `programs/leanxmss/host`'s run the guest on the VM against its native build and pin its keys and signatures to the specification's implementation.
- **`main`'s transcription**: Aeneas has no model of `read` and `commit`, which act on the VM's memory, so `main` (16 lines) is transcribed by hand in `Main.lean`: a read takes the next words of the advice and panics past its end, `PublicKey` and `Signature` are read as their `repr(C)` word layouts, and the committed words are the result. It calls the translated `verify`.
- **The specification**: `Spec/` is its `Xmss` modules, verbatim at the pinned commit (`scripts/check-spec.sh` checks), compiled with this project's Lean version.
- Lean's kernel and the axioms `scripts/Axioms.lean` lists.

## Versions

| | Version |
| --- | --- |
| Specification | `ethereum/cryptography-specs` at `d1331f02e308fe6d0aedda8601e4d5b0fc360318` |
| Guest | `programs/leanxmss/guest` of this commit |
| Aeneas | `nightly-2026.10.07-aa66752` (commit `aa66752b15d02335f936f607b5ad5b9fecb65b13`), binary and Lean library |
| Charon | 0.1.279 (commit `c8f15d7d658c86a95658f71ad99cddd4be002e04`), shipped in the Aeneas release; Rust `nightly-2026-09-17` with `rustc-dev`, `llvm-tools`, `rust-src` |
| Lean | `v4.31.0` (Aeneas's), Mathlib `v4.31.0` through Aeneas |

The specification pins Lean `v4.29.1` with Mathlib, Aeneas Lean `v4.31.0`: one project cannot depend on both, so the specification's `Xmss` modules, which import nothing but each other, are vendored into `Spec/`.

## Reproducing

Check the proofs (the generated files are committed, so this needs neither Charon nor Aeneas):

```sh
cd verification/leanxmss
lake exe cache get        # Mathlib's prebuilt files
lake build                # the specification, the translation, the proofs
lake env lean scripts/Axioms.lean
./scripts/check-spec.sh   # Spec/ is the pinned specification, verbatim
```

Regenerate the translation from the guest's source (after a guest change):

```sh
gh release download nightly-2026.10.07-aa66752 --repo AeneasVerif/aeneas -p 'aeneas-linux-x86_64.tar.gz'
mkdir aeneas && tar xzf aeneas-linux-x86_64.tar.gz -C aeneas && export PATH=$PWD/aeneas:$PATH
rustup toolchain install nightly-2026-09-17 -c rustc-dev,llvm-tools,rust-src
cd verification/leanxmss && ./scripts/extract.sh && lake build
```

`extract.sh` copies the guest's manifest and source, unchanged, next to `shim/`, runs Charon (`--opaque leanvm_guest --start-from leanxmss::verify`) and Aeneas, applies the closure patch, and writes Aeneas's lists of the opaque items to `Leanxmss/*_Template.lean.txt`: if those change, the models must follow.

## Layout

- `Spec/`: the specification, vendored.
- `shim/`: the SDK signatures Charon translates the guest against.
- `Leanxmss/`: `Types.lean`, `Funs.lean` (generated), `TypesExternal.lean`, `FunsExternal.lean` (the models), `Bytes.lean` (bytes of words, BLAKE2s on them).
- `LeanxmssProofs/`: the proofs, `Statement.lean` and `Verify.lean`, `Main.lean`, `Words.lean` being the statements.
- `scripts/`: `extract.sh`, `patch_closures.py`, `check-spec.sh`, `Axioms.lean`.
