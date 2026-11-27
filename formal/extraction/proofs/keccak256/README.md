# `keccak256::Hasher`, proved from its extraction, and what the scheme proofs share

The proofs about `crates/lean_sphincs` (`../lean_sphincs`) and `crates/lean_xmss` (`../lean_xmss`) both end at the same hasher, `keccak256::Hasher`, and step through the same Rust library models. This package holds that common part, so that each is proved once:

```lean
theorem spongeSpec : SpongeSpec keccakF1600
def hasherSpec_of_sponge {π : KeccakState → KeccakState} (S : SpongeSpec π) : HasherSpec π
theorem keccak256_eq_reference (data : List UInt8) :
    Hash.bytesToBitsLSB (digestBytes (LeanVM.Protocol.KeccakHash.keccak256 data)) =
      Hash.Keccak.Reference.keccak256 (Hash.bytesToBitsLSB data)
```

`spongeSpec` says that `keccak256::absorb` and `keccak256::digest_of`, as extracted, are Keccak's sponge step and digest over the statement's Keccak-f[1600] (`formal/Statement/Keccak.lean`), the permutation `keccak_f` included. `hasherSpec_of_sponge` turns it into what the scheme proofs ask of the hasher (`HasherSpec`, `Defs.lean`): `new`, `update` and `finalize` compute Keccak-256 of the bytes absorbed. `keccak256_eq_reference` checks the statement's own Keccak-256 against another specification: it is the FIPS 202 sponge KECCAK[512] with Keccak's original padding, as [hash-specs](https://github.com/Verified-zkEVM/hash-specs) defines it on bits.

```sh
formal/extraction/hax.sh extract                       # the extraction is generated, not committed
(cd formal/extraction/proofs/keccak256 && lake build)
```

`hax.sh check` builds it with the scheme packages, scans it for escapes and compares the three results' axioms with the `axioms` file: `propext`, `Classical.choice` and `Quot.sound`.

## Layout

| file | what it holds |
| --- | --- |
| `Defs.lean` | Rust's bytes as the statement's (`bytes`, `toDigest`, `toMessage`), and `HasherSpec` |
| `Common.lean` | the library models the extractions call, as equations; bytes read as numbers; the `bv_bits` macro |
| `Library.lean` | more library models: slices of arrays and writing them back, `fill`, `clone`, loops over a range, folds, `from_fn` |
| `Bytes.lean` | `truncate`, digests as numbers, `==` on byte arrays, and that `toDigest` and `toMessage` are injective |
| `Path.lean` | `keccak256::path_root` with any node function is the statement's `foldPath` |
| `Hasher.lean` | `keccak256::Hasher` computes Keccak-256, given `absorb` and `digest_of` (`SpongeSpec`) |
| `Sponge.lean` | `absorb` and `digest_of`, given what `keccak_f` computes |
| `Permutation.lean` | `keccak_f`, the 24 rounds on `u64` lanes, is hash-specs' Keccak-f[1600] on lanes |
| `KeccakSpec.lean` | the statement's Keccak-f[1600] and Keccak-256 are hash-specs', and so FIPS 202's |
| `Keccak.lean` | the three composed: `spongeSpec` |

Everything is in the namespace `Keccak256Proofs`, which the scheme packages open.

## What it rests on

As the scheme packages' READMEs say of their theorems: the patches of `crates/keccak256/proofs/keccak256/patches/pre` (the theorem is about the patched Rust), the choice of `permute` (the portable one, on every host: the x86-64 body and the AVX-512 one are not covered), the toolchain and its models of `core`, and hash-specs as a pivot only.
