# What the extraction leaves out

The extracted crates typecheck in Lean with no `sorry`. Extracted is not the same as faithful, though: some Rust is only described by a signature, some is rewritten before extraction, and some is out of reach by design. This file says what and why. The authoritative lists are each crate's `hax.toml` (what is opaque or excluded, grouped by reason) and `patches/pre/` (what is rewritten); `report.sh` counts them.

## Coverage by crate

| crate | extracted with bodies | left opaque |
| --- | --- | --- |
| `keccak256` | the streaming `Hasher`, the sponge step and the digest, Keccak-f[1600] on one state (the permutation over the lane type `u64`), the scalar helpers and the Merkle path fold | `final_state`, `hash_from_state`, and the batched entry points of `lanes`, which pick a vector lane type per CPU; the vector lane types and the batching generic over them are left out |
| `lean_xmss` | `verify` and everything it calls, down to `keccak256::Hasher`: tweaks, the message digest, WOTS+C codewords and chains, the tree's node; most of the rest of the tree code | `wots_sign`, the tree's `levels` and `subtree`, the `Mutex` cache, `to_bytes`, key generation from an RNG |
| `lean_sphincs` | `verify` and everything it calls, down to `keccak256::Hasher`: tweaks and addresses, the message digest, WOTS+C codewords and chains, FORS and the hypertree | `sign`, the folds that show their nodes to a visitor (`fors_recover`), the byte encodings, key generation |

`lean_sphincs` and `keccak256` are patched on the path of leanSPHINCS's `verify`: sums, chunk loops and the sponge step by index, and a Merkle fold with no visitor. The permutation's rounds are extracted as written, with two changes around them (`keccak256`'s patch 04). `lanes.rs` has one `permute` for x86-64, which alternates between two states, and one for every other architecture; the patch gives every host the second, so the extraction is the same everywhere, and on x86-64 it is not the body that runs there. And the two `Lane` methods that only batched hashing uses, whose default bodies Aeneas does not translate, move to a trait of their own, so the permutation's trait has no method without a body. `verify` passes a visitor that does nothing, and Aeneas translates neither that closure (it mistypes the `FnMut` of a closure returning `()`) nor a visitor passed on as `&mut visit`, so the patch gives `verify` the same fold without the parameter (`path_root`, `tree_root`, `fors_root`). That one is not a mechanical rewrite: what it claims is that a fold calling a visitor that does nothing computes what the fold without one does.

Everything else the toolchain rejected in the three signature crates was left opaque mechanically by `repair.py`, under the "Not yet triaged" heading of each scenario, with no patch or model attempted. Those entries are the first work to take up. Most are missing standard-library models (`as_chunks`, `Iterator::sum`, `IterMut`, `split_first_chunk`, `RangeInclusive`) that one addition to `CoreModelsExt` would clear in several crates at once.

Not extracted: `verifier`, the prover trees (`stable_prover/*`, `experimental_*`), `aggregation`, `zkdsl_compiler`, `isa`, `claims`, `fiat_shamir_prover`, `lean_da`, `lean_vrf`, `lean_vm`, `allocator` and `bench_harness`. The pipeline handles a crate that depends on other extracted crates, so each is a `hax.toml` away, at the cost of its upkeep.

## Out of scope by design

- **Hardware-specific code.** The extraction is of the portable code paths: `hax.sh` switches off the features the crates dispatch on (`aes` and `sha3` on aarch64; x86-64's are off once `target-cpu=native` is overridden), so every `cfg(target_feature)` choice takes its fallback. Items under a bare `cfg(target_arch)` differ between hosts, so they are excluded or opaque.
- **`unsafe`, raw pointers and uninitialized memory.** Aeneas does not dereference raw pointers; such items are opaque.
- **Concurrency.** Thread pools, atomics, thread-locals and `OnceLock`/`Mutex` caches are opaque.
- **The environment.** The global allocator, environment variables, timing, `tracing` spans (stripped where they wrap extracted code), terminal output.
- **Floating point.** Aeneas has no `f64` arithmetic.
- **Randomness and serialization.** Key generation (`rand`) and the serde wire formats are excluded or opaque.

## Across crates

Aeneas translates only the crate it runs on, and emits nothing for the items a crate uses from another workspace crate: it expects them declared elsewhere. They are: each extraction imports the extractions of the crates its crate depends on (`wire.py` derives the list from `cargo metadata`), so an item of another crate is that crate's own translation, with its body where it has one, and is opaque only where its own crate leaves it opaque. Nothing across crates is declared by hand. Two seams remain, both bridged by `wire.py` or the scenarios: a constant of another crate is a computation to Aeneas but a value in its own crate's translation, so each use is wrapped in `pure`; and a constant inside a module its crate keeps opaque is not reached by Charon at all (rustc inlines every use), so the scenario names it as a root (`include`).

## Toolchain gaps

Each gap is met by a patch, a model in `CoreModelsExt`, or an opaque item; most are worth reporting to the tool's maintainers.

**Aeneas**

- An early return or `?` inside a loop, or a `break` out of an outer loop, is not translated. 
- Borrows it cannot join or end: loops that hold a shared borrow of borrowed data, structs with `&mut` fields, closures that capture `&mut` state, nested loops over two `&mut` tables.
- The `Iterator` trait: the signatures of `filter`, `copied`, `cloned`, `find` and `unzip` crash the translation of the whole trait, and so does an impl of `Sum` or `Product`, which takes an `I: Iterator`. The scenarios exclude them (`repair.py` adds the excludes when it meets the crash).
- `dyn` trait objects, function pointers, higher-ranked closures and fn items used as closures are not translated, in a body or in a signature.
- A type recursive through `Vec` becomes a nested inductive Lean's kernel rejects.
- `&str` constants, `size_of::<T>()` (emitted without its type), and raw-pointer reads.
- A crate's opaque items are declared at the Lean root under `open <crate>`, not in the crate's namespace, so another crate cannot name them and two crates' can clash; `wire.py` moves them into the namespace.
- Generated names that clash or trip Lean's linters: a field and a module with one name, a local named `lift`, and `__N` for anonymous `const _` items (`mechanical.py` names the assertions).
- Internal errors on some functions, named in their `hax.toml`; each is still to be reduced to a reportable case.

**Charon**

- Name patterns cannot name an inherent impl whose type has a lifetime parameter, nor a disambiguated anonymous item (`_#1`), and split on commas.
- `--targets`, which would select the target to extract for, switches to a multi-target mode that translates differently (and crashes Aeneas on the `Iterator` trait), so the host's target is used, with its features switched off.

**The hax Lean library (CoreModels)**

- No `Iterator` instance for `IterMut` (its write-back return does not fit), and most adapters' methods beyond `next` (`fold` on `Zip`, `Rev` and `Filter`, `all`, `flatten`, `flat_map`, `sum`); no `as_chunks`, `concat`, `RangeInclusive` iteration.
- No `HashMap`, `HashSet`, `BTreeMap`, `Mutex`, `OnceLock`, and few `String` and `str` operations.
- Its interfaces disagree with Aeneas's output in places: Aeneas's builtin `Clone` of a tuple is not CoreModels' `Clone`; `Vec`'s `IntoIterator` takes a different number of type arguments; `fmt` gets a `Formatter` write-back `Debug` and `Display` do not have (`wire.py` drops it).

`CoreModelsExt` holds the models written to fill these gaps, definitions where the Rust is short and `opaque` declarations otherwise.

**hax**

- Its default opaque set names `serde::ser::Serialize`, but the derives resolve to `serde_core`, so it does not apply; the scenarios exclude the serde impls themselves.
- It seeds a new package's `Assumptions/` from the raw template; `wire.py` corrects the seeded declarations on the same run.

## Warnings left in the build

The workspace builds with one Lean linter warning, which cannot be fixed without silencing the linter: `dupNamespace` on `alloc.alloc.Global.Insts.CoreAllocAllocatorClone` (in `CoreModelsExt`), a name the generated code uses, after the Rust path.

## What the patch tests establish

`hax.sh test` runs each patched crate's tests on the patched source, and on its portable paths, the ones the patches rewrite. A suite that passes does not show that a rewrite agrees with what it replaced: it was written before the rewrite, so nothing in it was chosen to tell the two apart. Each patch's heading therefore names the test that calls the rewritten item, and a deliberate break of the rewrite with whether that test caught it (README.md, "Patches").

Every item a patch rewrites or adds has a test, in the patch, against the code it replaced, copied into the test, over inputs that reach every branch: the indexed loops against the iterator forms; `path_root`, `tree_root`, `fors_root` and `layer_root_unwatched` against the folds with a counting visitor; each `verify` against the source's, on real signatures and tampered ones; the `permute` every host is given against x86-64's two-state one; the portable `chain_ends` against the batched one a `std` build runs. Every one of these tests was seen to fail on a broken rewrite. This is agreement on the inputs tried, and nothing in Lean relates the patched Rust to the committed Rust. Not established: the vector lane types' permutation is compared with x86-64's only on a CPU that has them (under Rosetta, where the x86-64 run was made, `u64` alone is); the AVX-512 single-state permutation is compared with nothing; and the batched `chain_ends` and the visitors' folds are tested equal to what is proved, not proved equal.

Naming an anonymous `const _: () = assert!(..)`, as `mechanical.py` does, stops that assertion from being evaluated in the patched build (Rust evaluates a named constant only when something uses it); the unpatched build still checks it.
