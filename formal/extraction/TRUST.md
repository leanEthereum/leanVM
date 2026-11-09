# What is trusted

What, if wrong, could make a claim false without a Lean error. Per crate, add its `opaque` declarations, its `[[mirror]]` transcriptions and its patches.

1. **Lean.** The kernel at `lean-toolchain`, the release the rest of `formal/` uses. `native_decide` is forbidden.
2. **Aeneas and CoreModels**, at the revs in `lakefile.toml`: the Lean meaning of Rust's integers, arrays, slices, `core` and `alloc`. A model is only as faithful as they are. `HaxExt.lean` is trusted the same way.
3. **The extractor**, hax with charon and aeneas at the builds in `toolchain.toml`: trusted to translate faithfully and to drop nothing silently. `charon_args` makes `Debug` bodies opaque. The target is neither x86-64 nor aarch64, so **no AVX2, AVX-512 or NEON path is modelled**; the verifier has none.
4. **The statement** (`../Statement`), which the claims refine, and `Refinement/Spec.lean`, which reads the models' values as the statement's.
5. **The Mathlib cache**, whose `.olean` files `lake build` does not re-check.

Not trusted: the claims (proved, axioms checked against `claims.toml`), the Rust (the object modelled), `.lake/`.
