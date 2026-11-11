# crates

One directory per workspace crate, named as in `../../../crates`. `bench` has none: the prover never links it. `_template/` starts a new one. `../tools/check-layout.py` fails while a workspace crate has no directory.

## States

Each directory provides one Lean library, named as hax names it (`LeanvmCore` for `leanvm_core`). `crate.toml` says which state provides it:

| `state` | Library source | Written by |
|---|---|---|
| `extracted` | `extraction/`, the whole crate | hax, then `patches/post/` |
| `scoped` | `extraction/`, the items reachable from `start_from` | hax, then `patches/post/` |
| `stub` | `stub/<lean_lib>.lean` | hand, only what dependents reference |

`scoped` is for a crate that does not extract whole but whose items a dependent needs: aeneas emits only the crate it runs on. Leaving `stub` deletes `stub/`, adds `extraction/` and moves the library's `srcDir`; dependents import the same name.

Every crate is an empty stub today.

## Inside `extraction/`

hax's own layout, so the generated imports resolve unchanged:

```
<Lib>.lean                 root, by hand: imports Extraction (and Assumptions/Mirror)
<Lib>/Extraction.lean      hax
<Lib>/Extraction/          hax, then the post patches; never edited
  Types.lean  Funs.lean
  *External.lean             imports of Assumptions/*External
  *External_Template.lean    what Assumptions/*External must declare; not built
<Lib>/Assumptions/         by hand
  TypesExternal.lean  FunsExternal.lean
  Mirror.lean                transcriptions of items the extraction does not produce
```

## Hand-written bodies

A declaration in `stub/` or `Assumptions/` is either:

- **`opaque`**: assumed, its docstring saying why; or
- **mirrored**: a transcription of one Rust item, listed as a `[[mirror]]` in `crate.toml`. A pre patch that lets the extractor translate the item is preferred.

Never an `axiom`.

## Imports

A crate imports only itself, its Cargo dependencies' libraries (optional ones excluded), `Aeneas`, `CoreModels` and `HaxExt`.

## Patches

- `patches/pre/NNN-slug.patch`: on the Rust, gated on `cfg(hax_backend_lean)`, applied before hax and reverted after.
- `patches/post/NNN-slug.patch`: on the generated Lean, applied after hax.
