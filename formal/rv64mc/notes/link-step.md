# Templates and the link step

`scripts/regen.sh` builds the guest (or takes `--elf`), lifts it with machine-checked's `decompile --to lean --proved` and runs `scripts/gen.py`, which writes `Rv64mc/Gen/` (gitignored): per function a template `Tmpl/<M>.lean`, link modules `Link/<P>.lean` that each hold the link step of up to about 20 functions under the module prefix `P` (`index.tsv`'s `link` column names each function's), plus `Words.lean`, `Index.lean`, `hashes.tsv`, `index.tsv`. `gen.py --diff OLD NEW` lists the templates that changed. A proof imports a template and `Rv64mc.Link.Basic` only (as `Proof/Field/EMul.lean` does), so it is rebuilt only when that function's own code changes.

## The canonical image

`regen.sh` builds the guest in a fresh directory under `out/` (a copy of `guest/`'s sources and `.cargo/config.toml`, the `no_std` copy of `$VERIFIER_SRC`, an empty target dir), removed afterwards, with `CARGO_ENCODED_RUSTFLAGS` set to the guest config's own `rustflags`: Cargo merges `target.<cfg>.rustflags` from every `config.toml` above the build directory, and the repository's adds `-C target-cpu=native`, which changes the code (the old `out/canon.elf`, built in `guest/` with it, differs from the clean build in 128 of 230 templates). The ELF is then a function of the sources and the guest's config: two builds in different directories agree byte for byte. `regen.sh` writes its sha256 to `image.sha256` (committed) and the ELF to `out/canon.elf`; `regen.sh --check` rebuilds and fails if the sha256 or any generated file differs. A plain `cargo build` in `guest/` (and `scripts/build-variant.sh`) still picks up `target-cpu=native` and is not the canonical image.

Canonical image of 2026-11-20 (crates/verifier at 1135c5255): sha256 `8cb4e7b80e7ad696f4cac1f39e33e0cb3907420f0c8cc48805fe6692bdae842d`.

## Design

- Module name: the v0-demangled symbol without crate disambiguators (`scripts/v0demangle.py`), in CamelCase components, `<T as Trait>::m` as `T/AsTrait/M`, generic arguments folded into the last component and hashed past 40 characters; on a collision the instantiating crate, then a hash of the symbol, is appended. `index.tsv` maps module, index, address, size, symbol and key.
- `Link`: `name`, `base`, one `Callee` (index, entry) per distinct callee, named by the shortest unique suffix of its module path (`clmul`, `reduce`); one `Site` (`auipc` value, `jalr` offset) per call, `s0`, `s1`, ... in code order; one `DataRef` (`auipc` value, `lo12` offset, address) per PC-relative address, `d_<symbol>` for a named target, else `d_c<len>_<hash>` over its bytes with each `R_RISCV_64` word replaced by its target's key. Return addresses are `L.base + k`, candidates `[L.f.idx]`.
- `Link.WF` states each field's fact as the equation `lsym`'s simp set uses (`Callee.WF`, `Site.WF`, `DataRef.WF` of `Link/Basic.lean`). The link module proves `tmpl_eq` in m-c's chunks (`getElem?_eq_of_chunks`) and each `WF` field by `kernel_eq`; it does not build m-c's `F<i>` modules.
- Link modules: `gen.py --batch N` (default 20) groups functions by module path. A prefix with at most `N` functions under it is one module `Link/<P>.lean`; a larger one is split by its next component, and the components with fewer than `N / 4` functions stay together in `Link/<P>.lean` (`Link/Misc.lean` at the root). A function's batch depends only on how many functions share its prefixes, so it moves only when a subtree crosses those bounds. Each function's part keeps its namespace, so `<M>.link`, `<M>.tmpl_eq` and `<M>.wf` are unchanged; tables import the batch `index.tsv` names. Templates stay one module per function: they are what keeps proofs from rebuilding.
- `Needs.lean`: each function's frame is the sum of every decrement of `sp` read from its words, `addi sp, sp, -N` or an `add`/`sub` of `sp` and a register holding a constant (`lui`/`addi`/`addiw`/`slli` propagated through straight-line code, forgotten at branch targets; `linear_transpose` allocates 28 KB this way). Restores and setting `sp` to a constant (`_start`) take nothing; any other write to `sp` fails the generator.
- A constant table's `<d>_words` runs to the end of its object, the last doubleword partial when the object ends inside it (its remaining bytes the image's, the doc comment says whether they are zero), and `<d>_words32` gives the same bytes as 32-bit words for tables read with 4-byte loads.
- The generator fails on a call with more than one candidate, `abort`, an `auipc` without its relocation or user, a `lo12` user outside the function, and on any literal left in a template that lies in an allocated section or is a function entry.

## Measurements (2026-11-20, 32 cores shared, load 15 to 25, `LEAN_NUM_THREADS=10` or `12`)

| step | CPU-s | wall |
| --- | --- | --- |
| `decompile --to lean --proved` | 5 | 5 s |
| `gen.py` | 1.1 | 1.2 s |
| `regen.sh --elf` (with `check-relocs.py`) | 7.5 | 8 s |
| 230 `Tmpl` modules, cold | 816 | 99 s |
| `Words` + `Index` + 230 `Link` modules, cold (229 built; one field-name bug, fixed since) | 1,058 | 209 s |
| a clean rebuild of the same sources (`c0`, 128 templates changed) + `Probe/EMul` | 1,511 | 183 s |
| the same, switching to the clean canonical image (`Probe/EMul` unchanged, still proved) | 1,900 | 248 s |
| C1 (`eq_eval`: `ONE + x + y` to `ONE + x * y`) | 971 | 160 s |
| C2 (`MerklePath::root` with a rotating index and a tuple-chosen order) | 995 | 158 s |

Largest modules: `Tmpl` `verify_bus_balance` 14 s, `verify_whir::<..>` and `walk` 10 s; `Link` `verify_whir::<..>` 22 s, `walk` 18 s, `flushes_keccak` and `verify_bus_balance` 12 s; `Words` 51 s. Peak RSS of one module 2.2 GB. About a quarter of every module's CPU is system time loading imports.

Iteration, both from `c0` (a clean build of the canonical sources): C1 changes 1 template (`Verifier.Multilinear.EqEval`), 161 `Link` files and `Words.lean`; C2 changes 1 template (`Verifier.Merkle.MerklePath.Root`) and 138 `Link` files. Every `Link` module imports `Words`, which changes with any code change, so all of them are rebuilt: the link step is the fixed floor of a change. `Probe/EMul` is not rebuilt in either.

## Batched link modules (2026-11-23, 32 cores shared, load 33 to 48, 6 modules at once)

Every link module rebuilt (its sources regenerated, `Words` and templates built), `lake build Rv64mc.Gen.Link`, by batch size `N` of `gen.py --batch`:

| `N` | modules | CPU-s | wall |
| --- | --- | --- | --- |
| one per function (before) | 231 | 1,144 | 321 s |
| 10 | 46 | 495 | 105 s |
| 16 | 26 | 429 | 119 s |
| 20 | 20 | 288, 367 (two runs) | 63 s, 84 s |
| 30 | 17 | 378 | 105 s |
| 40 | 12 | 358 | 124 s |

Past 20, one batch dominates the wall time (`Verifier.Layout`, 24 functions, then `Verifier` with 42 at `N = 40`) and the CPU stops falling. Every batch at `N = 20` costs half or less of its functions built one per module.

Iteration harness (`iterate.sh`, the same day, before at `2fd6731ef`, after at `3299473ac`):

| | before | after |
| --- | --- | --- |
| C0 (no change) | 211 CPU-s, 195 s | 205 CPU-s, 188 s |
| C2 (`MerklePath::root`), total | 1,638 CPU-s, 619 s | 850 CPU-s, 376 s |
| C2, link step (`Gen.Link` and `Words`, `Index`, ...) | 1,140 CPU-s | 434 CPU-s |
| C2, `lake build` | 1,469 CPU-s, 462 s | 678 CPU-s, 217 s |

Cold build of `Rv64mc.Gen` (`Words`, `Index`, every template and link module): 2,226 CPU-s and 454 s before (link modules 1,165), 1,549 CPU-s and 398 s after (link modules 341); the templates (about 1,000 to 1,150 CPU-s) now set the wall time.

## Limits found

- The first `out/canon.elf` was built under the repository's `-C target-cpu=native` (an unrecognized CPU for RV64, yet different code: register allocation, for instance in `<E as Mul>::mul`); fixed as above.
- A data reference is keyed by its bytes, so a changed constant table changes the templates of its users, as it should. The image holds no panic locations (no file names or lines in `.rodata`); if a build brought them back, moving lines would change the templates of the functions below.
- The floor is the whole link step, since every link module imports `Words`. Its cost was mostly per module, not kernel evaluation: the kernel reduces `(liftProg fns)[i]?` lazily, decoding and lifting function `i` alone, and `entryOf` scans the 230 bases once per call site (about 40% of the kernel time of a call-heavy function such as `walk`). Each module also starts Lean and imports `Tools.ToLean`, which imports all of `Lean` (about 3 CPU-s, against under 1 for a trivial file). One module per function paid that 230 times; `gen.py` now writes about 20 functions per module (above).
- A relocatable lift theorem in machine-checked (`liftFn` parametric in the callee entries a function reads) would let a link module check one function against its own words and a local entry table, without `Words` and without the `entryOf` scans. That saves part of the kernel time, not the import cost, which batching removes.
- A callee field named like a Lean token (`stack`, `next`, `at`) needs `«»`; `gen.py` escapes callee fields in the link module's values and a fixed list in templates.
- Every proof imports a generated module: run `regen.sh` before building.
