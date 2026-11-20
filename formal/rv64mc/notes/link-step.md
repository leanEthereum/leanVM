# Templates and the link step

`scripts/regen.sh` builds the guest (or takes `--elf`), lifts it with machine-checked's `decompile --to lean --proved` and runs `scripts/gen.py`, which writes `Rv64mc/Gen/` (gitignored): per function a template `Tmpl/<M>.lean` and a link module `Link/<M>.lean`, plus `Words.lean`, `Index.lean`, `hashes.tsv`, `index.tsv`. `gen.py --diff OLD NEW` lists the templates that changed. A proof imports a template and `Rv64mc.Link.Basic` only (as `Probe/EMul.lean` does), so it is rebuilt only when that function's own code changes.

## Design

- Module name: the v0-demangled symbol without crate disambiguators (`scripts/v0demangle.py`), in CamelCase components, `<T as Trait>::m` as `T/AsTrait/M`, generic arguments folded into the last component and hashed past 40 characters; on a collision the instantiating crate, then a hash of the symbol, is appended. `index.tsv` maps module, index, address, size, symbol and key.
- `Link`: `name`, `base`, one `Callee` (index, entry) per distinct callee, named by the shortest unique suffix of its module path (`clmul`, `reduce`); one `Site` (`auipc` value, `jalr` offset) per call, `s0`, `s1`, ... in code order; one `DataRef` (`auipc` value, `lo12` offset, address) per PC-relative address, `d_<symbol>` for a named target, else `d_c<len>_<hash>` over its bytes with each `R_RISCV_64` word replaced by its target's key. Return addresses are `L.base + k`, candidates `[L.f.idx]`.
- `Link.WF` states each field's fact as the equation `lsym`'s simp set uses (`Callee.WF`, `Site.WF`, `DataRef.WF` of `Link/Basic.lean`). The link module proves `tmpl_eq` in m-c's chunks (`getElem?_eq_of_chunks`) and each `WF` field by `kernel_eq`; it does not build m-c's `F<i>` modules.
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
| C1 (`eq_eval`: `ONE + x + y` to `ONE + x * y`) | 971 | 160 s |
| C2 (`MerklePath::root` with a rotating index and a tuple-chosen order) | 995 | 158 s |

Largest modules: `Tmpl` `verify_bus_balance` 14 s, `verify_whir::<..>` and `walk` 10 s; `Link` `verify_whir::<..>` 22 s, `walk` 18 s, `flushes_keccak` and `verify_bus_balance` 12 s; `Words` 51 s. Peak RSS of one module 2.2 GB. About a quarter of every module's CPU is system time loading imports.

Iteration, both from `c0` (a clean build of the canonical sources): C1 changes 1 template (`Verifier.Multilinear.EqEval`), 161 `Link` files and `Words.lean`; C2 changes 1 template (`Verifier.Merkle.MerklePath.Root`) and 138 `Link` files. Every `Link` module imports `Words`, which changes with any code change, so all 230 are rebuilt: the link step is the fixed floor of a change. `Probe/EMul` is not rebuilt in either.

## Limits found

- `out/canon.elf` is not what a clean build of its sources gives: two clean builds in different directories, and an incremental rebuild, agree byte for byte with each other but differ from it in 128 of 230 templates (register allocation, for instance in `<E as Mul>::mul`). The canonical image should come from a clean target.
- A data reference is keyed by its bytes, so a changed constant table changes the templates of its users, as it should. The image holds no panic locations (no file names or lines in `.rodata`); if a build brought them back, moving lines would change the templates of the functions below.
- The floor is the whole link step: `Words` is one module, and each `Link` module's kernel check evaluates `liftProg fns`, which depends on every function's entry through `entryOf`.
- A callee field named like a Lean token (`stack`, `next`, `at`) needs `«»`; `gen.py` escapes callee fields in the link module's values and a fixed list in templates.
- `Probe/EMul.lean` imports a generated module: run `regen.sh` before building it.
