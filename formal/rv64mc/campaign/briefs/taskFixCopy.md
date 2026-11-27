# Fix: the partial `MemcpySpec`/`MemmoveSpec` are false of the image's code

Worktree: given in the spec (a fresh branch off draft PR #878's head). Lake project formal/rv64mc, warm.

## The defect

`Spec/Runtime/Mem.lean`'s `CopyPost` ends with `ByteFrame m m' dst n`: every byte outside the destination is unchanged. `compiler_builtins`' `memcpy` template (`Gen/Tmpl/CompilerBuiltins/Mem/Memcpy.lean`) moves `sp` down 16 and, on its misaligned path, stores scratch at `[sp+8]` (lines 80, 142, 256) without restoring it; `memmove` stores at `[sp+0]`, `[sp+8]` (lines 28, 88, 208, 270 of its template). So `MemcpySpec` and `MemmoveSpec` (class C, never proved) cannot hold of the image, and every partial `Table` theorem that takes `memcpy (223)` or `memmove (225)` as a hypothesis (`notes/status.md`: "env; memcpy (223)" rows, 47 A functions rest on open leaves) rests on an unsatisfiable hypothesis. Wave 1b found this (its defence D1: formal/rv64mc/campaign/defences/runW1b.md) and stated the total contract with a corrected frame: `Spec/Runtime/MemT.lean`'s `CopyPostT` (bytes off the stack below the entry `sp`, `OffStack env sp b 1`), proved for `memcpy` (`Proof/Runtime/MemcpyT.lean`, `Table/MemT.lean`'s `memcpyT`).

## Deliverables

1. **Confirm or refute** the defect first, by a machine-checked witness: a concrete state from which the template's run violates `CopyPost` (or a proof that `¬ MemcpySpec env (liftProg fns) …` under the environment facts), or an explanation of why it is not a defect. Put the result in the defence.
2. If confirmed: **correct the partial specs** so that they are true and still enough for every partial proof that uses them: weaken `CopyPost`'s frame exactly as `CopyPostT` does (or reuse `CopyPostT`), and likewise for `memmove`. Re-prove every partial proof that uses `MemcpySpec`/`MemmoveSpec`/`CopyPost` (`grep -rln "MemcpySpec\|MemmoveSpec\|CopyPost" Rv64mc --include=*.lean | grep -v Gen/`: about 8 and 3 files) against the corrected spec: their callers' data lies at or above the callee's entry `sp`, so the restricted frame should suffice; say per file what changed.
3. **Discharge the corrected partial `MemcpySpec` at the image** from the total one: a partial contract follows from a total one (look for or prove `HoldsT`/`TContract` to `Holds`/`Contract` with matching posts, generically at Lprog if it is not there), so `Table/Runtime.lean`'s partial instances can take `memcpy` from `Table/MemT.memcpyT` and lose the `memcpy (223)` hypothesis. Update `notes/status.md`'s rows and counts.
4. A short note in `notes/total-correctness.md` or `notes/status.md` on the defect and its fix (no audit-issue numbers).

This is a **statement change** to existing specs: each changed statement must be weaker than (implied by) or equivalent to what the code does, with the old-to-new relation stated in the defence, and no `Holds`, `HoldsT`, end theorem, `MainSpec*` or `EndStatement.lean` statement may change. The full `lake build Rv64mc` once at the end (with MemoryMax=24G, only when `free -g` shows at least 28 GB available), since `Spec/Runtime/Mem.lean` has many dependents.

Constraints: as the campaign's (no `sorry`/`axiom`/`native_decide`; build changed modules with `timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build <modules>`, one build at a time, `free -g` first; never `lake clean`, never delete `.lake` or `Rv64mc/Gen`; style per formal/AGENTS.md, no em or en dashes; commit with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`, do not push).
