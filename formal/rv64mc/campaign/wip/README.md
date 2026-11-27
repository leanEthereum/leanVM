# Unfinished proof files

Each file here is a proof module that was being written when the campaign stopped. They sit outside `Rv64mc/` so that the library's build (which builds every file under `Rv64mc/`) ignores them. To resume one, copy it to the same path under `formal/rv64mc/` in your worktree, finish it, and commit it there; delete it here in the same commit.

## `Rv64mc/Proof/Transcript/SumcheckRoundPolyT.lean`: `Transcript::sumcheck_round_poly` (107), track T2

- 817 lines. `lake env lean` stops at the main theorem `kept` (lines 795 to 817): `pro_ok`'s implicit `ret` is not determined, and two of its arguments are still `sorry`; the parts before it elaborate. Everything else (the parts, their invariants) was written in the stopped run and has not been reviewed.
- It imports `Rv64mc.Proof.Field.ESumCopiedSafeT` (in the library: `E::sum` over a copied slice for a possibly empty slice, which `VecT` does not make `Live`).
- Shape (from `defences/runW6f.md`, "Not done (pass 2)"): 13 calls (`next_scalars`, `next_scalar`, `grind_check`, `grinding_bits`, `<[Vec<E>]>::concat`, `E::mul`, `E::sum`, `alloc`, `panic_nounwind_fmt`) with the transcript threaded through; one call per executor run, about seven parts with invariants in the style of `Proof/Whir/RingSwitchT.lean`'s `base_call`.
- It unblocks `sumcheck` (85), which seven functions wait on (`plan.py`): finish it first.

## `Rv64mc/Proof/Layout/BytecodeT.lean`: `Flushes::bytecode` (195), track T1

- 628 lines. `lake env lean` gives application type mismatches at lines 512 to 513 and 603 to 604 and an unsolved goal at 512; the parts before elaborate. Not reviewed.
- Shape (`defences/runW6g.md`, "Not done"): `alloc(24 (1 + len))`, two `Vec<Form>::spec_extend`s into it (`SpecExtendFormT`; one source the 24-byte block `constant` filled, one the argument vector), a drop, `gpow`, `col`, `counted`.
- Every `flushes_*` builder (187 to 191) waits on it.
- Its postcondition is `StateDerivedT.PostT`, which is not enough for `tables` (175): see `PARALLEL.md`, track T1, first item. Decide that first, then finish this file against the stronger postcondition.
