# Defence: wave 6d, pass 1: the generic saved-register frame (`SavedT`), `ring_coefficients` (133) and `ring_target` (134) total with `Table` instances; the rest of the list not done

Base: 7b1d3faf0d. Head: 93f6642468 (branch formal/rv64mc-total-w6d, worktree /home/devops/leanEthereum/leanVM-t-symt, 7 commits, not pushed: 4da0ffbd8a `SavedT`, 2f7bb9c5e5 `ring_coefficients`, 7d3ecef0a8 `ring_target` (pass 1); ec9b1ab886 `instance_weights`, 053a1f6c00 `Scaled::new` (pass 2); 11c907ee19 `K::inv`, 93f6642468 `Subspace::new` (pass 3)). The current "Not done" list is pass 3's (below).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Runtime.SavedT Rv64mc.Proof.Whir.Frobenius8SafeT Rv64mc.Proof.Multilinear.ReadSliceT Rv64mc.Proof.Whir.RingCoefficientsT Rv64mc.Proof.Whir.RingTargetT Rv64mc.Table.WhirT6d` -> `Build completed successfully (5386 jobs).` (the last run cached; each module was rebuilt after its last source change; the only warnings in the log are the existing `Proof/Field/Reverse.lean` module-system note; the lakefile has `warningAsError = true`). Single-file `/usr/bin/time -v ... lake env lean`: `RingCoefficientsT` 59 s wall, peak RSS 4.5 GB; `RingTargetT` 37 s, 4.2 GB; the others under 10 s.

Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

## What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 133 | `verifier::ring_switch::ring_coefficients` | `RingCoefficientsT.specT` (safety: the slot `VecT` of 16-byte elements, `vecLen = 8 g.len`, buffer fresh unless capacity `0`; `Out := SretOut 24`, the partial spec's) | Proof/Whir/RingCoefficientsT | WhirT6d.ringCoefficients | env; clmul table |
| 134 | `verifier::ring_switch::ring_target` | `RingTargetT.specT` (safety: returns, `Post := True`, `Out` the default `False`) | Proof/Whir/RingTargetT | WhirT6d.ringTarget | env; clmul table |

Shared pieces (new modules): `Proof/Runtime/SavedT` (item 0), `Proof/Whir/Frobenius8SafeT` (`frobSafe`), `Proof/Multilinear/ReadSliceT` (`rdList`, `ringPsiSafe`, `polyEvalSafe`).

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `152 8410` (base `150 8185`; summary table left to the merge). Each module's `total` and each `Table` theorem has a `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]`.

## Decisions

### D1. `Proof/Runtime/SavedT.lean`: one saved-slot predicate for any slot count
- **What**: `Saved top cs vs M` by recursion on two lists (offsets `cs`, values `vs`): `M.getMem (top + c) = v ∧ Saved top cs' vs' M`, `True` otherwise. `MemOk env top out cs vs m M := env.Frame top out m M ∧ M.code = m.code ∧ env.Static M ∧ Saved top cs vs M`. `SlotsIn K cs := ∀ c ∈ cs, 2^64 - K ≤ c.toNat` (every slot among the `K` bytes below `top`), checked per function by `slots_le` (default argument, the `slots_in` macro: `simp only [...]; omega`). Lemmas proved once, generically: `Saved.keep` (by recursion on the lists, from `hk : ∀ a, top - K ≤ a < top → X a = M a`), `MemOk.call`, `MemOk.fresh`, `MemOk.slot` (frame of `F` bytes, store at `a` with `top - F ≤ a`, `a + 8 + K ≤ top`), `MemOk.next_le`.
- **Why two lists, not a list of pairs**: the side condition `SlotsIn` mentions only the offsets, closed literals; a list of pairs would mix in the symbolic values (`regs .x8`), which the closing tactic cannot evaluate.
- **Why `slots_in` and not `decide`**: as the default argument, both `decide` and `decide +kernel` on a two-offset `SlotsIn` failed with `maximum recursion depth` in a scratch file, and a scratch file trying `simp ...; decide` and `decide +kernel` variants did not finish within 120 s (I did not isolate which); a `repeat`-built tactic (`SlotsIn.cons` per offset) failed on the 13th offset inside the real module (recursion depth, swallowed by `repeat`) though it passed a 13-offset scratch test. `simp only [SlotsIn, List.mem_cons, ..., BitVec.toNat_ofNat]; omega` closes 13 offsets in about a second.
- **Executor (the brief's question)**: `Saved` with literal lists unfolds under `unfoldDefinition?` (smart unfolding) one cons at a time (checked in a scratch `MetaM` run: `Saved top [c1, c2] [v, v] M` unfolds to `M.getMem (top + c1) = v ∧ Saved top [c2] [v] M`), so `rv_introT`'s `splitFact` splits a `Mem` invariant into one equation per slot, ending in an unsplit `Saved top [] [] M`. Observed: at an epilogue with no call since the loop head (`RingCoefficientsT.fin_ok`) the closer restores every saved register from those equations unaided. After calls in the same part (`RingTargetT.fpass`) it left `Holds.post`'s `AbiRegs` open; I closed it by destructuring the head's `Mem` and `simp only [AbiRegs, Tactic.rf]` (a few lines). When a part builds `Mem` from stores, `refine ⟨?_ (15 of them), trivial⟩` followed by `rv_closeT` proves each slot (the final `trivial` is `Saved top [] [] M`). So: usable as is for reading, needs the anonymous constructor with a final `trivial` for building, and a manual `AbiRegs` after calls.
- **Rejected**: rewriting the earlier modules' `Saved`/`MemOk` (the brief says not to: rebuild cost); a `List.Forall`-based definition (its unfolding gives `(c, v).1` projections the closer does not normalise).
- **Claims**: `SavedT` imports only `Tactic.Heap`; its users are `RingCoefficientsT` and `RingTargetT` (each defines `abbrev Mem := Runtime.SavedT.MemOk env top <out> [literal offsets] [ret, regs .x8, ...]` and `slots : SlotsIn K [...]`). No existing module uses it.
- **Evidence**: `grep -rln "SavedT" formal/rv64mc/Rv64mc` lists those three files.

### D2. `ring_coefficients` (133): a safety contract, the functional one owed
- **Definition**: `PreT`: the slot `InWin 24`, 8-aligned, `Owned`; `f` (`a1`) `InWin 128`, 8-aligned; `g` (`a2`, `a3` elements) `n = 0 ∨ InWin g (16 n) ∧ Owned g (16 n)`. `PostT`: `VecT env m' a0 16 ∧ vecLen = 8 n ∧ (vecCap = 0 ∨ next m ≤ vecPtr)`. `Out := SretOut Layouts.Vec.byteSize`, `Stop := AbortStop`.
- **Why**: class C; the functional contract (`Spec.Whir.RingSwitch.coefficientsSpec`) needs value invariants over three loops and `reserve`'s possible reallocation. The caller's safety needs the result's `VecT` (`RingWeightEvaluateT.PreT` asks it of the weight's coefficients header). `f` needs no ownership: its values are only multiplied, never used for an address, so a window and alignment suffice for the loads. `g` is read once, by `memcpy`, which needs it in a window and off the stack below the stack pointer (`Owned` gives that).
- **Finding against the partial spec**: the image passes `f`'s pointer alone in `a1` (the length `RING_MAP_WIDTH = 8` compiled in: the loop runs while `x22 ≠ 0x80`) and `g` as `(a2, a3)`; `Spec/Whir/RingSwitch.lean`'s `CoefficientsPre` reads `f` from `(a1, a2)` and `g` from `(a3, a4)`. Likewise `TargetPre` (`ring_target`) reads `f` from `(a2, a3)` and `g` from `(a4, a5)` where the image passes `f` in `a2` and `g` in `(a3, a4)`. Read from `Gen/Tmpl/Verifier/RingSwitch/RingSwitch.lean` labels 35 to 47 and the two callees' templates' first instructions. Recorded in "Owed by contracts already total"; no statement changed.
- **Cuts**: `total` (entry to pc 96, label 48), `outer` (96, `Total.loop`, measure `k` passes left, `x22 = 16 (8 - k)`), `prods` (126, label 63, `Total.loop`, `j` products left), `frobs` (152, label 76, `Total.loop`, `j` powers left; its exit goes `through [92]` to the passes' head or the exit), `fin_ok` (172, label 86). Nesting as in `NovelBasisT`: `outer`'s body gets `hin k (ih at k - 1)`, built in `total` as `prods (frobs ... hl)`.
- **Invariants**: `CV` (the header at `top - 128`: `len ≤ cap`, `cap * 16 < 2^63`, the buffer fresh since the entry, `≥ 0x10000000`, `ptr + 16 cap ≤ NEXT`, aligned), `PW` (the powers' block: `n = 0`, or fresh, aligned, `q + 16 n ≤ NEXT`). The two blocks' disjointness is not tracked: no value matters for safety, and both lie in fresh memory, which the frame allows writing.
- **Lemmas**: `call_ok`, `heap_ok`, `res_ok` (after `reserve`: room or `Grown`, both give `len + n ≤ cap'` and the buffer fresh), `len_ok`, `hdr_stores`, `shl4`.
- **Claims (call site)**: only caller `ring_switch` (61), template labels 35 to 40: slot `sp + 0x38` (frame), `f` = the buffer of `Transcript::samples`' vector at `sp + 8`, `g = f + 0x80`, `g.len = len - 8` after the code's `len > 7` check. `SamplesT.PostT`'s `VecT` gives `BufT` with `len ≤ cap`, which covers `f`'s 128 bytes and `g`'s in a window below `NEXT`. Argued from the template, not machine-checked; added to "Obligations".
- **Evidence**: `#print axioms` pinned in `RingCoefficientsT`; `WhirT6d.ringCoefficients` builds.

### D3. `ring_target` (134): returns, nothing more
- **Definition**: `PreT`: `s` (`a0`, `a1`) none or `InWin` and 8-aligned; `f` (`a2`) `InWin 128`, 8-aligned; `g` (`a3`, `a4`) `Live` and none or `InWin` and 8-aligned. `specT := HoldsT ... PreT (fun _ _ _ _ => True) (Stop := AbortStop)`, `Out` the default (writes nothing of the caller's).
- **Why**: the result is a value in registers, which the caller stores; nothing a caller does is unsafe for any value. `g`'s `Live` is what `ring_psi`'s partial `Pre` (kept by `RingPsiT.PreT`) asks at each call; `Live` only grows with `NEXT`, so the entry's suffices (`hglM`).
- **Cuts**: `total` (entry to pc 92 or 114), `psi` (92, label 46, `Total.loop`, images left), `fstart` (114, label 57, straight to 128), `fpass` (128, label 64, `Total.loop`, passes left `x18 + 1`, the return inside it). `images` is allocated with capacity `s.len` and `reserve(s.len)`'s room clause keeps its pointer (`res_ok`, using only `ReservePost`'s room implication with `n ≤ n - 0`); `x27` is not saved by this function, so `TInv`/`FInv` carry `R .x27 = regs .x27`.
- **Claims (call site)**: `ring_switch` (61) labels 41 to 47: `s` its own `(a2, a3)` (its own total `PreT` must ask it of `walk`), `f`, `g` as in D2. Argued; added to "Obligations".

### D4. `Frobenius8SafeT.frobSafe`, `ReadSliceT.ringPsiSafe`, `polyEvalSafe`: callees' functional contracts as register-only safety contracts
- **What**: from `∀ v, HoldsT (Pre v) (Post v)` (and `∀ v gs` / `∀ cs pt`), a `HoldsT` whose `Pre` speaks of the registers and the slice's bytes only (`Live`, window, alignment) and whose `Post` is `True`, by instantiating the ghosts with what the registers and memory hold: `Model.ofLimbsW (a0, a1)` for the value, `rdList m ptr len` (the elements memory holds, each `ofLimbsW` of its two words) for the slice; `sliceArgs_rdList` proves `SliceArgs EListAt` of it.
- **Why**: the executor needs the ghost value at the call; picking it per call site would have meant a `using [h (term)]` per call with the loaded words.
- **Rejected**: `Isa.TContract.mono` (the ghost depends on the registers, so it cannot be fixed before the contract is opened).
- **Claims**: no callee contract weakened in place; these are new theorems whose hypotheses are the existing total contracts. The callers lose the callees' postconditions (values), which only a functional proof needs.

### D5. Table instances in `Table/WhirT6d.lean`
- `ringCoefficients` (callees `AllocT.reserveE`, `RuntimeT.alloc`, `RuntimeT.handleError`, `FieldT.eMul`, `WhirT.frobenius8`, `CopyUseT.memcpy`), `ringTarget` (`RuntimeT.alloc`, `RuntimeT.handleError`, `AllocT.reserveE`, `MultilinearT.ringPsi`, `WhirT.frobenius8`, `MultilinearT.polyEval`, `FieldT.eMul`); stacks by `decide` over `Gen.Needs`. Hypotheses: `FieldT.ClmulTable` and the allocator's two facts, both already in the status legend (`clmul table`, `env`); no legend entry added.

## Invariants of the whole change
- No existing statement or module changed: `git diff 7b1d3faf0d --stat` lists six new `.lean` files, `notes/total-status.md` (rows 133, 134; two obligations; two owed entries) and `README.md` (layout mentions).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, raised `maxHeartbeats`, `skipKernel`: `git diff 7b1d3faf0d | grep -nE '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by|maxHeartbeats|skipKernel|axiom )' | grep -v "print axioms\|depends on axioms"` is empty.
- No em-dash or en-dash added: `git diff 7b1d3faf0d | grep -c '^+.*[—–]'` -> `0`.
- Files changed only under the allowed paths: `git diff 7b1d3faf0d --name-only | grep -v "^formal/rv64mc/Rv64mc/\(Proof\|Table\|Spec\)/\|^formal/rv64mc/notes/\|^formal/rv64mc/README.md"` is empty.
- Every loop is `Total.loop` with a measure: `outer` (passes), `prods`, `frobs`, `psi` (elements), `fpass` (passes).
- No `Tactic/` change; no executor bug found (the only executor behaviours worked around: `AbiRegs` after calls, D1; the closer could not read through `memcpy`'s `CopyOut` frame, so `RingCoefficientsT.total` reads the frame words back by `keep5_1` and a `simp (disch := ...) only [rd5]`).

## Obligations
- Discharged by these proofs at real call sites (machine-checked): `memcpy`'s `CopyPreT false` (wave 1a's argued precondition) at `ring_coefficients`' copy of `g`; `AllocPre` (all three allocations); `ReservePre ∧ VecT` at both functions' `reserve`; `RingPsiT.PreT`, `PolyEvalT.PreT` and `Frobenius8`'s `Pre` at `ring_target`'s calls (through D4), and `Frobenius8`'s at `ring_coefficients`'.
- New (argued, in "Obligations"): `ring_switch` (61) must discharge `RingCoefficientsT.PreT` and `RingTargetT.PreT`.
- New owed (in "Owed by contracts already total"): both functional contracts, and the partial spec's register mismatch (D2).

## Not done
- `instance_weights` (140): not attempted beyond reading the template. Obstacles seen: a 528-byte frame with a 4-byte `sw` into it (`storeMem .b4`, which `SavedT`'s and the existing frame lemmas take as `setMem`; `CopyT.storeMem_eq_setMem` is the bridge), a 4-byte signed load from a static table (`d_c64_a72ced70`, an environment fact `DataRef.InData` and `Windows.dataSub`, a new legend entry), and `E::sum`'s iterator built in the frame each pass (`ESumEmbedBitsT.SumPreT` reads two of its words through the stores). Its `reserve(16)` finds the room, like `ring_target`'s.
- `Scaled::new` (96), `K::inv` (127), `Subspace::new` (76), `novel_eval` (80), `ring_switch` (61), 86, the `E::sum` family (18, 24, 27, 29, 33), `Input::digest` (5), `is_valid_encoding` (216), the `GenericShunt` 171: not attempted (this pass's budget went to items 0 and the first two of item 1).
- No golf. Duplication left: `RingCoefficientsT` and `RingTargetT` each have their own `call_ok`/`heap_ok`/`res_ok`/`hdr`/`hdr_stores` (different offsets and invariants); `shl4` is imported by `RingTargetT` from `RingCoefficientsT`.

## Known risks
- **D1's executor claim** rests on two observed parts (`fin_ok`, `fpass`) and the scratch `MetaM` check, not on a test in `Tactic/SymTest.lean`.
- **`ring_coefficients`' `res_ok`**: the `Grown` branch's freshness (`next m ≤ ptr'`) comes from `Grown`'s `Fresh M m1` and `CV`'s `next m ≤ next M`; look at the `hgrow` case.
- **`ring_target`'s infeasible paths** are refuted by `absurd hc_1 hc` / `absurd hc hc_1` on the executor's branch names (`regs .x11 = 0#64` against its negation); a wrong name fails the build, it does not prove the wrong thing.
- **Call sites** (D2, D3) are read from the templates, not checked by a proof; in particular `ring_switch`'s `s` for `ring_target` comes from `walk`, whose contract does not exist yet.
- **`ReadSliceT`'s wrappers** drop the callees' postconditions; a later functional proof of `ring_target` must use `RingPsiT.specT`/`PolyEvalT.specT` directly at `rdList`.

## Pass 2: `instance_weights` (140) and `Scaled::new` (96) total with `Table` instances; `K::inv` and the rest not done

Head: 053a1f6c00 (2 commits on pass 1's 7d3ecef0a8: ec9b1ab886 `instance_weights`, 053a1f6c00 `Scaled::new`). Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Keccak.InstanceWeightsT Rv64mc.Table.KeccakT6d Rv64mc.Proof.Field.ScaledNewT Rv64mc.Table.FieldT6d` -> `Build completed successfully (5228 jobs).` (each module built fresh after its last change: `InstanceWeightsT` 47 s, `ScaledNewT` 136 s, peak about 8 GB under `lake env lean`; the two `Table` files under 5 s; only the existing `Proof/Field/Reverse.lean` module-system warning in the log). `awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `154 8764` (pass 1 `152 8410`).

### What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 140 | `verifier::keccak::instance_weights` | `InstanceWeightsT.specT` (safety: the slot `VecT` of 16-byte elements, `vecLen = 16`, `next m ≤ vecPtr`; `Out` the partial spec's `Spec.Keccak.InstanceWeights.Out`) | Proof/Keccak/InstanceWeightsT | KeccakT6d.instanceWeights | env; clmul table; RMFE_EMBED table (InData) |
| 96 | `<verifier::field::Scaled>::new` | `ScaledNewT.specT` (safety: the slot `VecT` of 16-byte elements, `vecLen = 1408`, `next m ≤ vecPtr`; `Out` the partial spec's `Spec.Field.Scaled.NewOut`) | Proof/Field/ScaledNewT | FieldT6d.scaledNew | env; Scaled::new divisor (InData) |

### Decisions

#### P2-D1. `instance_weights`: a safety contract over `SavedT`, the functional one owed
- **Definition**: `PreT`: the slot `InWin 24`, 8-aligned, `Owned` (the partial `Pre`'s `Owned`, plus the window and alignment; `s` needs nothing: its limbs only reach `E::mul`, whose `Pre` is `True`). `PostT`: `VecT env m' a0 16 ∧ vecLen = 16 ∧ next m ≤ vecPtr`. `Stop := AbortStop`.
- **Why**: class C; the caller `keccak::verify_layer` (138) reads the result's pointer and length (`sp + 0x48`, `sp + 0x50`) and sums `16 len` bytes (`E::sum` over `Copied`): the `VecT` with its length is what its safety needs. The partial `Post` (`Model.instanceWeightsRust`) needs the values of `E::mul` and of the bit-filtered sums, whose total contract `ESumEmbedBitsT.SumSafeT` does not state them: owed (in "Owed by contracts already total").
- **Cuts**: `loopA` (instruction 64, `Total.loop`, powers left `j`, `x19 + 16 j = top - 136`), `mid` (74 to 98: `alloc(256)`, the header `(16, ptr, 0)` at `top - 136`, `reserve(16)` with the room by `res_ok`), `loopB` (98, `Total.loop`, weights left), `fin_ok` (112), `total` (entry to 64: the prologue and the 48 stores of `powers`' initial values).
- **Invariants**: `Mem` (`SavedT.MemOk`, nine slots, `K = 72`), `Keep` (`s8` to `s11`, never saved, as at the entry: the closer needs them at the return), `Buf` (the block fresh, `q + 256 ≤ NEXT`, aligned), the header words `16` and `q`.
- **The `u32` store**: the executor leaves `M.setWord32 (top - 108) v`; `w32` rewrites it as the store of its doubleword `top - 112` (`alignToDword`), after which `iter_ok` carries `Mem` through the five frame stores (by `SavedT.MemOk.slot`) and reads the frame back.
- **The table**: `tbl_win` puts the `k`-th `u32` of `RMFE_EMBED` in a window and 4-aligned from `DataRef.InData` of its eight words (`Windows.data_ok`, `dataSub`): a new environment fact, `RMFE_EMBED table (InData)` in the legend.
- **Discharged at real call sites (machine-checked)**: `ESumEmbedBitsT.SumPreT` (wave 3c's contract, argued until now) at all sixteen sums (the iterator at `top - 104` in the frame, `e` at `top - 108`, `powers` a `TabW` of 24 at `top - 520`, closed by the executor's closer from the stores); `AllocPre`; `ReservePre ∧ VecT` at `reserve(16)`.
- **Call site (argued)**: `verify_layer` (138) passes `sp + 0x40` (its frame); recorded in "Obligations".

#### P2-D2. `Scaled::new`: a safety contract, four nested loops
- **Definition**: `PreT` as P2-D1's (the partial `NewPre` is `Owned`; `r`'s limbs need nothing). `PostT`: `VecT env m' a0 16 ∧ vecLen = 1408 ∧ next m ≤ vecPtr`.
- **Why**: class C; callers `Scaler::new` (93, a tail call passing its own slot) and `induced_weight` (97, `sp + 0x30`) then use the tables as a slice for `Scaled::mul`, whose partial `MulPre` asks `SliceArgs` (the values): owed with the functional contract (`Model.scaledNew`), recorded.
- **Structure**: `from_elem` makes `1408` zero entries; `chunks_exact_mut(704)` makes two chunks; the code divides the length by `704` with a `mulhu` by the static constant `d_c8_a4f5b9af` (`hend`: `mulhu(1408, c) >> 7 * 11264 = 22528`, by `decide`), so the constant's value bounds the chunks' loop and is an environment fact (`DataRef.InData`, legend entry `Scaled::new divisor (InData)`). Each chunk has eleven blocks of 64 entries: sixteen straight (`middle`, thirty stores), sixteen in `inner1` (offset `16 x6 ||| 256`, `or256` by `decide` over the 16 values), thirty-two in `inner2` (`or512`).
- **Cuts and measures**: `chunk` (instruction 39, chunks left), `middle` (44, blocks left), `inner1` (141, entries left), `inner2` (164, entries left; its exits go back to `middle` with one block fewer, to `chunk` with one chunk fewer, or to `fin_ok` (200)), `total` (entry to 39 or 200). Nesting as `RingCoefficientsT`: each outer loop's body passes its `ih` into the inner closures.
- **`Frm`**: `Hdr` (the slot's address at `top - 168`, the end `p + 22528` at `top - 160`, the header `(cp, p, 1408)` at `top - 128`, the buffer's bounds) with `Mem` (thirteen slots) and the chunk's second word at `top - 152`. `Frm.store` carries it through one store into the buffer; `frm_chain n` applies it `n` times (`iterate`, not `repeat`: `repeat` with `exact hF` as an alternative made the unifier unfold `Frm` against store chains and run out of recursion depth) and closes each address's bounds by `omega`.
- **Raised `maxHeartbeats`, each with a comment**: `inner1` 400000 (the executor's run over the block's xor values and two `Frm` chains), `inner2` 1000000 (four exits, each a `Frm` chain), `middle` 1000000 (a 30-store `Frm` chain). I did not measure the minimal values.
- **A kernel pitfall found**: `simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega` on `top + c` offsets (a first `slot_off`) passed the elaborator but hit `(kernel) deep recursion` under `lake build` and, inside `total`, ran the 16 GB scope out of memory (three OOM kills, `journalctl --user`); the `rw`-based `tn` macro (the one every module of this wave uses) does not. Every such step in `ScaledNewT` uses `tn` or the closer.
- **Discharged (machine-checked)**: `FromElemT.FromElemPreT` at the call (`SretPre` and the window from the frame at `sp + 0x30`).

#### P2-D3. `K::inv` (127): not done, the route chosen
- A safety-only `HoldsT` (`Post := True`) over the callees' total contracts with their postconditions dropped (`dropPost`, a three-line generic lemma), so the executor carries no value of the chain, then `HoldsT.of_holds_post` with the partial `Proof.Field.KInv.ok` (taken as a hypothesis, supplied in the `Table` instance by `Table.Field.kInv`). The body is 133 calls (the last a tail call) with four saved slots; the plan cuts after every 27 calls (instructions 134, 246, 354, 464) with `Inv` = stack pointer, `Keep` (`s3` to `s11`) and `SavedT.MemOk` of four slots. A draft with that skeleton and one probed part is at formal/rv64mc/campaign/runW6d/p2/KInvT.draft.lean (not committed: it ends in `sorry`; not compiled).

### Claims
- No existing statement or module changed: `git diff 7d3ecef0a8 --stat` lists four new `.lean` files (`Proof/Keccak/InstanceWeightsT`, `Table/KeccakT6d`, `Proof/Field/ScaledNewT`, `Table/FieldT6d`), `notes/total-status.md` (rows 140 and 96, two legend entries, two obligations, two owed entries) and `README.md` (the two `Table` files in the layout).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `skipKernel`: each commit's diff was grepped before committing (empty). Raised `maxHeartbeats`: exactly the three above. No em-dash or en-dash added (`grep -c` 0 on each commit's diff). Lines at most 120 columns.
- Each `total` and each `Table` theorem has a `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]`.
- Every loop is `Total.loop` with a `Nat` measure: `loopA` (powers), `loopB` (weights), `chunk`, `middle`, `inner1`, `inner2`.
- Every `Pre` holds at its image call sites, argued from the templates (machine-checked only where a caller is total): `instance_weights` at `verify_layer` (138, `sp + 0x40`); `Scaled::new` at `induced_weight` (97, `sp + 0x30`) and `Scaler::new` (93, its own slot, so 93's total `Pre` must ask the slot's facts).
- Post against callers' needs: 138 needs the result's `VecT` and length `16` for its sum (given); 93 and 97 need, for `Scaled::mul`'s partial `MulPre`, the values (`SliceArgs`), which neither total contract gives: recorded as owed, and a safety-only `Scaled::mul` contract would need only windows and a length, which `PostT` gives.

### Not done (supersedes the header's list)
- `K::inv` (127): not started beyond the route and the draft (P2-D3); this pass's budget went to 140 and 96. No obstacle seen yet.
- `Subspace::new` (76, needs 127), `novel_eval` (80), `ring_switch` (61), `verify_whir`'s closure 86, the `E::sum` family (18, 24, 27, 29, 33), `Input::digest` (5), `is_valid_encoding` (216), the `GenericShunt` 171: not attempted.
- No golf. Duplication: `InstanceWeightsT` and `ScaledNewT` each have their own `hdr`, `call_ok`/`call_mem`, `heap_ok` for their offsets (the same shapes as pass 1's modules).

### Where to look hardest
- **`ScaledNewT.Hdr`'s end word**: `(M.getMem (top - 160)).toNat = p + 22528` is set from `hend` (the static constant's value, `hDv` from `DataRef.Words.get0`); the chunks' exit compares `x11 + 11264` against it (`inner2`'s third and fourth exits); a wrong value would make the chunk count wrong, and `inner2` would fail, not prove the wrong thing.
- **`ScaledNewT.Base`'s bounds**: every store of a block must stay below `p + 16 cp` with `cp ≥ 1408` (`Frm.store`'s `hhi`, by `omega` from `x11 = p + 11264 (2 - c)`, `x16 = 1024 (11 - k)` and the offsets); look at `or256`/`or512`'s use (`hx8`, `hx8'`).
- **`InstanceWeightsT.res_ok`**: uses only `ReservePost`'s room clause (`16 ≤ 16 - 0`); the `Grown` branch is never needed.
- **`total`s' `Mem` after the prologue**: built by `refine ⟨?_, ..., trivial⟩ <;> rv_closeT` (`InstanceWeightsT.total` through 57 stores, `ScaledNewT.total` through `call_mem`'s argument).

## Pass 3: `K::inv` (127) and `Subspace::new` (76) total with `Table` instances; the rest not done

Head: 93f6642468 (2 commits on pass 2's 053a1f6c00: 11c907ee19 `K::inv`, 93f6642468 `Subspace::new`). Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded. Earlier passes' commits not touched.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.SubspaceNewT Rv64mc.Table.WhirT6d Rv64mc.Proof.Field.KInvT Rv64mc.Table.FieldT6d` -> `Build completed successfully (5598 jobs).` (each module built fresh after its last change: `KInvT` 49 s, `SubspaceNewT` 102 s, the two `Table` files under 10 s; only the existing `Proof/Field/Reverse.lean` module-system warning in the log). `awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `156 9135` (pass 2 `154 8764`).

### What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 127 | `<verifier::field::K>::inv` | `KInvT.specT` (class A: the partial `KInv.Post`, `a0 = Model.kInv a`, `Out` the default (writes nothing of the caller's), `Stop` the default `False`) | Proof/Field/KInvT | FieldT6d.kInv | clmul table |
| 76 | `<verifier::whir::Subspace>::new` | `SubspaceNewT.specT` (safety: both vectors at the slot `VecT` of `log_n + 1` elements, buffers fresh; `Out` the partial spec's `SretOut Layouts.Subspace.byteSize`; `Stop := AbortStop`) | Proof/Whir/SubspaceNewT | WhirT6d.subspaceNew | env; clmul table |

### Decisions

#### P3-D1. `K::inv`: safety in twelve parts, then `of_holds_post` with the partial proof
- **What**: `safe : HoldsT env p i need (fun _ _ => True) (fun _ _ _ _ => True)` over the callees' total contracts with their postconditions dropped (`dropPost`, proved once generically), then `total := (safe ...).of_holds_post hpart fun _ _ h => h`, `hpart : KInv.spec env p i need` (the partial contract; the `Table` instance supplies `Table.Field.kInv` at `ClmulTable.words`). So `specT`'s postcondition is exactly the partial `KInv.Post` and its frame the partial one's (default `Out`), as the brief asks of a class-A port.
- **Cuts**: after the prologue (instruction 10) and before every twelfth call: `part1` (10 to 68) ... `part11` (512 to 564), `part12` (564: call `s132`, the epilogue, the tail call `s133`). 134 call sites in all (pass 2 counted 133). Each part keeps only `Inv`: `x2 = top - 32`, `Keep` (`s3` to `s11` as at the entry) and `Mem` (`SavedT.MemOk` with the four slots `ret, s0, s1, s2`). Chained in `safe` by a `chain` macro (`have hN := partN ... hN+1`).
- **Why twelve**: one `rv_symT` run costs more than linearly in its calls (measured: 12 calls about 96k heartbeats, 18 calls and 27 calls over the default 200k; pass 2's plan of 27 per part timed out). Twelve leave about half the default budget; no `maxHeartbeats` raised in `KInvT`.
- **`call_back`**: `Mem` across one callee (`SavedT.MemOk.call`); each part applies it `n` times backwards (`iterate n (refine call_back (by assumption) ... hlim ?_)`), the callee's frame, keep, code and static facts found by `assumption` from the executor's `hretK_*`/`keepK_1` (unique by their two memories). Then `exact hM` closes at the part's entry memory.
- **`part12`**: the tail call's frame from `top` (`Tactic.frame_trans` of `call_back`'s `Mem` after `s132` with the tail callee's `Frame top`); `AbiRegs` by `simp only [AbiRegs, Tactic.rf, hI_15, hI_16, hI_17, and_self]` (the three slots read by the epilogue).
- **`set_option linter.unusedSectionVars false`** (in the parts' section only, with a comment): every part takes all three callee contracts so `safe` chains them uniformly; a part without a `base_mul` call does not use `hbm`.
- **Rejected**: wave 2b's port (`rv_symT` carrying the chain's values: timed out at 1M heartbeats); pass 2's 27-call parts (timed out at 200k, reproduced).

#### P3-D2. `Subspace::new`: a safety contract over `SavedT`, the functional one owed
- **Definition**: `PreT`: the slot `InWin 48`, 8-aligned, `Owned` (the partial `NewPre`'s `Owned`, plus window and alignment; its `log_n < 64` dropped: safety does not need it, so `PreT` is weaker there). `PostT`: `VecT env m' sret 8 ∧ vecLen = log_n + 1 ∧ next m ≤ vecPtr` and the same at `sret + 24`. `Out := SretOut Layouts.Subspace.byteSize` (the partial spec's), `Stop := AbortStop`.
- **Why**: class C; the callers (`induced_weight` 97, `verify_whir`'s closure 74) pass the subspace to `Subspace::at`, whose total `PreT` asks `VecT` at `+0` and `+24` (given). The functional `NewPost` (`Model.SubspaceRust.new`) needs `subspace_roots`'s values (owed) and `K::inv`'s (kept): recorded in "Owed by contracts already total".
- **Cuts**: `total` (entry to 24: prologue, `subspace_roots` into the frame slot `top - 104`), `mid` (24 to 104/118: the size check, `alloc`, the inverses' header `(n, q, 0)` at `top - 80`, `reserve(n)` with the room), `loop` (104, `Total.loop`, measure `j` roots left; back edge at `j - 1` with `2 ≤ j` from the exit test), `fin_ok` (118: both headers into the slot, the epilogue, the return).
- **Invariants**: `Mem` (`SavedT.MemOk`, seven slots, `K = 56`), `Keep` (`s6` to `s11`), `RT` (the roots' header in the frame: length `n`, `n ≤ cap`, `cap * 8 < 2^63`, buffer fresh, aligned, below `NEXT`), `IB` (the inverses' block: fresh, `q + 8n ≤ NEXT`, aligned). Lemmas: `RT.keep`, `IB.mono`, `call_ok`, `roots_ok` (`subspace_roots`' `SretOut 24` frame), `hdrR`/`hdrI`, `hdr_stores`, `res_ok`, `heap_ok`, `finMem`/`fin_mem` (the six slot stores and the frame store at the exit: reads, `NEXT`, `Frame`).
- **Infeasible paths refuted** in `mid`: `n = log_n + 1 ≥ 1` (from `SubspaceRootsT.PostT`) and `n ≤ cap`, `cap * 8 < 2^63` make the paths `n * 8 = 0` (dangling block) and `n = 0` (straight to the exit) contradictory, by `congrArg BitVec.toNat` of the branch equation (named `hc`, `hc_1` or `hc_2` by the executor; a `try first` over the three) and `omega`; the size check's failure path (`handle_error`) is stepped by `Aborts`.
- **Raised `maxHeartbeats`**: `fin_ok` 1000000, with a comment (the epilogue's seven loads read through the six slot stores and the frame store, each disequality proved by the closer from `Owned`). Measured 773302 by `#count_heartbeats` (removed). I did not split it: the alternative, a cut between the stores and the epilogue, needs `Mem` and `PostT` proved through the seven stores by hand. A reviewer may prefer the split.
- **A bug found and fixed while proving** (not committed in its bad form): a local `have hhe := hW.heapEnd_le` shadowed the `Aborts` hypothesis `hhe` passed to `rv_symT ... using [hac, hhe, hres]`, so the executor could not step the size check's `handle_error` call (a goal left at instruction 49). Renamed `hHE`. Worth a lint or a habit: never shadow a name passed to `using`.

### Claims
- No existing statement or module changed: `git diff 053a1f6c00 --stat` lists two new `.lean` files (`Proof/Field/KInvT`, `Proof/Whir/SubspaceNewT`), additions to pass 1's and 2's `Table/WhirT6d.lean` and `Table/FieldT6d.lean` (new theorems, header docstrings), `notes/total-status.md` (rows 127 and 76; one obligation struck, one added; one owed entry) and `README.md` (the two modules in the layout's list).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `skipKernel`: `git diff 053a1f6c00 | grep -nE '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by|skipKernel|axiom )' | grep -v "print axioms\|depends on axioms"` is empty. Raised `maxHeartbeats`: exactly one (`SubspaceNewT.fin_ok`, above). No em-dash or en-dash added (`grep -c` 0). Lines at most 120 columns.
- `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]` for `KInvT.total`, `SubspaceNewT.total`, `FieldT6d.kInv`, `WhirT6d.subspaceNew`.
- Every loop is `Total.loop` with a `Nat` measure: `SubspaceNewT.loop` (roots left). `KInvT` has none.
- Pre at the call sites: `KInvT`'s `Pre` is `True` (holds everywhere; its callers 76 and others need nothing). `SubspaceNewT.PreT` at 97 (`sp + 0x30`, template step 25) and 74 (`sp + 0x140`, step 247), both frame slots: argued from the templates, added to "Obligations".
- Post against the callers' use: 97 and 74 call `Subspace::at` on the subspace (its `PreT`: `VecT` at `+0` and `+24`, given); `K::inv`'s callers get the partial postcondition (value), as before.
- **Discharged at real call sites (machine-checked)**: `SubspaceRootsT.PreT` at 76's call (wave 6b's argued obligation, struck in "Obligations": the executor closes it at the frame slot); `AllocPre`, `ReservePre ∧ VecT` at 76's `reserve(n)`; `KInvT.specT`'s `True` at 76's loop.

### Not done (supersedes pass 2's list)
- `novel_eval` (80): its callee `E::sum` over `Zip<..., novel_eval::{closure#0}>` is not total (not in the frontier); comes after the `E::sum` family.
- `ring_switch` (61), `verify_whir`'s closure 86, `induced_weight` (97, now in the frontier: its callees `Subspace::new`, `Subspace::at`, `base_mul`, `E::mul` are total), the `E::sum` family (18, 24, 27, 29, 33), `Input::digest` (5), `is_valid_encoding` (216), the `GenericShunt` 171: not attempted (this pass's budget went to 127 and 76).
- No golf. Duplication: `SubspaceNewT` has its own `call_ok`/`res_ok`/`heap_ok`/`hdr_stores` (the shapes of passes 1 and 2's modules, different offsets); `KInvT.call_back` is `SubspaceNewT.call_ok`'s shape without `RT`. A generic "frame below `K` slots, callee at `top - F`" version of `call_ok` over `SavedT` would serve all of them.

### Where to look hardest
- **`KInvT`'s cut points** (68, 118, 170, 218, 270, 318, 366, 414, 464, 512, 564): each is the label before `set x1 <s_k.hi>` for `k = 12 j` (computed by script from the template: `pc = 2 * label`). A wrong cut makes a part fail, not prove the wrong thing; `safe` chains them in order.
- **`KInvT.total`'s use of `hpart`**: the total contract's postcondition comes wholly from the partial proof via `of_holds_post`; `safe` proves only safety, termination and the frame/`AbiRegs`/`Static` that `HoldsT.post` asks with `Post := True`.
- **`SubspaceNewT.PreT` drops `log_n < 64`** (the partial `NewPre` has it): the total contract is stronger there. Check that no part used it (none could: it is not in `PreT`).
- **`SubspaceNewT.fin_ok`'s heartbeats**: 1000000 against 773302 measured.
- **`mid`'s refutations**: the `try first` chain closes the six goals of the paths `n * 8 = 0` and `n = 0`; if the executor named the branch equation otherwise the build would fail with a leftover goal, so a silent wrong closure is not possible (each closure is a kernel-checked `omega`).

## Golf

Head: 8f39c8dfbc (one commit on 93f6642468). Skills: lean4:golf and lean4:refactor loaded. Diff: 8 files, 86 insertions, 114 deletions. No statement of a theorem the wave exports changed. The only statements that changed are those of `KInvT`'s parts (G3), and only by naming their shape. No new `sorry`, `axiom`, `native_decide`, raised `maxHeartbeats` or dash: `git diff 93f6642468 8f39c8dfbc | grep -nE '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by|maxHeartbeats|skipKernel|axiom )'` is empty, and `grep -c '^+.*[—–]'` gives 0.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Runtime.SavedT Rv64mc.Proof.Whir.Frobenius8SafeT Rv64mc.Proof.Multilinear.ReadSliceT Rv64mc.Proof.Whir.RingCoefficientsT Rv64mc.Proof.Whir.RingTargetT Rv64mc.Proof.Keccak.InstanceWeightsT Rv64mc.Proof.Field.ScaledNewT Rv64mc.Proof.Field.KInvT Rv64mc.Proof.Whir.SubspaceNewT Rv64mc.Table.WhirT6d Rv64mc.Table.KeccakT6d Rv64mc.Table.FieldT6d` -> `Build completed successfully (5624 jobs).` Every changed module was rebuilt fresh before that run: `KInvT` and `RingCoefficientsT` together, `RingTargetT` and `InstanceWeightsT` together, then `ScaledNewT` and `SubspaceNewT` one at a time, all `Build completed successfully`. The only warning in the log is the existing `Proof/Field/Reverse.lean` module-system note. Every module's `#guard_msgs in #print axioms` (`[propext, Classical.choice, Quot.sound]`) still passes, because the build checks it.

### G1. `SavedT.MemOk.call_at` / `MemOk.call_below`: one generic "callee from `top - F`" lemma, used by seven call lemmas
- **What**: `call_at` takes `MemOk` across a callee whose stack pointer `sp` has `sp.toNat = top.toNat - F`, writing at most `out'`, where each word of `out'` lies in `[top - F, top - K)`. It gives `MemOk` for the callee's memory, and every word of the frame outside `out'` reads as before. `call_below` is the case `out' = fun _ => False`. Each is proved once, from `MemOk.call`, `Tactic.mw_stack` and `Tactic.le_of_toNat`, by the same steps the local lemmas repeated.
- **Users**: `KInvT.call_back`, the `call_ok`s of `RingCoefficientsT`, `InstanceWeightsT`, `RingTargetT` and `SubspaceNewT`, `SubspaceNewT.roots_ok`, the `res_ok`s of `RingCoefficientsT` and `InstanceWeightsT` (their `Mem` conjunct), and `ScaledNewT.call_mem`.
- **Why the meaning is the same**: each local lemma's statement is unchanged. Only its proof changed, and that proof now goes through the generic lemma. The generic lemma's hypotheses are the ones the local proofs used to discharge inline: `K ≤ F` and the window bound (`by omega` from `hlim`), `sp`'s address (`by tn`, or the `e472`/`e528` already present), and the `out'` bounds (from each lemma's `hout`/`ho`, as before). In `ScaledNewT.call_mem`, `call_at` is instantiated at the frame's own `out`. The stated `¬ InRange` reading follows by `hout`, which is the step the old `rd` took.
- **Added**: `SavedT` now imports `Rv64mc.Spec.Runtime.RawVec` (for `hdr_at`, G2) and opens `Rv64mc.Spec.Runtime`. Its header docstring lists the new lemmas.

### G2. `SavedT.hdr_at`: the six identical vector-header lemmas
- **What**: `hdr_at top c M` says that the header at `top + c` reads as `rvCapAt`, `rvPtrAt`, `vecCap`, `vecPtr` and `vecLen` name it, with offsets `c + 8#64` and `c + 16#64`. Its proof is one term: `BitVec.add_zero` and `BitVec.add_assoc`, with `congrArg M.getMem`. The local `hdr` of `RingCoefficientsT`, `RingTargetT`, `InstanceWeightsT` and `ScaledNewT`, and `SubspaceNewT.hdrR`/`hdrI`, keep their statements (literal offsets). Each proof is now `Runtime.SavedT.hdr_at top _ M`.
- **Why the meaning is the same**: the statements did not change. The literal offset sum `c + 8#64` equals the literal the statement names by definitional unfolding. That is the same `rfl` the old `rw [BitVec.add_assoc]; rfl` closed with, and the build checks it.

### G3. `KInvT.Cut`: the parts' statements
- **What**: `abbrev Cut env p i Q ret top rest regs m pc := ∀ R M, Inv env ret top regs m R M → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, pc, ret, top⟩ :: rest, R, M⟩`. `part1` to `part11` now state `(hb : Cut ... b) : Cut ... a`, and `part12`'s conclusion is `Cut ... 564`. The proofs (`part_tac`, `part12`'s script), `safe` and `total` are unchanged.
- **Why the meaning is the same**: `Cut` is a reducible abbreviation whose body is the text it replaced, character for character, so each part's type is definitionally the old one. `safe` chains them as before. `total`'s statement (`specT`) and the `Table` theorem `FieldT6d.kInv` did not change.
- **`call_back`** goes through `call_below` (G1) and no longer has its local `e`.

### Docs
- README: the `SavedT` entry names `hdr_at`. No change to `notes/total-status.md` (no row, obligation or legend entry is affected).

### Not changed (considered)
- `dropPost` (`KInvT`) and the same continuation in `Frobenius8SafeT.frobSafe` and `ReadSliceT.ringPsiSafe`/`polyEvalSafe` (a one-line `fun r' m' ⟨⟨h1, h2, h3, _⟩, h5⟩ => ...`): sharing it would mean a new module or an import that does not fit, to save one line per site.
- The `local macro "tn"` in each module: twenty existing modules define the same local macro, and a shared non-local `tn` could clash with them as a second parser for the same token.
- `hdr_stores`, `heap_ok` and `res_ok`: their offsets and their per-module invariants (`CV`, `PW`, `RT`, `Img`) differ. A generic version would need the invariants as parameters and would not be shorter at the call sites.

## Amendments, round 1

Head: dc5277f832 (one commit on 8f39c8dfbc). Skill lean4:prove loaded.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Field.KInvT Rv64mc.Proof.Field.ScaledNewT Rv64mc.Proof.Whir.RingCoefficientsT Rv64mc.Proof.Whir.RingTargetT Rv64mc.Table.FieldT6d Rv64mc.Table.WhirT6d Rv64mc.Table.KeccakT6d` -> `Build completed successfully (5624 jobs).` It rebuilt `KInvT` (60 s), `RingCoefficientsT` (77 s), `RingTargetT` (43 s), `ScaledNewT` (159 s), `SubspaceNewT` (124 s, through `SavedT`'s dependents) and the `Table` files. The lakefile has `warningAsError = true`, and every module's `#guard_msgs in #print axioms` still passes. No statement changed. The commit diff adds no dash (`grep -c '^+.*[—–]'` gives 0) and no `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide`/`implemented_by`/`skipKernel` (grep empty). No changed `.lean` file has a line over 120 characters (counted in characters by a Python check over `git diff --name-only`).

### R1-1 (important): fixed. This contradicts P2-D2's "Why", pass 2's Claims, and the obligation as first written.
- `Scaled::new` (96) has exactly one caller, `Scaler::new` (93), which tail-calls it. `induced_weight` (97) calls `Subspace::new` (76) at `sp + 0x30` (`Gen/Link/Verifier/Whir.lean`, `InducedWeight`'s link: `«new» := ⟨Idx.Verifier.Whir.Subspace.New, ...⟩`). The only link naming `Idx.Verifier.Field.Scaled.New` as a callee is `Gen/Link/Verifier/Multilinear.lean:192`, inside `namespace Rv64mc.Gen.Verifier.Multilinear.Scaler.New`.
- So P2-D2's "callers `Scaler::new` (93 ...) and `induced_weight` (97, `sp + 0x30`)" and pass 2's Claims line "`Scaled::new` at `induced_weight` (97, `sp + 0x30`) and `Scaler::new` (93 ...)" were wrong. So were the "97's proof discharges it" clause and "93 and 97 need" in the Post-against-callers line. The obligation's only discharger is 93's total `Pre`, which must ask the slot's facts of its own slot. P3's 97 at `sp + 0x30` (for `Subspace::new`) was right.
- `notes/total-status.md` line 70 is rewritten: 93 is the only caller (with the note that 97 calls 76, not 96), and the 97 clause is gone.

### R1-2 (nit): fixed
- Wrapped `ScaledNewT.lean` (the `call_mem` application in `total`, now three lines), `RingCoefficientsT.lean` (the two `refine hout ...` anonymous constructors, split before the inner `Mem` tuple) and `RingTargetT.lean` (`fpass`'s `hfr`/`hpe` binders on two lines). The claim "lines at most 120 columns" now holds in characters, which is how the Lean linter counts them. Note that `LC_ALL=C awk 'length > 120'` counts bytes and still flags lines that hold `⟨`/`⟩`.

### R1-3 (nit): fixed
- The README layout now lists `Proof/Keccak/InstanceWeightsT` (a safety contract over `SavedT`, the `RMFE_EMBED` table a static-data fact, its sums through `ESumEmbedBitsT`) and `Proof/Field/ScaledNewT` (a safety contract over `SavedT`, four nested loops, stores by `Frm.store`, the divisor a static-data fact). Both come after `SubspaceNewT`'s entry.

### R1-4 (nit): fixed here, in an amendment. The earlier entries are not edited, as the lifecycle requires.
- **The title** ("pass 1 ... the rest of the list not done") is pass 1's. It is superseded by the pass headings: pass 2 (140, 96), pass 3 (127, 76), Golf, and this round. The wave's done list is 133, 134, 140, 96, 127 and 76. Pass 3's "Not done" is the current one.
- **D1's Claims and Evidence are superseded.** "SavedT imports only `Tactic.Heap`" stopped holding at G1, when it also began to import `Rv64mc.Spec.Runtime.RawVec` (for `hdr_at`). "Its users are `RingCoefficientsT` and `RingTargetT`" is now six users: `grep -rln SavedT formal/rv64mc/Rv64mc` lists `SavedT` itself plus `KInvT`, `ScaledNewT`, `InstanceWeightsT`, `RingCoefficientsT`, `RingTargetT` and `SubspaceNewT`. "No existing module uses it" still holds: every user is new in this wave.
- **P3's Claims line** "its callers 76 and others" is wrong. `K::inv`'s only caller is `Subspace::new` (76), which is reviewer 1's `cg.json` reading. Its `Pre` is `True`, so the conclusion stands: it holds at that call site, and `SubspaceNewT`'s loop discharges it by the machine-checked proof.

### R1-5 (nit): fixed
- I measured with `#count_heartbeats in` (Mathlib's `Mathlib.Util.CountHeartbeats`) in a scratch copy, `runW6d/scratch/ScaledNewHB.lean`. That copy is the module with each `set_option maxHeartbeats N in` replaced by `#count_heartbeats in`, run by `lake env lean` under the 16 GB scope, exit 0. Results: `inner1` 245628, `inner2` 646617, `middle` 626044.
- The budgets are now `inner1` 300000 (was 400000), `inner2` 800000 (was 1000000) and `middle` 800000 (was 1000000). That is about 22% to 28% headroom over the measured values. Each budget keeps its stated reason in the comment above it, with no number in the comment, per the repo's writing rule. `ScaledNewT` rebuilt at these budgets in the check above.
- This contradicts pass 2's "I did not measure the minimal values", which no longer holds.
- `SubspaceNewT.fin_ok` (1000000 against 773302 measured in pass 3) is unchanged. It was not in the finding, and 800000 would leave 3% headroom.

### R1-6 (nit): fixed
- The section-wide `set_option linter.unusedSectionVars false` in `KInvT` is removed. Compiling a copy without it (`runW6d/scratch/KInvLint.lean`) flagged exactly `part4`, `part6`, `part7`, `part8`, `part10` and `part12`, each for `hnM` and `hbm` (those parts make no `base_mul` call). Each of these six parts now has `omit hnM hbm in`.
- Their proofs no longer name `hbm`. `part_tac'` passes only `dropPost hsp, dropPost hrd` to the executor, and `part12`'s `rv_symT` `using` list drops `dropPost hbm`. One core macro, `part_core b n [cs]`, takes the callee list. `part_tac` and `part_tac'` are one-line instances of it.
- `safe` chains the six parts with `chain'`, which is `chain` without `hnM hbm`.
- The parts' statements lose two unused hypotheses. Nothing outside `KInvT` uses them, and `safe`, `total` and `FieldT6d.kInv` are unchanged. `grep -rn "set_option linter" formal/rv64mc/Rv64mc` is now empty.
- This contradicts P3-D1's last bullet, which is superseded.

### R1-7 (nit): deferred, with the reason (the brief's "its restore at the epilogue" was not built as a lemma)
- **Why there is no lemma**: no epilogue in this wave needs one. With `Saved` over literal lists, `rv_introT` splits `Mem` into one equation `M.getMem (top + c) = v` per slot (D1). At the epilogue, the executor's closer reads each restored register `r' .xN` as the load `M.getMem (top + c)` and closes `AbiRegs` from those equations unaided in `RingCoefficientsT.fin_ok`, `InstanceWeightsT`'s and `ScaledNewT`'s `fin_ok`, and `SubspaceNewT.fin_ok`.
- **The two manual sites** are `KInvT.part12` (`simp only [AbiRegs, Tactic.rf, hI_15, hI_16, hI_17, and_self]`, one line) and `RingTargetT.fpass` (destructure `Mem`, then `simp only [AbiRegs, Tactic.rf]; exact ⟨trivial, s2, ..., s12, trivial⟩`, three lines). In both, the goal after `simp only [AbiRegs, Tactic.rf]` is already one slot equation per conjunct.
- **Why a lemma would not help**: a generic `Saved.restore` would need a third list (registers to offsets) and a hypothesis that each register holds its slot's load, stated the way the executor never states it. It would not shorten either site.
- **What it would take**: if a later wave's epilogue does not close, either (a) a `SymTest` case plus a closer extension that rewrites `AbiRegs` conjuncts by `Saved`'s equations after calls, or (b) `Saved.get : Saved top cs vs M → ∀ k < cs.length, M.getMem (top + cs[k]) = vs[k]`.

### R1-8 (nit): fixed
- `notes/total-status.md` line 70 now says that `ScaledMulT.mulSpecT` holds for every `tabs`. A safety-only caller therefore takes `tabs` to be the memory's contents, as `ReadSliceT.rdList` does for `ring_psi`. `ScaledNewT.PostT`'s `VecT` gives `MulPre` of them: the window and alignment, length `1408`, and `Live` from `BufT`'s `ptr + 16 cap ≤ NEXT` with `cap ≥ len`. Only a functional caller needs `Model.scaledNew`'s values, which are owed (the "Owed" entry for 96, unchanged).
- This supersedes pass 2's Claims phrase "which neither total contract gives", which was right only for a functional caller.

### Also changed (not a finding)
- `ScaledNewT`'s header docstring said "`specT`, not yet proved: the entry part `total` is missing". That was stale, because `total` is proved (line 458). It now says "A total proof ... (`total`, of `specT`)", and `total` is added to its Main results.
