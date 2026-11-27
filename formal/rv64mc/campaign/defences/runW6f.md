# Defence: wave 6f, pass 1: the five `E::sum` closures (18, 29, 33, 24, 27), `Input::digest` (5), `Scaler::new` (93) and `novel_eval` (80) total with `Table` instances; `ring_switch` (61) and the rest of the list not done

Base: e0b25661c3. Head: dda69ebd22 after pass 2 (see "## Pass 2"; pass 1's head was aca10074f6) (branch formal/rv64mc-total-w6f, worktree /home/devops/leanEthereum/leanVM-t-symt, pass 1's 11 commits, not pushed: 97e9d48e53 (18), 1b59d23eb8 (29), c65fdd8cbf (33), 0f51bb38f6 (24), a9dfcf15bb (27), f5cf0dcdc9 (header width), 0b76d8fa08 (5), da8d428d46 (93), 30326ae345 (80), d9b2ec57a9 (README), aca10074f6 (obligations)).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Field.ESumNovelT Rv64mc.Proof.Field.ESumProjectT Rv64mc.Proof.Field.ESumFormT Rv64mc.Proof.Field.ESumBlockT Rv64mc.Proof.Field.ESumLaneT Rv64mc.Proof.Runtime.InputDigestT Rv64mc.Proof.Multilinear.ScalerNewT Rv64mc.Proof.Whir.NovelEvalT Rv64mc.Table.SumT6f Rv64mc.Table.RuntimeT6f Rv64mc.Table.MultilinearT6f Rv64mc.Table.WhirT6f` -> `Build completed successfully (5546 jobs).` (the final run cached; each module was rebuilt by `lake build` after its last source change, with `warningAsError`: two linter failures, an unused hypothesis in `ESumFormT.off_eq` and a dead `all_goals rv_closeT` in `InputDigestT.total`, were fixed that way). Build times from those runs (`lake build`'s own report): `ESumNovelT` 17 s, `ESumProjectT` 15 s, `ESumFormT` 16 s, `ESumBlockT` about 34 s (`lake env lean`), `ESumLaneT` 77 s, `InputDigestT` 24 s, `ScalerNewT` 9 s, `NovelEvalT` 9 s, the `Table` modules under 8 s each.

Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

## What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 18 | `E::sum` over `novel_eval`'s zip | `ESumNovelT.SumSafeT` (safety, `Post := True`, `Out` default, no `Stop`) | Proof/Field/ESumNovelT | SumT6f.eSumNovel | clmul table |
| 29 | `E::sum` over `RMFE_PROJECT`'s filter (`verify_layer`) | `ESumProjectT.SumSafeT` (safety, `Stop := AbortStop`) | Proof/Field/ESumProjectT | SumT6f.eSumProject | RMFE_PROJECT table (InData), new legend entry |
| 33 | `E::sum` in `Form::evaluate` | `ESumFormT.SumSafeT` (safety, `AbortStop`) | Proof/Field/ESumFormT | SumT6f.eSumForm | clmul table |
| 24 | `E::sum` in `Bytecode::evaluate`'s block value | `ESumBlockT.SumSafeT` (safety, `AbortStop`) | Proof/Field/ESumBlockT | SumT6f.eSumBlock | clmul table |
| 27 | `E::sum` over `verify_layer`'s chunks zip | `ESumLaneT.SumSafeT` (safety, `AbortStop`) | Proof/Field/ESumLaneT | SumT6f.eSumLane | clmul table |
| 5 | `Input::digest` | `InputDigestT.InputDigestSpecT` (safety, `Out := DigestOut`, post `ReaderT`) | Proof/Runtime/InputDigestT | RuntimeT6f.inputDigest | none |
| 93 | `Scaler::new` | `ScalerNewT.safeT` (safety) and `ScalerNewT.specT` (with the partial `NewPost`) | Proof/Multilinear/ScalerNewT | MultilinearT6f.scalerNewSafe; MultilinearT6f.scalerNew | env; Scaled::new divisor (InData); `scalerNew` also `Spec.Field.Scaled.newSpec` (not an environment fact, D7) |
| 80 | `novel_eval` | `NovelEvalT.specT` (safety, `AbortStop`) | Proof/Whir/NovelEvalT | WhirT6f.novelEval | env; clmul table |

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `172 10252` (base `164 9792`; the summary table left to the merge). Each proof module's main theorem and each `Table` theorem has a `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]`.

## Decisions

### D1. The `E::sum` closures are safety contracts over the iterator the caller builds (all five)
- **What**: each `SumPreT` takes the iterator by reference (`x10`), with: its words 8-byte aligned and `InWin`; `env.Owned m (regs .x2) (regs .x10) n` where the function has a frame (18, 33, 24, 27: the prologue's stores precede the loads, and the executor must read the iterator through them); the slices it walks; `Post := True`. 29 has no frame and no `Owned`. `Stop := AbortStop` wherever a callee may abort (`panic_bounds_check`, `dot`, `ESumU16T`); 18 calls only `base_mul` and has no `Stop`.
- **Why**: class D, no partial spec; no caller's safety reads a sum's value (each is multiplied or summed into a value that is only compared). The iterator shapes are the templates' (dumped with a script reading `c0`, label `k` at program counter `2k`).
- **Rejected**: stating the sums. It would need `base_mul`'s/`E::mul`'s partial postconditions carried through every loop invariant; not needed for `MainSpecT`.
- **Claims (per function)**:
  - 18 (`ESumNovelT`): the zip's index word (`+ 48`) is `0` in `SumPreT` (the code adds it to both cursors); `novel_eval` stores `0` there (`Gen/Tmpl/Verifier/Whir/NovelEval.lean`, the store at `sp + 0x48`, iterator at `sp + 0x18`), and `NovelEvalT`'s proof discharges the whole `SumPreT` at that call (machine-checked, D8). Each side is a `SliceW` (end not below pointer; equal, or the bytes in a window and 8-aligned); the count is `min` of the two shifted lengths (`shr_sub`), and `SliceW.win` gives the windows of the first `n` elements.
  - 29 (`ESumProjectT`): `RMFE_PROJECT`'s 16 words are read at `hi + lo + x10 <<< 3` only when the index is below `16`: the code compares the index with `x12 = max(start, 16)` and panics on equality, so the loop invariant carries `x10 ≤ b ∧ (b = 16 ∨ x10 = b)` and the read path has `x10 ≠ b`. `tbl_win` turns `DataRef.InData` plus `Windows.data_ok` into the word's window. `mu[i]` reads go through `TabW.entry'` after the code's `i < mu.len` check.
  - 33 (`ESumFormT`): the terms are whole 40-byte elements (`(e - q) % 40 = 0`), as `count_toNat` needs: the code divides by `40` as `>> 3` then a multiplication by `0xcccccccccccccccd`, exact only on multiples of `5` (proved: `5 t * C = t + 2^64 (4 t)`). `TermsW` asks each monomial, unless empty, in a window and aligned; the terms' words are read through `MemOk`'s frame (`kept`), so the terms must be the caller's (`Owned`).
  - 24 (`ESumBlockT`): elements 32 bytes, `(e - s) % 32 = 0` (else the do-while loop's exit test `x22 ≠ x23` never holds: `x23 = s + 24 + ((e - s) & !31)`); `and_mask32` proves the mask is the identity on multiples of 32. Each pass stores the inner sum's iterator at `top - 96 .. top - 80` (below the nine slots, `MemOk.slot`, `iter_ok`) and discharges `ESumU16T.SumPreT` there (`rd3`, `rd3_ref`, `elem_ok`).
  - 27 (`ESumLaneT`): the zip's index `0`; unless empty, `c (n - 1) < v.len` (so every chunk is nonempty and lies in `v`), `v` and `eq_lane`'s first `n` elements in windows; `eq_z` a `VecW`. `dot` is called with `x11 = eq_z.len` and `x13 = min(rest, c)`, of possibly different lengths, so `DotSafeT.dotSafe` (which asks equal lengths) does not apply; `dotAny` restates it from `DotOwnT.specT` at `elemsAt` of each slice with its own length (`dot`'s `assert_eq` is then an abort, `AbortStop`).
- **Measures**: 18, 29, 24, 27: `Total.loop` on the elements (pairs, indices) left; 33: outer `Total.loop` on terms left (`OInv`, `d`), inner `Total.loop` on indices left (`IInv`, `k`), the inner exit continuing at the outer step (`after`, instruction 27) which closes over the outer induction hypothesis.
- **Evidence**: the modules build; `grep -n "Total.loop" Rv64mc/Proof/Field/ESum{Novel,Project,Form,Block,Lane}T.lean` shows one loop per function and two in `ESumFormT`.

### D2. Saved registers over `SavedT`, no new per-module `Saved`
- **What**: every new module with a frame defines `abbrev Mem := Runtime.SavedT.MemOk env top <out> [offsets] [ret, regs .x8, ...]` and `slots : SlotsIn K [...] := slots_le`, and carries `Mem` across calls with `MemOk.call_below`/`call` (`call_back`, `call_ok`), across frame stores with `MemOk.slot`. `InputDigestT`'s `out` is `DigestOut regs m`, `ESumNovelT`/`ESumFormT`/`ESumBlockT`/`ESumLaneT`'s `fun _ => False`.
- **Claims**: no new `def Saved` in this change: `git diff e0b25661c3 -- '*.lean' | grep '^+def Saved'` is empty.

### D3. Cuts where one executor run timed out at the default heartbeats
- **What and why**: no `maxHeartbeats` was raised. Where a run timed out I cut instead:
  - `ESumLaneT`: the entry stops after the prologue (instruction 14, `rv_autoT ... stop [28]`); `entry_ok` steps the rest with the iterator's words read at the prologue memory `M` and related to the entry's by `kept` after the run; the loop's return path stops at instruction 19 and `ret_ok` steps the epilogue alone (going `through` it timed out). The zip's and `eq_z`'s facts (`ZipW`, `VecW`, `Mem`) are hidden from the executor's closer in a `PLift` during `entry_ok`'s run and unpacked afterwards: with them in the context, the closer's `omega` calls split their disjunctions and the run timed out.
  - `ESumBlockT`: the element's facts (`k16`, `k24`, `hE`, `h8`, `h16`) are computed after `rv_symT` by the lemma `elem_ok`, not before: computed before, they slowed the run past the limit (bisected: the facts alone took 8 s; facts plus run timed out; run alone fit).
  - `InputDigestT`: cut after the four calls (`stores`, instruction 24) and after the 32 byte stores (`epi`, instruction 84); `byte_ok` carries `Mem` and `ReaderT` across one byte store, and the `bytes_close` macro (as `KeccakHashT.out_close`) peels the stores, so no epilogue load is read through 32 `setByte`s.
- **Evidence**: the modules build under the default `maxHeartbeats`; `grep -rn maxHeartbeats` over the eight new proof files is empty.

### D4. `Input::digest` (5): safety with the reader kept, the functional `DigestPost` owed
- **What**: `DigestPreT := DigestPre ∧ InWin a0 32 ∧ sp ≤ a1 ∧ ReaderT a1`; `DigestPostT := ReaderT a1` at the end; `Out := DigestOut` (the partial spec's); `Stop := AbortStop` (`Input::word`'s `WordStop` weakened by `mono_stop`). Started from wave 1a's draft (`ReaderT`, `ReaderT.next`); the draft's `ReaderT.next` did not compile (beta-unreduced `(fun _ => a) .x10` in the hypotheses, an `OfNat` `8` that `toNat_add_ofNat` did not unify); fixed with `dsimp only` and `(k := 8)`.
- **Why `sp ≤ a1`**: the reader is read after the prologue's six stores; `DigestPre` gives only `stackLimit ≤ a1`, which allows a reader inside the callee's own frame. At both of `main`'s calls the reader is `sp + 0x48` (`Gen/Tmpl/Main.lean` lines 144 and 494).
- **Why the result at or above `top` suffices for the slots**: `DigestPre`'s `sp ≤ a0` and `top` 16-aligned put every result byte's doubleword at or above `top`, above the six slots (`byte_ok`'s `hsv.keep`). The reader's two words are outside the result's doublewords by `DigestPre`'s non-overlap conjunct (`hd5`).
- **Rejected**: proving `DigestPost` (the 32 `extractByte`s): not needed for safety; recorded in "Owed by contracts already total".

### D5. `Scaler::new` (93): `safe` (environment facts only) and `total` (the partial postcondition, over `Scaled::new`'s partial contract)
- **What**: `safeT`: `PreS` (slot `InWin 24`, aligned, `Owned`) to `PostS` (`uses ≤ 255`: the slot holds `Plain` words; else `ScaledNewT.PostT`), `Out := NewOut`. `specT r`: `NewPreT r` (`NewPre ∧` window, alignment) to `PostS ∧ NewPost r`, by `HoldsT.of_holds` of `safe` with the partial `newSpec` (`hpart`).
- **Why two**: the brief says class A keeps the partial postcondition. `Scaler::new`'s partial proof (`ScalerNew.ok`) takes `Scaled::new`'s partial `newSpec`, and `Table.Multilinear.scalerNew` keeps it as a hypothesis: no proof of it exists (`Scaled::new` is class C; its total contract `ScaledNewT` is safety only). A port with `ScaledNewT` cannot reach `NewPost` (it needs the tables' values). So the contract with `NewPost` is at the image only over that hypothesis (`MultilinearT6f.scalerNew`'s `hsn`), and `scalerNewSafe` is the instance with environment facts only. The status row names `scalerNewSafe` as the `Table` theorem and says `scalerNew` also takes `hsn`.
- **Consequence for callers**: `Scaler::mul`'s total contract (`ScalerMulT.MulPreT`) asks `ScalerAt` of the model value, which only `NewPost` gives; so `eq_kernel` (137) and `multilinear_eval` (59, 90) need `scalerNew`, hence `Scaled::new`'s functional contract. Recorded in "Owed by contracts already total".
- **Rejected**: a `Table` theorem for `specT` presented as environment-only (false); dropping `NewPost` (against the brief).

### D6. `novel_eval` (80): safety only
- **What**: `PreT`: the coefficients `n = 0 ∨ InWin a0 (16 n) ∧ aligned`; `what` `NovelBasisT.SliceK`. `Post := True`, `Out` default (it writes only its frame: `novel_basis`' slot at `sp + 0`, the zip at `sp + 0x18`), `AbortStop`.
- **Claims**: its proof discharges `NovelBasisT.PreT` at its call and `ESumNovelT.SumPreT` at its call, the basis slice from `novel_basis`' `PostT` (`VecT` of `count` elements: `hret1_19`'s `BufT`, `hret1_21`'s `len ≤ cap`, `kslice`), the coefficients' by `eslice`. The iterator's reads through its eight stores are closed by `simp [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne, BitVec.add_right_inj]` after `BitVec.reduceAdd`.

### D7. Environment facts
- `RMFE_PROJECT table (InData)` is new (`ESumProjectT.Tab`), added to the legend at the top of `notes/total-status.md`; only its addresses matter (no value is used for an address: the bit test only selects which `mu[i]` to add).
- `MultilinearT6f.scalerNew`'s `hsn` is not an environment fact (D5); it is not in the row's "open hypotheses" column, which names `scalerNewSafe`'s.

### D8. Earlier obligations and argued call sites
- Discharged by a proof here: `novel_basis`' `PreT` and `ESumNovelT.SumPreT` at `novel_eval`'s calls (`NovelEvalT`); `ESumU16T.SumPreT` at `ESumBlockT`'s call (each pass); `DotOwnT.specT`'s precondition at `ESumLaneT`'s `dot` call; `Input::word`'s `WordPreT` at `Input::digest`'s four calls; `Scaled::new`'s `PreT` at `Scaler::new`'s tail call. No item of the ledger's existing "Obligations" list is struck: none names these call sites.
- Added to "Obligations" (argued from the templates, not proved): each new contract at its callers per `cg.json` (18 at 80 (proved, D6), 29 at 32, 33 at 146, 24 at 23, 27 at 138, 5 at 7, 93 at 137/59/90, 80 at 74). I re-ran the caller query on `cg.json` (`python3 -c ... if by[t]['mod'] in f['callees']`) for each index; the callers listed are exactly those.

## Invariants of the whole change
- No existing statement changed and no existing module edited: `git diff --stat e0b25661c3 -- formal/rv64mc/Rv64mc` lists only new files (12: eight proof modules, four `Table` modules). Other files changed: `notes/total-status.md`, `README.md`.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, raised `maxHeartbeats`: `grep -rnE "sorry|admit|native_decide|bv_decide|maxHeartbeats|^axiom"` over the twelve new files is empty.
- No em or en dashes in the new files, README or notes (grep for the two characters: no hits).
- Lines within 120 columns (`awk 'length > 120'` over the new files: no output).

## Not done
- `ring_switch` (61): started, deleted. A single `rv_autoT` to the first call (`grind_check`) timed out at the default heartbeats: the precondition I drafted (result and `point` windows, `Owned`, three `Apart`s, `s`, `TranscriptAtT`, `OwnedT`) gives the closer a dozen disjunctions. Plan: stop after the prologue (instruction 9), establish `Mem` (eight slots, `out := InRange a0 64 ∨ InRange a4 360`) and `TranscriptAtT`/`OwnedT` at the prologue memory by `kept` plus `TranscriptAtT.of_get`, then parts at each call with the transcript facts as hypotheses: `grind_check` (pc 36), `samples` (its `PreT` from `TranscriptAtT.1` and `OwnedT.sponge`), the `len > 7` check, `ring_coefficients` (its `f`, `g` from `SamplesT.PostT`'s `VecT`), `ring_target` (`g` `Live` from the same), the copy of `point`'s header and of the coefficients' header to `sret`. Drafted post: `TranscriptAtT`, `OwnedT` and the proof's address kept; unless the niche `-1` at `sret + 16`, `point`'s three words copied and the coefficients `VecT` of 64 `E`s at `sret + 40` (what `RingWeightEvaluateT.PreT` asks of `walk`'s weight).
- `verify_whir`'s closure 86, `induced_weight` (97), `sumcheck_round_poly` (107), `is_valid_encoding_of_a_leanisa_program` (216), the `GenericShunt` 171: not started (this pass's budget went to the list's earlier items). 86 is a tail call to `ext_row` or a `K`-to-`E` copy loop after `alloc`/`reserve` (like `ExtRowT`); its post must give `VecT` of 16-byte elements (`FoldRowT.PreT` at 74).
- The `E::sum` over `verify_layer`'s outer range (32) and over the blocks (23) became ready with 29 and 24 (`frontier_now.py`) but are not in the brief's list.
- Functional contracts recorded as owed: `Input::digest`'s `DigestPost`, `novel_eval`'s `evalSpec`, `Scaler::new`'s `NewPost` without `hsn` (via `Scaled::new`'s).

## Known risks
- `ESumBlockT.U16sW` asks every element's `Vec<u16>` pointer 2-byte aligned even when the vector is empty, because `ESumU16T.SumPreT` (wave 3c) asks `ptr % 2 = 0` unconditionally. An empty `Vec<u16>`'s dangling pointer is `2`, but no `VecT` or builder postcondition states it, so the obligation at 23 (and so at `group_by_word`, 218) may not be dischargeable from the representation predicates as they stand. If not, the fix is a corrected `ESumU16T` precondition (`ptr = end ∨ ptr % 2 = 0`, which its proof should still satisfy since nothing is read when empty) restated in a new module with a proof from the old one; I did not do it.
- `ESumFormT.SumPreT` and `ESumLaneT.SumPreT` require the walked buffers `Owned` (below `NEXT` or at or above the stack pointer). For `Form::evaluate` the terms are a `Form`'s heap buffer (`FormT`), below `NEXT`; for `verify_layer`, `claim.weights` and `eq_z` are heap vectors. A buffer that were a static constant would fail `Owned`; I read none of the callers' proofs (none is total), only their templates' iterator construction.
- `ESumProjectT` and `ESumNovelT`/`ESumLaneT` state `index = 0` for the zip or range start as given; `ESumProjectT` handles any start (the `max(start, 16)` bound), the zips do not (a nonzero index is not covered). All callers in the image pass `0` (checked in the templates of 80, 32 is a range not a zip, 138 not read beyond the brief's argument).
- `MultilinearT6f.scalerNew` carries a non-environment hypothesis (D5); a reviewer may prefer it not to be a `Table` theorem at all.
- `InputDigestT`'s frame `Out := DigestOut` includes the reader's two words; `InputWordT`'s `WordOut` is included by `call_ok`'s `hout`. The final `Frame` at the return comes from `Mem` (`epi` reads `hI` facts), not from a separate lemma; check that the returned `HoldsT.post`'s frame is `Frame top (DigestOut regs m) m m'` with the entry's `regs`, not the callee's.

## Pass 2

Head: dda69ebd22 (3 commits on aca10074f6, not pushed: 56b229de90 (61), fedf08d0b8 (86), dda69ebd22 (97)). Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.RingSwitchT Rv64mc.Proof.Whir.LanesOfT Rv64mc.Proof.Whir.InducedWeightT Rv64mc.Table.WhirT6f` -> `Build completed successfully (5638 jobs).` (each module rebuilt by `lake build` after its last change: `RingSwitchT` 58 s, `LanesOfT` 44 s, `InducedWeightT` 48 s, `WhirT6f` 10 s; no warnings from `lake env lean` on the three proof files).

### What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 61 | `ring_switch` | `RingSwitchT.specT` (safety, `TranscriptAtT`/`OwnedT` kept, proof's address kept, `OkW`; `Out` the slot, sponge, stream offset; `AbortStop`) | Proof/Whir/RingSwitchT | WhirT6f.ringSwitch | env; clmul table; keccak tables (InData) |
| 86 | `verify_whir`'s `lanes_of` closure | `LanesOfT.specT` (the slot `VecT` of `len` (level `0`) or `len / 2` elements, fresh unless no capacity; `SretOut 24`; `AbortStop`) | Proof/Whir/LanesOfT | WhirT6f.lanesOf | env |
| 97 | `induced_weight` | `InducedWeightT.specT` (safety, `Post := True`, `SretOut 24`, `AbortStop`) | Proof/Whir/InducedWeightT | WhirT6f.inducedWeight | env; clmul table |

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `175 10523` (pass 1 `172 10252`). Each `total` and each new `Table` theorem has a `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]`.

### Decisions

#### P2-D1. `ring_switch` (61): safety with the transcript kept; the functional `switchSpec` owed
- **What**: `PreT`: transcript (`a4`) `TranscriptAtT` and `OwnedT`; slot (`a0`, 64 bytes) `InWin`, aligned, `Owned`, `Apart` from the transcript and from its proof; point header (`a1`) `VecT 16`, `Owned 24`, `Apart` from the transcript and from the slot; `s` (`a2`, `a3`) none or `InWin` and aligned. `PostT`: `TranscriptAtT`, `OwnedT` at `sp`, the proof's address kept, `OkW` (unless the word at `slot + 16` is the niche `-1`, `VecT` at `slot + 16` and `slot + 40`, the weight's point and coefficients). `Out`: the slot, the sponge (328 bytes), the stream offset (narrower than the partial `SwitchOut`, so better for callers). `Stop := AbortStop`.
- **Why safety**: class C; the functional contract needs `samples`', `ring_coefficients`' and `ring_target`'s functional contracts, all safety-only. Recorded in "Owed by contracts already total".
- **Why `OkW`**: `walk` (42) passes the weight at `slot + 16` to `RingWeight::evaluate`, whose `PreT` asks `VecT` at the weight and at `weight + 24`; checked against `RingWeightEvaluateT.PreT`.
- **Why the point's `Owned` and two `Apart`s**: the header is read at instruction 96 after four calls; `point_kept` reads it through `Mem`'s frame (`getMem_owned_out`), which needs the header owned by the caller and outside `Out` (the slot, sponge, stream offset).
- **Structure** (D3 of pass 1's plan, redone): one executor run over two calls timed out (tried: `rt_ok` over `ring_coefficients` and `ring_target`, and `mid_ok` over `grind_check` and `samples`), so nine parts, each over at most one call: `kept` (prologue to instruction 32; the `PreT` facts packed into `Ctx` and cleared before the run), `mid_ok` (`grind_check`, the branch), `err_ok`, `sam_ok`, `len_ok`, `rc_ok`, `rt_ok`, `fin_ok`, `out_ok`. Each part's invariant is a register predicate (`ARegs`, `BRegs`, `CRegs`, `RRegs`, `DRegs`, `GRegs`) and `BaseM` (`SavedT.MemOk` with the eight slots, `TranscriptAtT`, `OwnedT` at `top`, the proof's address). Heavy facts are hidden from the executor's closer in a `PLift` (as pass 1's `ESumLaneT`). `base_call` carries `BaseM` across a call whose `out` is frame words below the slots, the sponge and the stream offset (it derives `TranscriptAtT` by `frameS`), `sponge_keep` the sponge across a call writing none of it, `base_slot` `BaseM` across a frame store.
- **The panic**: `len_ok` refutes `panic_fmt`'s branch (`samples(16)`'s `PostT` gives the length `16`); `panic_fmt` is not a hypothesis of `total`.
- **Evidence**: `RingSwitchT.total`; `WhirT6f.ringSwitch` takes `TranscriptT3.grindCheck`, `TranscriptT3.samples`, `WhirT6d.ringCoefficients`, `WhirT6d.ringTarget`.

#### P2-D2. `lanes_of` (86): `ExtRowT`'s pieces reused
- **What**: `PreT` is `ExtRowT.PreT` on `(a0, a2, a3)` (slot `InWin`, aligned, `Owned`; the row `ExtRowT.SliceW`). `PostT`: `VecT 16` at the slot, its length `len` if `a1 = 0` else `len / 2`, its capacity `0` or its buffer fresh.
- **Why reuse**: at level `0` its frame (64 bytes, five slots at the same offsets) and header at `sp` are `ext_row`'s, so `ExtRowT.Hdr`, `Hdr.push2`, `Hdr.vecT`, `Hdr.reserve` apply unchanged. `Hdr` contains `ExtRowT.Saved`, an existing five-slot definition: this module defines no new `Saved` (the brief's `SavedT` rule is about new definitions); I chose reuse over restating `Hdr` over `SavedT`.
- **The tail call**: above level `0` the executor discharged `ExtRowT.PreT` at the tail call from `PreT` (no goal left), and `PostT` from `ExtRowT.PostT` (three goals, closed by unfolding `vecLen`/`vecCap`/`vecPtr`).
- **Obligation struck**: `notes/total-status.md`'s `ext_row` entry said 86's proof must discharge `ExtRowT.PreT` at its tail call; it now does (marked struck, 74's call still argued).
- **Loop**: `Total.loop` on the words left (`LInv`), the source read backwards from `row + 8 (k - 1)`, the end test against `row - 8` (no wrap: `row ≥ 8` from `InWin`).

#### P2-D3. `induced_weight` (97): safety only
- **What**: `PreT`: slot (24 bytes) `InWin`, aligned, `Owned`; `queries` (8-byte elements), `query_weights`, `point` (16-byte) each `SliceN` (none, or `InWin` and aligned). `Post := True`, `Out := SretOut 24`, `AbortStop`.
- **Why `Post := True`**: class C; the partial `Post` is `Model.inducedWeightRust`'s value, which needs `Subspace::new`'s and `Subspace::at`'s functional contracts (owed). `GluedWeight::evaluate` (89) only returns the result. Recorded as owed.
- **Structure**: `total` runs the prologue to `Subspace::new`'s call (instruction 48), the `point.len ≠ message_log` error path closing automatically; `new_ok` steps the call (its frame by `MemOk.call_at`, so no slot is read through the call; an earlier version read the 13 slots through the call by `simp`/`omega` per slot and took 11 minutes, so it was replaced), the count `min`, and builds `Frm` (`frm_init`); `outer` (`Total.loop` on queries left) steps `Subspace::at`; `inner` (`Total.loop` on pairs left) is `inner_a` (two `base_mul`s) then `inner_b` (`E::mul`, cursors, and through instruction 72 to the next query or the exit): three calls in one run timed out. `keep_call` carries `Mem` and `Frm` across a call whose `out` lies in `what`'s slot.
- **Window facts**: each load's window is given to the closer as `inWindow ... = true` facts computed before the run (`InWin.dword`, `WinT.elem_toNat`); `what`'s buffer window from `Subspace::at`'s `VecT` (`BufT` with the length at most the capacity, the count at most the length).

### Claims
- No existing statement changed; no existing module edited except this wave's `Table/WhirT6f.lean` (three theorems and imports added), `notes/total-status.md` (rows 61, 86, 97; four obligation entries; two owed entries; one obligation struck) and `README.md` (one sentence per module). `git diff --stat aca10074f6 HEAD` lists exactly these plus the three new proof files.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, raised `maxHeartbeats` in the four Lean files (grep empty); no em or en dashes in them or the notes/README (grep count 0); lines within 120 columns.
- Every loop has a `Total.loop` measure: `LanesOfT.loop` (words left), `InducedWeightT.outer` (queries left), `InducedWeightT.inner` (pairs left).

### Call sites (Pre at every image caller, from `cg.json`)
- 61's caller is 42 (`walk`) only: slot `sp + 0x2c0`, point `sp + 0x440`, transcript `sp + 0x98` (`Gen/Tmpl/Verifier/Walk.lean`, the call at `L.base + 0x938`): windows, alignment, `Owned` and the three frame-to-frame `Apart`s by offsets; `Apart` slot/proof as `ReadOodT.PreT` already asks of 42's callers' slots; argued, added to "Obligations".
- 86's caller is 74 only: slot a frame slot, row `SliceW` from `merkle`'s opened leaves (`SliceKT`); argued, added.
- 97's caller is 89 only: slot its own `sret`, slices from `VecT`s and `x`; argued, added.
- Callee `Pre`s discharged by these proofs (machine-checked): `GrindCheckT.PreT`, `SamplesT.PreT`, `RingCoefficientsT.PreT`, `RingTargetT.PreT` at 61; `ExtRowT.PreT`, `ReserveSpecT`'s pre, `AllocPre` at 86; `SubspaceNewT.PreT`, `SubspaceAtT.PreT` (its `VecT`s from `Frm`) at 97.

### Not done (pass 2)
- `sumcheck_round_poly` (107): not started. 13 calls (`next_scalars`, `next_scalar`, `grind_check`, `grinding_bits`, `<[Vec<E>]>::concat`, `E::mul`, `E::sum`, `alloc`, `panic_nounwind_fmt`) and a transcript threaded through; at one call per executor run (what 61 needed) it is about seven parts with `BaseM`-style invariants (`RingSwitchT.base_call` is the pattern). Obstacle: budget.
- `is_valid_encoding_of_a_leanisa_program` (216, class A, 287 instructions, two loops) and the `GenericShunt` (171): not started (budget).
- `GluedWeight::evaluate` (89) became ready with 97 (`frontier_now.py`); class A, so its total contract with the partial postcondition rests on `induced_weight`'s partial spec (no proof), as `Scaler::new` did in pass 1 (D5). Not attempted.
- Functional contracts recorded as owed: `ring_switch`'s `switchSpec`, `induced_weight`'s `spec`.

### Where to look hardest
- `RingSwitchT.PreT`'s point conjuncts (`Owned`, `Apart` from slot and transcript) at `walk`: argued from offsets only; `walk`'s point header at `sp + 0x440` must be the `Vec` moved in, not a reborrow of a heap header.
- `RingSwitchT.Out` omits the transcript's other words: `base_call`'s `hout` obligations at each call show every callee writes only frame words, the sponge or the stream offset.
- `LanesOfT.PostT`'s length uses `if regs .x11 = 0#64`: the closure's `level` is passed in `a1` by value (the template compares `a1` with `0` directly); check 74's template passes it so.
- `InducedWeightT.keep_call`'s `hout` bound (`top - 128 ≤ a`, `a + 104 < top`): only `Subspace::at`'s slot; `base_mul`/`E::mul` write nothing.
- `frm_init` and `new_ok`: `Frm`'s `sp + 0x10` word is `point + 8` from `R .x21 = regs .x16` (added to `NRegs`, closed by `rfl` at the entry).
