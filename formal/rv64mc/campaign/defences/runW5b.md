# Defence: wave 5b, pass 1: the transcript's remaining callers `next_scalars`' iterator (212), `next_scalars` (44), `read_ood` (47) total, with `Table` instances; `Transcript::merkle`, WHIR, ring switch, the `E::sum` family and the rest not done

Base: 4d30c0ec3d. Head: 7af9bbfda2 (branch formal/rv64mc-total-w5b, worktree /home/devops/leanEthereum/leanVM-t-symt, 7 commits, not pushed; pass 1 ended at 15fdf54583, pass 2 added 8ba95862eb, see "## Pass 2", pass 3 added 7af9bbfda2, see "## Pass 3"; the current "Not done" list is pass 3's).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Transcript.ScalarsIterT Rv64mc.Proof.Transcript.NextScalarsT Rv64mc.Proof.Whir.ReadOodT Rv64mc.Table.TranscriptT4` -> `Build completed successfully (5252 jobs).` (last run cached; the runs after the last source changes rebuilt them: `ScalarsIterT` 95 s, `NextScalarsT` 95 s, `ReadOodT` 47 s, `TranscriptT4` 6 to 8 s, no warnings in these modules).

Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

## What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 212 | `GenericShunt<Map<Range, next_scalars::{closure}>>::next` | `ScalarsIterT.specT` (safety: `TranscriptAtT` kept; on `Some` the start was below the end and advanced by one; `Out := ScalarsIter.Out`, the partial spec's) | Proof/Transcript/ScalarsIterT | TranscriptT4.scalarsIter | keccak tables |
| 44 | `Transcript::next_scalars` | `NextScalarsT.specT` (safety: `TranscriptAtT` kept, the slot `VecT` unless `Err`; `Out := NextScalar.Out 24`, the partial spec's) | Proof/Transcript/NextScalarsT | TranscriptT4.nextScalars | env; keccak tables |
| 47 | `read_ood` | `ReadOodT.specT` (safety: `TranscriptAtT` kept, the point `VecT` unless `Err`; `Out := TOut 40`, the partial spec's) | Proof/Whir/ReadOodT | TranscriptT4.readOod | env; keccak tables |

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `132 5812` (base `129 5630`). The summary table is not updated (left to the merge). Each `Table` theorem and each module's `total` has a `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]`.

## Decisions

### D1. All three contracts are safety only, with the partial spec's `Out`
- **Why**: 212, 44 and 47 are class C; their functional contracts (`ScalarsIter.spec`, `NextScalars.spec`, `readOodSpec`) are stated over `next_scalar`'s, `samples`' and `grind_check`'s functional contracts, which rest on `keccak_f`'s (unproved; wave 4b's D1). Their callees' total contracts are safety contracts over `TranscriptAtT`, so the callers can only be safety contracts too. Each `Out` is the partial spec's (`ScalarsIter.Out`, `NextScalar.Out Layouts.ResultVecE.byteSize`, `Spec.Whir.Transcript.TOut Layouts.ResultVecEE.byteSize`), so a later functional proof can combine with these frames unchanged.
- **Rejected**: functional posts (non-environment `Table` hypotheses).
- **Claims**: `ScalarsIterT.PostT = TranscriptAtT m' T ∧ OwnedT m' sp T ∧ m'(T + 328) = m(T + 328) ∧ Advanced`, with `T := m.getMem (regs .x11)` and `Advanced regs m m' := m'.getMem (regs .x10) ≠ 0 → start < end ∧ m'(a + 8) = start + 1`. `NextScalarsT.PostT` and `ReadOodT.PostT` are `TranscriptAtT ∧ OwnedT ∧ proof address kept ∧ OkVec`, `OkVec := m'.getMem (regs .x10) ≠ -1 → VecT env m' (regs .x10) 16`. The functional contracts left owed are recorded in `notes/total-status.md`'s "Owed by contracts already total" (three new entries).

### D2. `ScalarsIterT.PreT`: the shunt, the slot and the residual, with the apartness the code's stores need
- **Definition**: the transcript (the shunt's word 0) `TranscriptAtT` and `OwnedT`; the shunt `a1` `InWin` 32, 8-aligned, `Owned`, apart from the transcript (360) and its proof (48); the slot `a0` `InWin` 24, aligned, `Owned`, apart from transcript, proof and shunt; the residual (shunt word 3) `InWin` 16, aligned, `Owned`, apart from transcript, proof and shunt.
- **Why each conjunct**: `Owned` of shunt, slot and residual: they are stored to after (or read across) `next_scalar`'s call and the epilogue reads the saved registers from slots just below `top`; without `Owned` the executor cannot show the slots apart (the run timed out at `whnf` until each was added: a failed read-through apartness shows as a timeout, not a goal). Apart slot/shunt: `Advanced` reads the shunt's start after the slot's three stores. Apart residual/shunt: the `None` path's stores into the residual come before the epilogue; without it the closer could not finish the return (time out), although `Advanced` is vacuous on that path. Apart from transcript and proof: `TranscriptAtT` after the stores and `out_miss` for `TranscriptAtT.frameS` in `total`.
- **Rejected**: a weaker precondition without residual/shunt apartness, proving the `None` path's post by hand: more proof for a fact the only caller has.
- **Claims (call sites)**: the only caller is `next_scalars` (44), at template steps 39 and 111 (body indices): slot `sp + 0x50` then `sp + 0x70`, shunt `sp + 0x18` then its copy `sp + 0x50`, residual `sp + 8`, all in 44's frame; machine-checked: `NextScalarsT.first_ok` and `loop` step through both calls with `ScalarsIterT.specT` and the closer discharges every conjunct (after rewriting the transcript's facts to `M.getMem (shunt)`, see D5).

### D3. `ScalarsIterT`: cut into `kept` / `mid` / `tail` / `none_ok`, the entry facts held in a structure `Ctx`
- **Why**: `rv_autoT` splits every `Prop` definition in `PreT` (`splitFact` unfolds any definition outside `Sym.keep`), so the 38 unfolded facts, about 20 of them disjunctions, went to every `omega` the closer ran and `rv_autoT … stop [14]` timed out. A `structure Ctx … : Prop` is not unfolded; `kept` packs the facts into it after `rv_autoT … stop [2]` and exposes only what each part reads. The parts' invariants (`MidInv`, `TailInv`, `NoneInv`) follow `NextScalarT`'s shape.
- **The memory facts in `kept` are proved by frames, not by reading stores**: `TranscriptAtT` and `OwnedT` after the prologue and the shunt's `+8` store come from `TranscriptAtT.frame` (out `= {a + 8}`, apartness from `Ctx`'s `Apart`) and `frameF`; the slots from `slots3` (by `getMem_setMem_ne` with `Whir.slot_ne`). An earlier version read the transcript's words through the stack stores with a `rw [getMem_setMem_ne]; rotate_left; omega` loop and the slots with `rv_closeT`: elaboration succeeded but the kernel check of `kept` was OOM-killed at the 16 GB scope three times (`journalctl`: `run-…scope: The kernel OOM killer killed some processes`, `oom-kill`); with `set_option debug.skipKernelTC true` (diagnostic only, removed) it passed in 114 s; bisection pinned the culprit to the parts proving reads through stores at `top + <literal>` addresses, but I did not identify the term. The final proof avoids both patterns.
- **`maxHeartbeats 1000000` on `tail`** (the only raised budget, with a comment): one `rv_symT` run over both outcomes of the tag and their three stores each exceeded 200000 for the declaration (`timeout at whnf` at the decl, while the same run with `stop [68]` passed). I did not measure the smallest budget that suffices.

### D4. `NextScalarsT`: the loop, its measure, and `Base`/`BaseM` carried by lemmas
- **Measure**: `LInv k` holds `(M.getMem (sp + 0x58)).toNat + k = count` (the shunt copy's start); the iterator's `Advanced` (D1) gives start `<` end on `Some`, so `k ≥ 1` and the next head has `k - 1`; `Total.loop` with `ih (k - 1)` at both back edges (direct store, and after `reserve`). The loop head is instruction 104 (the iterator's call), which the entry reaches by a forward jump; the back edges go to 92 (`store_ok`), which stores the element and continues to 104.
- **Invariants**: `Hdr` states the vector's header words (capacity, pointer = `x9`, length = `x19 ≥ 1` stored), its buffer `BufT`, `cap * 16 < 2^63`, `len ≤ cap`, the pointer at or above `NEXT` at entry (so stores into it are `frame_fresh`), and `x18 = 16 (len - 1)`; `SInv` adds `len < cap`. Element stores at `ptr + 16 len` and `+ 8` are in the heap window by `BufT` and `len < cap` (explicit `toNat` equations `hA`, `hA8` given to the closer).
- **`BaseM`** (frame, code, static, seven saved slots, `TranscriptAtT`, `OwnedT`, proof address equal to the entry's) is carried across each step by a lemma: `baseM_iter` (the iterator's frame), `baseM_callF` (`alloc`), `baseM_callS` (`reserve`, out the two header words), `baseM_store` (a store into the frame below the slots or into memory allocated since entry). The executor is used only for registers and the code's own reads; this avoids the kernel blow-up of D3.
- **Exit**: `fin_ok` stores `Ok` (cap, ptr, len) or the residual's error with tag `-1`; `vecT_stores` gives `VecT` of the slot from `BufT`, `cap * 16 < 2^63`, `len ≤ cap`; `sret_spongeT` keeps `SpongeT` through the three stores (slot apart from the transcript). On `Err` the slot's first word is `-1`, so `OkVec` is vacuous.
- **Claims (callees' `Pre` at their calls, machine-checked here)**: `ScalarsIterT.PreT` at both iterator calls (D2); `AllocPre` (`64 < 2^63`); `ReserveT.ReserveSpecT`'s `ReservePre ∧ VecT` at the `reserve` call (the closer from `hV : VecT env m1 (sp + 0x38) 16`, built by `vecT_hdr`); `Aborts` of `handle_error`.

### D5. Rewriting the transcript's facts into the shunt's word before the iterator's call
- **What**: in `NextScalarsT.first_ok` and `loop`, `rw [← h] at …` turns the `TranscriptAtT`/`OwnedT` facts about `regs .x11` into facts about `M.getMem (shunt)`, the form `ScalarsIterT.PreT` asks after the callee's registers are substituted.
- **Why**: without it the closer left nine of `ScalarsIterT.PreT`'s conjuncts open (it does not rewrite a hypothesis `M.getMem (sp + c) = regs .x11` inside a callee's precondition).
- **Claims**: the rewritten hypotheses are only the unfolded copies the executor reads; `BaseM`, `Hdr` and `Shunt` were captured whole beforehand (`have hBM := hinv.1.2` etc.) and are unchanged.

### D6. `ReadOodT`: `PreT` and parts
- **Definition**: `TranscriptAtT`/`OwnedT` of `a1`; the 40-byte slot `a0` `InWin`, 8-aligned, `Owned`, apart from the transcript and its proof. `count` (`a2`) is unconstrained: `samples` builds a vector of `count` elements or aborts.
- **Parts**: `kept` (entry to `grind_check`'s call, `AInv`), `mid_ok` (`grind_check`, its `Err` path to `err_ok`, `samples` to `next_scalar`'s call, `CInv`), `tail_ok` (`next_scalar`, `Ok` or `Err` stores, the return, proving `Holds.post` by hand: the closer left the saved registers, the frame and `PostK`). `baseM_call` carries `BaseM` across `samples`; `not_gcOut`, `not_nsOut`, `out_miss_frame` give the frames' misses.
- **Claims (call sites of 47, argued from the templates, not machine-checked)**: `walk` (42, `sites2.py readOod`: body step 121) passes `x10 = sp + 0x2c0`, `x11 = sp + 0x98` (walk's transcript, 360 bytes, ends at `sp + 0x200`), `x12` loaded from `sp + 0x2a8`; `verify_whir::<…>::{closure#1}` (74, step 295) passes `x10 = sp + 0x1e8`, `x11 = x18` (its transcript argument). The slots are the callers' frames: `Owned` (at or above the callee's stack pointer), `InWin` (stack window), 8-aligned (16-aligned `sp`); apart from the transcript in walk by the offsets, in 74 because the transcript is walk's (above 74's frame). The proof's apartness: the `Proof` is `main`'s, above every callee's frame or in the heap.
- **`next_scalars`' call sites** (`sites2.py nextScalars`): slots `sp + c` in the callers' frames at all thirteen sites (`TableSumcheck` 274, `VerifyBusBalance` 122, `VerifyKeccak` 508, `VerifyLayer` 23 and 240, `SumcheckRoundPoly` 28 and 83, `Walk` 27, 101, `VerifyWhir…Closure1` 134, 264, 284, 658, and the iterator 171 at 34): `NextScalarT.PreT`'s slot conjuncts hold by the frame; the transcript conjuncts are the transcript chain's existing obligation. Argued, not checked.

### D7. Notes and README
- `notes/total-status.md`: rows 212, 44, 47 `yes`; the obligation "next_scalars calls its iterator" added and struck as met; the transcript-callers obligation says 212's and 47's proofs discharge their callees' preconditions; three "Owed" entries (212's functional contract; 44's length and freshness; 47's point length and value). README: the new modules in the transcript chain's sentence, `TranscriptT4` in the `Table` list.

## Invariants of the whole change
- No existing statement changed: `git diff 4d30c0ec3d -- '*.lean'` touches only the four new files (`--stat`: `NextScalarsT.lean` 934, `ScalarsIterT.lean` 484, `ReadOodT.lean` 523, `TranscriptT4.lean` 66 lines added); the only removed lines in the diff are README's two layout lines and three status rows plus one obligation sentence, all replaced.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`: `git diff 4d30c0ec3d | grep -E '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by)'` is empty; the `#guard_msgs` axiom blocks pass in the build.
- One raised `maxHeartbeats` (D3), with its reason in a comment.
- Files changed only under `formal/rv64mc/Rv64mc/Proof/`, `Rv64mc/Table/`, `notes/`, `README.md`.
- No em-dash or en-dash added (`grep -n '—\|–'` over the four new files, the notes and README: empty).

## Not done
- Item 1's last function, `Transcript::merkle` (78, 148 instructions, six loops), and everything after it in the list: WHIR and ring switch (75, 77, 79, 82, 116, 126, 133, 134, 140, 96, then 76, 80, 61, 86), the `E::sum` family (18, 24, 27, 29, 33), `Input::digest` (5), `is_valid_encoding_of_a_leanisa_program` (216), `memmove` (225), `K::inv` (127). None stalled: the pass's budget went to the three functions above (`next_scalars` alone took most of it: its loop with `reserve` and the kernel blow-up of D3). The parts' lemmas (`BaseM` carriers, `vecT_stores`, `vecT_hdr`, `sret_spongeT`, `out_miss_frame`) are reusable by the next pass for `merkle` and `sample_queries`.
- No golf: the files are long (NextScalarsT 934 lines). Obvious duplication: the seven-slot rewriting blocks repeated in `baseM_iter`, `baseM_store`, `baseM_callF`, `baseM_callS`; `ReadOodT.BaseM` is a four-slot copy of `NextScalarsT.BaseM`; `ScalarsIterT.ne_owned`/`apart_ne`/`slots3` and `NextScalarsT.ne_of_toNat_lt`/`tr_words` overlap `WinT` and `Whir.Mem`.
- The history has a `wip(formal): …` commit (70e4ac8c7d) with `sorry`s in `NextScalarsT`, superseded by 6588d4122b; squash it if the branch's history matters.

## Known risks
- **The kernel OOM (D3)**: I removed the patterns that triggered it but did not identify the exact term; a reviewer re-running `lake build` of the three modules should watch memory (peak RSS of `lake env lean` on each file stayed near 3.5 to 4.2 GB in my last runs, `/usr/bin/time`).
- **`ScalarsIterT.PreT`'s extra conjuncts (D2)**: they are satisfiable at the only caller (machine-checked there), but they are more than the partial `ScalarsIter.Objects` in one respect: the shunt and residual `InWin` and aligned (the partial asks `InFrame`, which the totals need anyway). Look at whether any is unnecessary.
- **`OkVec` is weak**: no length and no freshness; a caller that writes into the returned vector, or needs `len = count` without a bounds check, cannot use these posts. Recorded as owed.
- **`Advanced` uses the tag word `≠ 0`**, not `OptionEAt`; at the image `None`'s tag is `0` and `Some`'s `1` (`Layouts.OptionE`), so the loop measure is sound, but the predicate is about the raw word.
- **Call sites of 44 and 47 (D6)** are argued from `sites2.py`'s register traces, not proved; `VerifyLayer` step 23's `x11` was not traced by the script (`?`).

## Pass 2

Head: 8ba95862eb (one commit on 15fdf54583: `feat(formal): Transcript::merkle total (MerkleT), at the image (TranscriptT5b)`).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Transcript.MerkleT Rv64mc.Table.TranscriptT5b` -> `Build completed successfully (5184 jobs).` (`MerkleT` about 60 s and 4.2 GB peak RSS by `/usr/bin/time -v` on `lake env lean`, `TranscriptT5b` 4 s, no warnings).

Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

### What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 78 | `Transcript::merkle` | `MerkleT.specT` (safety: `TranscriptAtT`, `OwnedT`, proof address kept; unless `Err`, the result `VecT` and each slice a path's leaf, `SliceKT`; `Out := Merkle.Out`, the partial spec's) | Proof/Transcript/MerkleT | TranscriptT5b.merkle | env; keccak tables; log2 tables (InData) |

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `133 5960` (pass 1: `132 5812`). The `Table` theorem and `MerkleT.total` each have a `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]`.

### Decisions

#### P2-D1. Safety contract with the partial `Out`; leaves as `SliceKT`
- **Why**: 78 is class C; its functional `Post` (`Model.TM.merkle`) needs `MerklePath::root`'s digest, whose total contract (`RootT`) is safety only. The callers (74) index the returned leaves (`ext_row`, `fold_row` read their words), so the post gives each slice allocated, in a window and 8-byte aligned (`SliceKT`), not only `VecT`.
- **Claims**: `PostT = TranscriptAtT m' T ∧ OwnedT m' sp T ∧ m'(T+328) = m(T+328) ∧ OkVec`, `OkVec := m'(a0) ≠ -1 → VecT m' a0 16 ∧ ∀ k < len, SliceKT m' (ptr + 16k)`. `Out := Merkle.Out` (slot or `T + 344`), so a later functional proof combines with this frame unchanged. Owed: the length (the queries' count) and the functional contract (recorded in "Owed by contracts already total").

#### P2-D2. `PreT`: the openings `OpeningsT`, the transcript in a caller's frame
- **Definition**: `TranscriptAtT`, `OwnedT`; `(regs .x2).toNat ≤ (regs .x11).toNat` (the transcript at or above the stack pointer); `OpeningsT env m q` for the proof `q`: the openings' buffer (`q + 32`, length `q + 40`) 8-aligned, `Live`, `InWin` of `24 n` bytes unless none, each opening `PathsT` (its paths' buffer likewise, `56 n` bytes, each path `PathT`: its leaf `SliceKT` at `path + 8`, its siblings, unless none, `Live` and `InWin` of `32 n` bytes); the slot `InWin 24`, 8-aligned, `Owned`, `Apart` from the transcript and from the proof; the root `InWin 32`; the queries (`a4`, `a5` words) `InWin (8 len)` and 8-aligned unless none.
- **Why each conjunct**: the code reads every opening it selects (bounds-checked offset), every path's `+16`, `+40` (shape loop), `+48` (positions loop), `+8`, `+16` (copy loop) and calls `root` on each path, whose `RootT.PreT` asks the path `Owned`, `InWin 56`, aligned, the leaf and siblings `Live`/`InWin` unless empty. `Live` (not only `Owned`) so the words are below `NEXT` at entry and so kept by every later frame (`keepLow`). The transcript at or above the stack pointer: the opening offset's store at `T + 344` comes before the reads of the paths, so it must miss them; with `T` in a caller's frame it is above `heapEnd`. Root `InWin 32`: `memcmp`'s `CmpPreT`. Queries: the positions loop reads `queries[j]`, `j < n` (the code checks `n == len` first).
- **Rejected**: requiring `top ≤ slot` (the slot is written only at the end, after all reads, so the frame keeps the narrower `OffOut` until then and is widened, `frame_widen`); `Apart` of the transcript from each path (needs a quantified apartness the call site can give only via the stack anyway).
- **Claims (call sites)**: the only caller is `verify_whir`'s stacked-opening closure (74), template steps 351 and 710 (`sites2.py merkle`): slot `sp + 0x1e8` (74's frame), transcript `x18` / `x20` (74's argument, `walk`'s frame at `sp + 0x98`, above 74's and so above merkle's stack pointer), root `*(sp + 0xb8)`, queries `(x20, x23)` from `sample_queries`. Argued from the template; `OpeningsT` is a new obligation on the `Proof` `main` decodes (added to `notes/total-status.md`'s "Obligations", with the queries' window from `sample_queries`' post).

#### P2-D3. Cut at loop heads, continuations as hypotheses
- **What**: `kept` (entry to the shape loop's head, instruction 82), `loop1` (82, `L1Inv`), `loop2` (112, `L2Inv`), `mid_ok` (154, the checked flag), `loop3` (162, `L3Inv`: `root`, `memcmp`), `coll_ok` (204, `DInv`: the capacity check, `alloc`), `loop4` (274, `L4Inv`: the copy), `fin_ok` (288, `FInv`), `err_ok` (132, `EInv`). Each part takes the next one as a hypothesis (`herr`, `hnext`, ...), `kept` composes them.
- **Measures**: each loop `Total.loop` with `k` the paths left: `x28 = 56 k` (loop1), `x6 = 56 k` and `x16 = 8 k` (loop2), `x18 = 56 k` (loop3), `x14 = buf + 8 + 16 (n - k)` against `x8 = buf + 8 + 16 n` (loop4, a do-while: `1 ≤ k` in the invariant, `k = 1` at the exit). A back edge is reached only with `k ≥ 1` (the branch's word equation turned into `k ≠ 0`), and `ih (k - 1)`.
- **Memory**: `BaseM` (frame writing only `T + 344`, code, static data, six saved slots) is carried by the executor in loops 1 and 2 (no stores), by `baseM_call` across `root` (out `DigestOut sp`, below the slots, `digestOut_low`) and `memcmp` and `alloc` (out `False`), and by `baseM_fresh2` across the copy's two stores (fresh: at or above `NEXT` at entry, below `NEXT` now, below `staticLo`).
- **Window facts the closer did not find**: given by hand (`w16`, `w40` in loop1 via `InWin.dword_add`; `w1`..`w4` in loop4 via `InWin.dword`; `hcw` and `byte_in` for `log2_strict`'s two table loads). In loop1 the closer did not use an identical `inWindow` hypothesis in context; the goals are closed by `any_goals (first | exact w16.1 | exact w40.1)`.

#### P2-D4. `log2_strict`'s tables as an environment fact
- `MerkleT.tables L` (the 8-byte de Bruijn multiplier and the 64-byte index) `DataRef.InData`, as `KeccakFT.tables`; `KeccakFT.table_range` gives each in a window and aligned. The index is read by a byte load at `base + (x >>> 58)` (`byte_in`: below 64). Added to the status legend as `log2 tables (InData)`.

#### P2-D5. Obligations
- Struck "`Transcript::merkle` (78) calls `MerklePath::root` (119)": discharged at the call in `loop3` (`hpm.1.leaf` for the leaf conjunct, `PathT.keep` for the path in the call's memory, the closer for the rest).
- New: 74 must establish `MerkleT.PreT` at its two calls (above), `OpeningsT` from the decoded proof.

### Invariants of pass 2
- No existing statement changed: `git diff 15fdf54583 HEAD --stat` touches only `MerkleT.lean` (new, 1018 lines), `TranscriptT5b.lean` (new, 43), `notes/total-status.md` (legend entry, one row, one obligation struck, one added, one owed entry) and `README.md` (two layout mentions).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, no raised `maxHeartbeats` (`grep` over both new files: empty).
- No em-dash or en-dash in the new files, notes or README lines.

### Not done (supersedes pass 1's list)
- Item 2, WHIR and ring switch, from its first function: `derive_config` (75), `sample_queries` (77), `Subspace::at` (79), `ext_row` (82), `novel_basis` (116), `subspace_roots` (126), `ring_coefficients` (133), `ring_target` (134), `instance_weights` (140), `Scaled::new` (96), then 76, 80, 61, 86. None attempted: the pass's budget went to `merkle`. Not abandoned: no obstacle found. `derive_config` has a functional callee contract (`WhirQueriesT.specT` gives `Post`) and two `grow_one` pushes; `sample_queries` calls `Sponge::sample` (total) and gives the queries `merkle`'s `PreT` asks in a window.
- Item 3, the `E::sum` family (18, 24, 27, 29, 33); item 4 (`Input::digest` 5, `is_valid_encoding` 216, `memmove` 225, `K::inv` 127): not attempted.
- No golf of `MerkleT` (1018 lines): `EInv` duplicates `Base`; the `base_regs` macro and the `baseM_*` lemmas overlap `NextScalarsT`'s and `ReadOodT`'s.

### Where to look hardest
- **`PreT`'s `(regs .x2).toNat ≤ (regs .x11).toNat`**: holds at 74's two calls only if 74's transcript argument is `walk`'s frame (74 is reached through `verify_whir` (86) and `verify_stacked_opening` (66) from `walk` (42), whose transcript is its frame at `sp + 0x98`, as pass 1's obligation on the transcript chain records; I did not trace the pointer through 66 and 86). If a later caller passes a heap transcript, this conjunct is the one to replace by an apartness from the openings.
- **`OpeningsT` is stated over all openings**, not only the one at the offset: satisfiable for a decoded proof (every vector allocated by the decoder), but it is a new obligation on `main`'s decoder, which has no total contract yet; check it is not stronger than what the decoder can give (alignment of each leaf's buffer: `Vec<K>` buffers from `alloc` are 8-aligned; empty leaves are exempt).
- **`OkVec`'s `SliceKT` is about the memory after the slot's stores**: proved from the copy's contents (`copy_step`) and the paths' `PathT` (`slices_of`), the slot apart from the fresh buffer (the slot `Owned` at entry: below `NEXT` at entry or above `top`).
- **The `log2_strict` byte load**: its window is from the table's 64 bytes (`byte_in`); its value is not used for safety (only compared to the siblings' count).

## Pass 3

Head: 7af9bbfda2 (one commit on 8ba95862eb: `feat(formal): derive_config total (DeriveConfigT), at the image (WhirT5b)`).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.DeriveConfigT Rv64mc.Table.WhirT5b` -> `Build completed successfully (5332 jobs).` (`DeriveConfigT` 64 s, `WhirT5b` 4.5 s; no warning in either module; the only warning in the log is the existing `Proof/Field/Reverse.lean` module-system note). Peak memory not measured; the scope's 16 GB was never hit.

Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

### What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 75 | `verifier::whir::derive_config` | `DeriveConfigT.specT` (safety: unless `Err`, `log_inv_rates` and `folds` `VecT` of one length, their buffers allocated since the entry, the queries `whir_queries`' slice of that length (`QueriesOk`); `Out := SretOut 64`, the partial spec's) | Proof/Whir/DeriveConfigT | WhirT5b.deriveConfig | env; WHIR query tables (InData) |

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `134 6110` (pass 2: `133 5960`). `DeriveConfigT.total` and `WhirT5b.deriveConfig` each have a `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]`.

### Decisions

#### P3-D1. Safety contract, the functional one owed
- **Why**: 75 is class C with `DeriveConfig.spec` (`ConfigResultAt`: the vectors' contents `FreshVecW` of `Model.deriveConfigRust`'s ladder). Proving the contents would need a second loop invariant relating both buffers to `Model.configLoop` through each `grow_one`'s byte copy (`Grown`'s third conjunct); the only caller (74) indexes the vectors with bounds checks, so its safety needs `VecT`, not contents. Recorded in "Owed by contracts already total".
- **Claims**: `PreT := DeriveConfig.Pre ∧ InWin a0 64 ∧ a0 % 8 = 0`; `PostT := m'(a0) ≠ -1 → OkCfg`, `OkCfg :=` `VecT m' a0 8 ∧ VecT m' (a0 + 24) 8 ∧ next m ≤ vecPtr m' a0 ∧ next m ≤ vecPtr m' (a0 + 24) ∧ vecLen m' a0 = m'(a0 + 56) ∧ vecLen m' (a0 + 24) = m'(a0 + 56) ∧ QueriesOk env log_n rate (m'(a0 + 48)) (m'(a0 + 56))`. `QueriesOk` is functional for the queries (`∃ qs, Model.whirQueriesRust log_n rate = some qs ∧ len = |qs| ∧ DataWords env ptr qs`), passed through from `WhirQueriesT.specT`'s post at no cost. The `Err` discriminant is the first word `-1` (`Layouts.ResultWhirConfig`: niche at offset 0, `nicheStart = 2^64 - 1`); on `Ok` that word is `log_inv_rates`' capacity, and `OkCfg` is proved on that path without using the antecedent.
- **Rejected**: functional `Post` (above); a `Fresh` upper bound in `OkCfg` (the buffers' `Live` in `m'` is already in `VecT`).

#### P3-D2. Cuts at each `grow_one`, the loop head, the exit and the epilogue
- **What** (pcs are body indices, label `L` at `2L`): `total` (entry to the first `grow_one` call 111, the skip to 212, `Err(WhirShape)` to 268), `g0_ok` (111 to 114, `G0Inv` to `E2Inv`), `e2_ok` (114 to 132, `folds` grown if full), `e3_ok` (132 to 168 or 212), the loop: `head_ok` (168 to 188, `log_inv_rates` grown if full), `a_ok` (188 to 152, `folds` grown if full), `b_ok` (152 to 168 or 212), `loop` (`Total.loop`), `exit` (212 to 268: the count check, `Ok` copy or `Err(QueryCountLadder)`), `ret_ok` (268: epilogue). Each part takes the next one's invariant as a continuation.
- **Why**: after a `grow_one` the executor cannot read the other header through the callee's frame (`GrowOut` is a definition `arithProve` cannot refute), so every branch on a header word after it splits; stopping right after each call and rebuilding the invariant from `Hd.grown`/`Hd.keep` (`grow_r`, `grow_f`) keeps every run short. `exit`'s single run through the 14 stores and the epilogue's 12 loads exceeded 200000 heartbeats; split at 268 (`RetInv`, `ret_ok`), no raised budget remains.
- **Measure**: `LInv k` holds `c.toNat = j + 1 + k` for `c = (log_n - 12) >>> 2` (the word in `x22` is `-c`); the back edge in `b_ok` is taken only when `-c + (j + 3) ≠ 2`, which gives `k ≠ 0` (`cnt_left`), and continues with `ih (k - 1)`. The entry to the loop (`e3_ok`) has `c ≠ 0` (else the jump to 212) and `k = c.toNat - 1`.
- **Room**: each element store needs the length below the capacity: from the branch `len ≠ cap` with `len ≤ cap`, or from `Grown`'s `cap + 1 ≤ cap'` after `grow_one`. The first pass's `folds` branch after `log_inv_rates`' grow is infeasible (the capacity is still 1) but is handled by the same general argument, not refuted.

#### P3-D3. `Hd`, the memory facts, and the lemmas carrying them
- `Hd env m ac ap al n M := BufT M cap ptr 8 ∧ cap * 8 < 2^63 ∧ M(al) = n ∧ n ≤ cap ∧ next m ≤ ptr` at literal frame addresses (`top + c`, so the executor's reads match syntactically). Carried by `Hd.keep`, `Hd.grown`, `Hd.heap` (a heap store: header words are stack, `NEXT` unchanged), `Hd.stk`, `Hd.len`. `BaseM` (frame writing nothing, code, static, `Saved`: the twelve saved slots) by `BaseM.call`, `BaseM.heap` (a store at or above `NEXT` at entry, below `NEXT` now: `Tactic.frame_fresh`), `BaseM.stk`. `RS` (frame writing the slot, static, `Saved`, `NEXT` unchanged) by `RS.tmp`, `RS.sret` for the exit's stores.
- At the entry's stops (`total`), `BaseM` and both `Hd`s of the concrete memory are closed by `rv_closeT` (frames, saved slots, header reads) once the two allocations' blocks are bounded below the heap's end (`h2b`, `h4b`); `NEXT` through the stores by `Env.next_setMem_stack` and `Tactic.next_setMem` (`nc`, `n1`, `n4`).

#### P3-D4. Callees' preconditions (machine-checked)
- `WhirQueriesT.specT`: `True`. `alloc`: `AllocPre` (8 bytes) by the closer, its `AllocStop` weakened to `AbortStop` (`mono_stop`), its failure (`a0 = 0`) to `panic_nounwind_fmt` (`Aborts`). `grow_one` (four call sites, `GrowOneSpecT env 8 8`): `GrowPreT`'s four conjuncts the closer leaves (the buffer's `Live` or empty, `cap * 8 < 2^63` twice, `BufT`) are closed from `Hd` after normalising `rvCapAt`/`rvPtrAt` (`hdr_r`, `hdr_f`); owned and in a window by the closer (the header in the frame).

#### P3-D5. Call site of 75 (argued from the template)
- The only caller is `verify_whir`'s stacked-opening closure (74), template step 22 (`sites2.py deriveConfig`): `a0 = sp + 0x140`, its frame, so `Owned` (at or above the callee's stack pointer), `InWin` (stack window) and 8-byte aligned (`sp` 16-aligned). Recorded in `notes/total-status.md`'s "Obligations". The post gives what 74 reads for safety: `folds.len()`, the zip of both vectors, `folds[0]` and `queries[level]` (bounds-checked), each `VecT` or the data window (`QueriesOk`'s `DataWords`, in windows by `Windows.data_ok`).

### Invariants of pass 3
- No existing statement changed: `git diff 8ba95862eb --stat` touches `DeriveConfigT.lean` (new, 970 lines), `WhirT5b.lean` (new, 43), `notes/total-status.md` (row 75, one obligation, one owed entry) and `README.md` (two layout mentions).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, no raised `maxHeartbeats`, no em-dash or en-dash in the new files (`grep -nE` over both: empty).
- Every new `Pre` checked at its call site (P3-D5); no earlier wave's argued callee `Pre` was discharged here other than at these calls (`grow_one`'s, `alloc`'s, machine-checked).

### Not done (supersedes pass 2's list)
- Item 2 from `sample_queries` (77) on: `Subspace::at` (79), `ext_row` (82), `novel_basis` (116), `subspace_roots` (126), `ring_coefficients` (133), `ring_target` (134), `instance_weights` (140), `Scaled::new` (96), then 76, 80, 61, 86. Not attempted, no obstacle found: the pass's budget went to `derive_config`. `sample_queries` (139 instructions) has two nested loops over `Sponge::sample` (the transcript chain, `TranscriptAtT`), `log2_strict`'s two tables (as `MerkleT.tables`) and a `Vec<u64>` pushed with `grow_one`: `DeriveConfigT`'s `Hd`/`grow_*` pattern and `MerkleT`'s table facts are the pieces; its result must give the window `MerkleT.PreT` asks of the queries.
- Item 3 (the `E::sum` family 18, 24, 27, 29, 33) and item 4 (`Input::digest` 5, `is_valid_encoding` 216, `memmove` 225, `K::inv` 127): not attempted.
- No golf of `DeriveConfigT` (970 lines): `head_ok`/`a_ok`/`e2_ok`/`g0_ok` repeat the four-goal `grow_one` closing block (a `local macro` would share it); `e2_ok`/`a_ok` and `e3_ok`/`b_ok` are the first pass and the loop's pass with different registers and could share a parametrised lemma; `RS.sret`/`BaseM.*` overlap `MerkleT.baseM_call` and `NextScalarsT.baseM_*`.

### Where to look hardest
- **`OkCfg`'s third and fourth conjuncts** (`next m ≤ ptr`): proved from `Hd`'s freshness, which `Hd.grown` re-establishes from `Grown`'s `Fresh M m1` and `next m ≤ next M`; together with `VecT`'s `Live` they say each buffer was allocated during the call, so apart from every object live at entry.
- **`QueriesOk` is a functional fact** in an otherwise safety contract: it is `WhirQueries.Post`'s `some` branch (`queriesOk_of`), the `none` branch being the `Err(WhirShape)` path (`r1 .x10 = 0`).
- **The first pass's infeasible branch** (P3-D2): handled, not refuted; check `e2_ok`'s no-grow path's room argument (`hne` from the branch, `hnf : 1 ≤ cap`).
- **The executor's closer proved the entry's frames and saved slots** (`total`, P3-D3) only after the two `alloc` blocks' upper bounds were in context; if `rv_closeT` changes, those `by rv_closeT` are the fragile spots.


## Golf

Head: af0b2db7c7 (one commit on 7af9bbfda2: `refactor(formal): golf wave 5b's transcript and WHIR proofs`). Files: `Proof/Transcript/NextScalarsT.lean`, `Proof/Transcript/MerkleT.lean`, `Proof/Whir/ReadOodT.lean`, `Proof/Whir/DeriveConfigT.lean` (107 insertions, 195 deletions). No statement, definition, `Pre`, `Post`, `Out` or `Table` theorem changed; no import added; no `maxHeartbeats` added; no em-dash or en-dash.

Skills: lean4:golf and lean4:refactor loaded.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Transcript.ScalarsIterT Rv64mc.Proof.Transcript.NextScalarsT Rv64mc.Proof.Whir.ReadOodT Rv64mc.Proof.Transcript.MerkleT Rv64mc.Proof.Whir.DeriveConfigT Rv64mc.Table.TranscriptT4 Rv64mc.Table.TranscriptT5b Rv64mc.Table.WhirT5b` -> `Build completed successfully (5514 jobs).` (the proof modules were rebuilt by the two runs before it: `NextScalarsT` 108 s, `DeriveConfigT` 71 s, then `MerkleT` and `ReadOodT`, both `Build completed successfully`; the three `Table` modules rebuilt in this run, 6 to 7 s each, so their `#guard_msgs in #print axioms` blocks passed again). No warning in the changed modules (the log's only warnings are the existing `Proof/Field/Reverse.lean` module-system note).

### G1. Saved-slot reads as one-line transitivity terms
- **What**: the 44 bullets `· rw [show (N#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - c) from rfl, hsl c (by omega) (by omega)]; exact hX` in `NextScalarsT.baseM_iter`, `baseM_store`, `baseM_callF`, `baseM_callS` (7 each), `ReadOodT.baseM_call` (4), `MerkleT.baseM_call`, `baseM_fresh2` (6 each) became `· exact (hsl c (by omega) (by omega)).trans hX` (mechanical, by a regex that matched only this exact shape).
- **Why equivalent**: each bullet proved the same goal `M'.getMem (top + N#64) = v`; the `rw [show … from rfl]` only rewrote `N#64` to the defeq `BitVec.ofNat 64 (2 ^ 64 - c)` so `hsl c` would match syntactically; `Eq.trans` checks that defeq directly (the form `DeriveConfigT.BaseM.call` already used). Same lemmas, same side conditions.

### G2. `Tactic.ne_of_toNat` in place of the local `NextScalarsT.ne_of_toNat_lt`
- **What**: removed `ne_of_toNat_lt (h : x.toNat < y.toNat ∨ y.toNat < x.toNat) : x ≠ y`; its uses in the three transcript-side files call the existing `Rv64mc.Tactic.ne_of_toNat (h : a.toNat ≠ b.toNat) : a ≠ b` (`Tactic/Heap.lean`), with `Or.inl (by …)` arguments unwrapped to `(by …)` and the `next_thru` macro's `right; …` / `left; …` alternatives without the `right`/`left`. The `open … NextScalarsT (…)` lists in `MerkleT` and `ReadOodT` and `NextScalarsT`'s "Main results" list drop the name.
- **Why equivalent**: both conclude `x ≠ y`; each argument's tactic proof (`rw [eqs]; omega` or `omega`) now proves `x.toNat ≠ y.toNat` from the same hypotheses it used to prove one side of the disjunction, which implies it. `ne_of_toNat_lt` was a proof helper with no caller outside these files (grep over `Rv64mc/`).

### G3. `DeriveConfigT.Saved.keep`
- **What**: the twelve-conjunct `Saved` transport, written out twice (`Saved.setMem` and `BaseM.call`), is one lemma `Saved.keep (h : Saved ret top regs M) (e : ∀ c, 0 < c → c ≤ 96 → M'.getMem (top + ofNat (2^64 - c)) = M.getMem (…)) : Saved ret top regs M'`; `Saved.setMem` passes its store's `e` (the same `getMem_setMem_ne` proof as before), `BaseM.call` its `hsl`.
- **Why equivalent**: `Saved.keep`'s body is the former tuple verbatim, abstracted over the slot-keeping function; `Saved.setMem`'s statement is unchanged; `BaseM.call` builds the same `BaseM` tuple with `hSv.keep hsl` for its fourth component.

### Considered, not done
- `DeriveConfigT.ne_off` duplicates `Whir.slot_ne` (`Proof/Whir/Mem.lean`), but `DeriveConfigT` does not import `Whir.Mem`; adding an import edge to remove a one-line lemma is not worth it.
- `DeriveConfigT`'s two `iterate 4` `grow_one` closing blocks (each written twice, six lines): a `local macro` would save about four lines net and hide which hypotheses close which goal.
- `e2_ok`/`a_ok` and `e3_ok`/`b_ok` as one parametrised lemma each, and sharing `BaseM` between `NextScalarsT` and `ReadOodT` (different `Out`, seven vs four slots): statement-level refactors of the cut structure, with kernel-memory risk (D3); left for a later pass.

## Amendments, round 1

Head: 5230f682a4 (one commit on af0b2db7c7: `docs(formal): wave 5b call-site notes for next_scalars, read_ood and merkle`; 9 commits on 4d30c0ec3d, not pushed). Files: `notes/total-status.md`, `Table/TranscriptT4.lean`, `Table/TranscriptT5b.lean`, `Proof/Whir/DeriveConfigT.lean` (comments, notes and one line wrap; no statement, definition or proof term changed).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.DeriveConfigT Rv64mc.Table.TranscriptT4 Rv64mc.Table.TranscriptT5b Rv64mc.Table.WhirT5b` -> `Build completed successfully (5514 jobs).` All four rebuilt in that run (olean timestamps 19:12 to 19:13 against `date` 19:13:30); the three `Table` modules' `#guard_msgs in #print axioms` passed again. No warning in these modules (the log's only warnings are the existing `Proof/Field/Reverse.lean` module-system note).

Skills: lean4:prove loaded.

### R1-1 (stale title, head, line counts): fixed here, earlier entries not edited
The lifecycle forbids editing earlier entries, so the corrections are stated here and supersede them:
- **Title**: the change makes total `next_scalars`' iterator (212), `next_scalars` (44), `read_ood` (47), `Transcript::merkle` (78, pass 2) and `derive_config` (75, pass 3), with `Table` instances. Not done: WHIR and ring switch from `sample_queries` (77) on, the `E::sum` family, item 4 (pass 3's "Not done" list stands). The title's "`Transcript::merkle` ... not done" is wrong since pass 2.
- **Head**: 5230f682a4, nine commits on 4d30c0ec3d (the header's "7af9bbfda2, 7 commits" was pass 3's; the golf added af0b2db7c7, this round 5230f682a4).
- **Line counts**: the figures in "Invariants of the whole change" (`NextScalarsT` 934, `ReadOodT` 523), pass 2's (`MerkleT` 1018) and pass 3's (`DeriveConfigT` 970) are pre-golf. Now (`git diff --stat 4d30c0ec3d`): `NextScalarsT` 879, `ScalarsIterT` 484, `ReadOodT` 516, `MerkleT` 996, `DeriveConfigT` 966, `TranscriptT4` 66, `TranscriptT5b` 44, `WhirT5b` 43.

### R1-2 (44's and 47's call sites missing from Obligations): fixed
`notes/total-status.md`'s transcript-chain entry now names both callees and their slot conjuncts (`NextScalarsT.PreT` is `NextScalarT.PreT`: the 24-byte slot in a window, 8-aligned, `Owned`, apart from the transcript and its proof; `ReadOodT.PreT`: the 40-byte slot likewise) and their sites, re-read with `sites2.py nextScalars` and `sites2.py readOod`. Correction to D6: `next_scalars` has fourteen call sites, not thirteen (D6's own list has fourteen entries): 54 step 274, 48 step 122, 60 step 508, 138 steps 23 and 240, 107 steps 28 and 83, 42 steps 27 and 101, 74 steps 134, 264, 284 and 658, and 171 step 34. Also new against D6: 171 is the `GenericShunt` over `verify_gkr_grand_products`' closure (`Gen/Index.lean`: `GenericShuntMapRangeUsizH358d5da0`, mangled name `...verify_gkr_grand_products0...`), and 54 and 171 were missing from that entry's caller list; both are now named in the added sentence. `read_ood`: `walk` step 121 (slot `sp + 0x2c0`, transcript `sp + 0x98`) and 74 step 295 (slot `sp + 0x1e8`, transcript `x18`), as D6 said.

### R1-3 (merkle's queries registers at step 710): fixed; P2-D2 corrected
Confirmed from the template (`VerifyWhirVerifyStackedOpeningClosure1.lean`, body indices without labels): at step 351 `x11 := x18` (343..344) and `x14 := x20`, `x15 := x23` (347, 348; `x20`, `x23` loaded from `sp + 0x1f0`, `sp + 0x1f8` at 326, 327); at step 710 `x20` is reloaded from `sp + 0xf8` (689) and `x11 := x20` (703), `x14` is loaded from `sp + 0x1f0` (695) and `x15 := x11` (702) with `x11` loaded from `sp + 0x1f8` (696). P2-D2's "the queries `(x20, x23)`" holds only at 351; the note now names, per site, the transcript (`x18`, then `x20`) and the queries (`(x20, x23)`, then `(x14, x15)`), both the buffer and length at `sp + 0x1f0`, `sp + 0x1f8` (the vector `sample_queries` returned at `sp + 0x1e8`). `MerkleT.PreT` is unaffected: it constrains `a4`, `a5`, which are these registers at both sites.

### R1-4 (TranscriptT4 header): fixed
The header now says the allocator's two facts are left for `next_scalars` and `read_ood` (the theorem `readOod` takes `hnext`, `hend`).

### R1-5 (the `wip` commit 70e4ac8c7d with two `sorry`s): deferred
Not squashed in this round: rewriting the branch changes every later hash (6588d4122b, a568c67c49, 15fdf54583, 8ba95862eb, 7af9bbfda2, af0b2db7c7) that this defence, the review files and the orchestrator's range `4d30c0ec3d..af0b2db7c7` cite, in a close-out pass that should only add commits. The head has no `sorry`: `grep -c sorry` over the eight new `.lean` files at 5230f682a4 gives 0 for each; 6588d4122b replaced the `wip` commit's two `sorry`s. What it takes: at merge, squash 70e4ac8c7d into 6588d4122b (`git rebase` with `fixup`, non-interactively via `GIT_SEQUENCE_EDITOR`), or squash-merge the branch, which the project's one-large-PR practice for `formal/` already does.

### R1-6 (long line, history wording): fixed
`TranscriptT5b.lean`'s `MerkleT.total` application is wrapped (longest line now under 120). `DeriveConfigT`'s header reads "It has no partial proof (class C)." Not changed: the other lines over 120 characters in the proof modules (`awk 'length>120'`: `ScalarsIterT` 118, 171, 191, 384, 386; `NextScalarsT` 199, 656, 766 to 769, 776, 842; `MerkleT` 402, 436, 907; `ReadOodT` 462; 121 to 146 characters), not flagged and in proof bodies whose rewrap would rebuild the four heaviest modules for no change; a later golf can wrap them.
