# Defence: wave 6b, pass 1: `sample_queries` (77), `Subspace::at` (79), `ext_row` (82) total with `Table` instances; the rest of the WHIR list, the `E::sum` family, `Input::digest`, `is_valid_encoding`, `K::inv` not done

Base: d067505500. Head: f2bb10fff8 after pass 3 (pass 2 ended at d62e5c6b03, pass 1 at 26de971f86; branch formal/rv64mc-total-w6b, worktree /home/devops/leanEthereum/leanVM-t-symt, 3 commits, not pushed: 329447d759 `sample_queries`, d51e13f6ba `Subspace::at` (also creates `VecWordT` and moves two lemmas into it), 26de971f86 `ext_row` (also generalises `VecWordT.vecT_stores`)).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.VecWordT Rv64mc.Proof.Whir.SampleQueriesT Rv64mc.Proof.Whir.SubspaceAtT Rv64mc.Proof.Whir.ExtRowT Rv64mc.Table.WhirT6b` -> `Build completed successfully (5394 jobs).` (last run cached; the runs after each last source change rebuilt the changed modules; the only warning in the log is the existing `Proof/Field/Reverse.lean` module-system note; the lakefile has `warningAsError = true`, so the new modules have no warning). Single-file timings by `/usr/bin/time -v lake env lean`: `SampleQueriesT` about 50 s wall, peak RSS 3.78 GB; `SubspaceAtT` and `ExtRowT` 28 to 35 s wall, 3.5 to 3.8 GB in the runs I measured (not all final runs were measured).

Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

## What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 77 | `verifier::whir::sample_queries` | `SampleQueriesT.specT` (safety: `TranscriptAtT`, `OwnedT`, proof address kept; unless `Err`, the slot `VecT` of 8-byte elements with `vecLen = count`; `Out := TOut 24`, the partial spec's) | Proof/Whir/SampleQueriesT | WhirT6b.sampleQueries | env; keccak tables; log2 tables |
| 79 | `<verifier::whir::Subspace>::at` | `SubspaceAtT.specT` (safety: the slot `VecT` of 8-byte elements, length `min roots.len inverses.len`, buffer fresh unless capacity `0`; `Out := SretOut 24`) | Proof/Whir/SubspaceAtT | WhirT6b.subspaceAt | env; clmul table |
| 82 | `verifier::whir::ext_row` | `ExtRowT.specT` (safety: the slot `VecT` of 16-byte elements, length `len / 2`, buffer fresh unless capacity `0`; `Out := SretOut 24`) | Proof/Whir/ExtRowT | WhirT6b.extRow | env |

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `144 7204` (base `141 6912`; summary table left to the merge). Each module's `total` and each `Table` theorem has a `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]`.

## Decisions

### D1. All three contracts are safety contracts; the functional ones are recorded as owed
- **Why**: all three are class C. `sample_queries`' functional post (`sampleQueriesSpec`, `Model.sampleQueriesRust`) needs `Sponge::sample`'s functional contract, which rests on `keccak_f`'s (not total; wave 4b D1). `Subspace::at`'s (`atSpec`) and `ext_row`'s (`ExtRow.spec`) are provable in principle (their callees' totals keep the partial posts) but need a loop invariant over the values written; the callers' safety needs only the result's `VecT` and length. Each `Out` is the partial spec's (`TOut 24` = `NextScalar.Out 24`, `SretOut 24`), so a later functional proof combines with these frames unchanged.
- **Rejected**: functional posts now (cost: a value invariant per loop; for 77 not available at all).
- **Claims**: three new entries in `notes/total-status.md`'s "Owed by contracts already total" (77, 79, 82), each naming the spec owed.
- **Evidence**: `git diff d067505500 -- formal/rv64mc/notes/total-status.md`.

### D2. `SampleQueriesT.PreT := NextScalarT.PreT`; `OkVec` gives the length
- **Definition**: `PreT` is `next_scalar`'s (transcript `TranscriptAtT`/`OwnedT`; the 24-byte slot `InWin`, 8-aligned, `Owned`, apart from the transcript and its proof), as `NextScalarsT` does. `OkVec regs m' := m'(a0) ≠ -1 → VecT env m' a0 8 ∧ vecLen m' a0 = regs .x13`.
- **Why**: the slot and transcript are what the code touches (the slot only at the exit; the sponge through `Sponge::sample`, whose `SampleT.PreT` is `SpongeT` and `Owned` of the transcript, both from `TranscriptAtT`/`OwnedT`). `block_length` and `count` need nothing: a non power of two gives `Err`, a count over `2^61` words aborts in `handle_error`. The length is cheap (the exit is reached with `len ≥ count` and the invariant has `len ≤ count`) and makes the post usable by `merkle`'s caller without a separate bound.
- **Claims (call sites)**: only caller 74, template steps 324 and 693 (`sites2.py sampleQueries`): slot `sp + 0x1e8`, transcript `x18` / `x20` loaded from `sp + 0xf8`. Argued, not machine-checked; added to "Obligations".

### D3. `grow_one` is refuted in `sample_queries` and `Subspace::at`, not stepped; `reserve`'s growth branch unused in `ext_row`
- **What**: both functions allocate the vector with capacity equal to (77) or at least (79) the number of elements they push, so the code's `len == cap` branch to `grow_one` is infeasible. The executor is stopped at the `grow_one` block's label (77: 224; 79: 140) and those goals are closed by `exfalso` from the branch equation (`len = cap`) against the invariant (`len < count = cap`; `len < n ≤ cap`). `grow_one` is not in `using`, so the executor never steps the call. In 82, `Hdr.reserve` uses only `ReservePost`'s room clause (`n ≤ cap - len`, with `len = 0` and `n ≤ cap`), so the header's capacity and pointer are kept; the `Grown` clause is never used.
- **Why**: stepping `grow_one` would require re-establishing the invariants across a reallocation that cannot happen.
- **Rejected**: `GrowOneSpecT` in `using` and the `Hd.grown` pattern of `DeriveConfigT`.
- **Claims**: `SampleQueriesT.LInv` has `M(sp+0x20) = count` (`Mem`'s fourth conjunct) and `len + k = count`; `SubspaceAtT.Inv` has `n ≤ cap` and `LInv` has `len + k = n`, `1 ≤ k`; the refutations are the `push_grow` macro (77) and the third bullet of `SubspaceAtT.loop`.

### D4. Cuts, measures, loop heads
- **`sample_queries`** (instructions, label `k` at `2k`): `kept` (entry to 152 or 234; the Err path to 248 `ret_ok`), `call_ok` (152: `Sponge::sample`, to 194), `loop` (194, `Total.loop`, measure `k` with `len + k = count`), `fin_ok` (234 to the return), `ret_ok` (248, epilogue). The executor passes 146 and 176 (`through`), which are backward-jump targets; every path from 194 back to 194, directly or through 146 and 152, pushes once, so the measure drops by one (`ih k` at the back edge, `hcall k (ih k)` through `call_ok`). The `eq` branch at 194 (`len = count`) goes to 146 and exits; its `¬ geu` continuation to 152 is refuted (`len = count`), and the `ne` branch with `k = 0` is refuted.
- **`Subspace::at`**: `total` (entry to 62), `mid_ok` (62: the header stored, the zip's `min`, to 122 or 152), `loop` (122, `Total.loop`, measure `k` with `len + k = n`, `1 ≤ k`), `fin_ok` (152). `total` alone over every path exceeded 200000 heartbeats (`timeout at whnf` at the declaration), so the cut at 62 was added; no raised budget remains.
- **`ext_row`**: `total` (entry to 50), `res_ok` (50: `reserve`, to 76 or 90), `loop` (76, `Total.loop`, measure `k` pairs left), `fin_ok` (90). The cut is at 50, not at the call's label 56, because the target register `x1` is set at 55 and the invariant does not record `L.s2.hi` (at 56 the executor stopped "at a call without a contract").
- **Claims**: no raised `maxHeartbeats`; every loop is `Total.loop` with the measure above.

### D5. Infeasible entry paths refuted by hand in `sample_queries`
- `sample_queries` entry: (a) `count << 3 = 0` with `count ≠ 0` (refuted by `ovf`: the overflow check gives `count * 8 < 2^63`); (b) the allocation path reaching `count == 0` (refuted: `count = 0` makes `count << 3 = 0`). The goals of (a) at its table loads are closed by `hcw`/`byte_in` before the refutation.
- `Subspace::at` has no refuted entry path in its final form: the cut at 62 (D4) leaves `total` three goals (the two paths to 62 and `AllocPre`) and `mid_ok` four feasible ones; its only refutation is `grow_one` (D3).
- **Claims**: every `exfalso` in the three files derives `False` from the context, not from a `sorry` (`#print axioms` pinned).

### D6. `Proof/Whir/VecWordT.lean`: `vecT_stores` and `shl3` moved out of `SampleQueriesT`, `vecT_stores` generalised to element size `s`
- **Why**: all three functions store a vector header into a slot at the exit; `shl3` is shared by 77 and 79. `vecT_stores` was first written in `SampleQueriesT` for 8-byte elements and generalised (implicit `{s : Nat}`) when `ext_row` needed 16.
- **Rejected**: importing `NextScalarsT.vecT_stores` (16 only, and a heavy import for `ExtRowT`).
- **Claims**: `VecWordT` is new in this change; its only users are the three new modules (`grep -rn VecWordT Rv64mc/` lists those and itself); the generalisation keeps the 8-byte uses compiling (the final check rebuilt them).

### D7. Patterns avoided after kernel or elaboration blow-ups (OOM-killed at the scope's limit)
- **`SampleQueriesT.call_ok`**: a frame lemma stated for every `c` (`m1.getMem (top + BitVec.ofNat 64 (2^64 - c)) = …`) and used with `.trans` against hypotheses at literal addresses (`top + 18446744073709551464#64`) was OOM-killed at 16 GB once the proof elaborated without errors; the version with a lemma over an explicit address (`∀ a, top - 160 ≤ a → a + 8 ≤ top → …`) builds in under a minute. I changed two things at once (the lemma's shape and a missing `a + 8 ≤ top` bound), so I did not isolate which caused it.
- **`SampleQueriesT.pushed`**: a `tns` macro (`simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega`) for frame-word inequalities inside `pushed` was OOM-killed (elaboration, with `debug.skipKernelTC` it still ran out); replaced by `rd` over an offset `c ≠ 18446744073709551504#64` (decided by `decide`) and `BitVec.add_right_inj`.
- **`ExtRowT.Hdr.reserve`**: bisected (each run under an 8 GB scope) to the frame bullet `rcases ha with rfl | rfl <;> simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega`; replaced by rewriting with `hdr_words` and `tn` per address. The earlier change of `hout` to an explicit-address lemma was made before the bisection and may not have been needed.
- **Claims**: `debug.skipKernelTC` appears in no committed file (`git diff d067505500 | grep skipKernel` is empty); no committed proof was shown to blow up at the final build.

### D8. `SubspaceAtT.PreT` and `PostT`
- **Definition**: `PreT`: the slot `InWin 24`, 8-aligned, `Owned`; `self` `InWin 48`, 8-aligned, `Owned`; `VecT env m self 8` and `VecT env m (self + 24) 8`. `PostT`: `VecT env m' a0 8`, `(vecLen m' a0).toNat = min (m(self+16)).toNat (m(self+40)).toNat`, and `vecCap m' a0 = 0 ∨ next m ≤ vecPtr m' a0`.
- **Why each conjunct**: `self` `InWin 48` and aligned: the closer needs `self + 8`, `+ 16`, `+ 32`, `+ 40`'s windows in one fact (it does not relate `(self + 24).toNat` to `self.toNat` from `VecT` at `self + 24`); `Owned` of `self`: its words are read after the prologue's stores and the allocation, so they must lie outside the frame and below `NEXT` or above `top` (`mid_ok` reads them in the post-allocation memory; with `ho11` in context the closer reads them through). `VecT` of both vectors: the loop reads `roots[i]` and `inverses[i]` for `i < min`, which `src_of` turns into `Src` (each buffer allocated before the entry, aligned, `8 n` bytes live) when `min > 0`.
- **Rejected**: the partial `AtPre` (`SubspaceAt`, functional `WVecAt`) as the precondition: safety needs only `VecT`; a caller with `SubspaceAt` would need a conversion lemma (not written).
- **Claims (call sites)**: `induced_weight` (97) step 54 (slot `sp + 0x60`, `self` `sp + 0x30`), 74 steps 392 and 743 (slots `sp + 0x210`, `sp + 0x1e8`, `self` `sp + 0x140`) (`sites2.py «at»`): the slot and `self` conjuncts are frame facts; `VecT` of both vectors must come from `Subspace::new`'s (76) total post, which does not exist yet. Recorded in "Obligations". Argued, not machine-checked.

### D9. `ExtRowT.PreT` (`SliceW`) and `PostT`
- **Definition**: `SliceW env m ptr len := len = 0 ∨ (Live m ptr (8 len) ∧ InWin ptr (8 len) ∧ ptr % 8 = 0)`, `MerkleT.SliceKT`'s shape over registers; `PostT`: `VecT env m' a0 16`, `(vecLen m' a0).toNat = len / 2`, fresh unless capacity `0`.
- **Why**: the loop reads `words[2i]`, `words[2i+1]` for `i < len / 2`; `Live` puts the words below `NEXT` at entry, so apart from the fresh buffer the loop writes and from the frame. The window asked is all `len` words, slightly more than the `2 (len / 2)` read when `len` is odd; the caller's `SliceKT` gives it.
- **`hw2`** (`res_ok`): the final address arithmetic needed `w + 8 len + 8 < 2^64`, which `InWin`'s `.lt` (`< 2^64`) does not give (an even `len` with `w + 8 len = 2^64 - 8` overflows); `hw2` takes the window's real bound (`≤ 0xc0000000`) from `InWin`'s two disjuncts.
- **Claims (call sites)**: 74 step 423 (slot `sp + 0x228`, words `(x25, x23)`) and the closure 86's tail call (step 16, its own `a0`, `(a1, a2)`) (`sites2.py extRow`). At 86 the slot conjuncts must be in 86's own precondition. Argued; recorded in "Obligations". `PostT`'s `VecT` of 16-byte elements is what `FoldRowT.PreT` asks of the row header at 74.

### D10. `Table/WhirT6b.lean`
- `sampleQueries` (callees `TranscriptT3.sample`, `RuntimeT.alloc`, `RuntimeT.handleError`), `subspaceAt` (`FieldT.baseMul`, `spread`, `reduce`, `RuntimeT.alloc`, `handleError`), `extRow` (`AllocT.reserveE`, `RuntimeT.alloc`, `handleError`); stacks by `decide` over `Gen.Needs`. Hypotheses: `HashT.KeccakTables`, `DataRef.InData env (SampleQueriesT.tables …link)` (the `log2_strict` tables of this function's own link, contents identical to `merkle`'s), `FieldT.ClmulTable`, and the allocator's two facts: all already in the status legend (`keccak tables`, `log2 tables (InData)`, `clmul table`, `env`); no legend entry added.

## Invariants of the whole change
- No existing statement changed: `git diff d067505500 --stat` touches only the five new `.lean` files (`ExtRowT` 390, `SampleQueriesT` 627, `SubspaceAtT` 429, `VecWordT` 57, `WhirT6b` 78 lines added), `notes/total-status.md` (three rows, three obligations, three owed entries, one obligation's sentence on `merkle`'s queries) and `README.md` (two layout mentions).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, raised `maxHeartbeats`, `set_option debug`: `git diff d067505500 | grep -nE '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by|maxHeartbeats)'` is empty; the axiom pins pass in the build.
- No em-dash or en-dash added: `git diff d067505500 | grep -n '^+.*[—–]'` is empty.
- No `Tactic/` file changed; no executor bug found.

## Obligations
- Discharged at their calls by these proofs (machine-checked): `SampleT.PreT` (each `Sponge::sample` call), `AllocPre` (all three), `ReservePre ∧ VecT` (`ext_row`'s `reserve`, from `Hdr.vecT`).
- Text changed, not machine-checked: the `merkle` obligation's queries window now says it follows from `SampleQueriesT.OkVec` (`VecT`, with `BufT.inWin` and `len ≤ cap`); no lemma states that conversion.
- New (argued): 74's calls of `sample_queries`, `Subspace::at`, `ext_row`; 97's call of `Subspace::at`; 86's tail call of `ext_row`; `Subspace::new` (76) must give `VecT` of both vectors.

## Not done
- Item 1 from `novel_basis` (116) on: `subspace_roots` (126), `ring_coefficients` (133), `ring_target` (134), `instance_weights` (140), `Scaled::new` (96), then `Subspace::new` (76), `novel_eval` (80), `ring_switch` (61), 86. Not attempted; no obstacle found: the pass's budget went to the three above. `novel_basis` calls `memcpy` (its `CopyPreT` and `CopyPostT` frame) and `Vec<K>::reserve` with growth (the doubling loop), so it needs `Grown`, unlike the three here.
- Item 2 (`E::sum` 18, 24, 27, 29, 33), item 3 (`Input::digest` 5, `is_valid_encoding` 216, `GenericShunt` 171), item 4 (`K::inv` 127): not attempted.
- No golf. Obvious duplication: the three `Saved`/frame-slot definitions (13, 12, 5 slots) and their keep lemmas; the slot-frame `frame_out` blocks in the three `fin_ok`s; `rd_push`/`Hdr.push2`/`Inv.push`.

## Known risks
- **Call sites argued, not checked** (D2, D8, D9): the slot and `Owned` conjuncts at 74, 86 and 97 are read from `sites2.py` traces; `Subspace::new`'s `VecT` is owed by a contract that does not exist yet. If `Subspace::new`'s post cannot give both vectors `VecT` (it builds `inverses` by a `map`/`collect`), `SubspaceAtT.PreT` is the place to weaken.
- **`OkVec`'s length** in `sample_queries` (`vecLen m' a0 = regs .x13`): proved from the exit branch `count ≤ len + 1` (or `count ≤ len` at the `eq` exit) with `len ≤ count`; look at `push_fin` and the `k = 0` branch of `loop`.
- **`ext_row` relies on `reserve` finding room**: `Hdr.reserve` uses `hroom` with `n ≤ cap - 0`; if the image's `ext_row` were ever compiled to reserve before allocating, this would no longer hold, but the proof would fail rather than be wrong.
- **D7**: the OOM causes are partly unidentified; a reviewer re-running the build should watch memory on `SampleQueriesT` and `ExtRowT`.
- **Linter-driven shape**: the entry of `SampleQueriesT.kept` closes eight goals by position (bullets in the executor's goal order); a change in the executor's goal order breaks it loudly, not silently.

## Pass 2

Head: d62e5c6b03 (one commit on 26de971f86: `feat(formal): novel_basis total (NovelBasisT), at the image (WhirT6b)`). Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.NovelBasisT Rv64mc.Table.WhirT6b` -> `Build completed successfully (5398 jobs).` (the only warning in the log is the existing `Proof/Field/Reverse.lean` module-system note; `warningAsError` is on, so the new module has no warning). `NovelBasisT` alone by `/usr/bin/time -v ... lake env lean`: 54 s wall, peak RSS 3.78 GB.

### What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 116 | `verifier::whir::novel_basis` | `NovelBasisT.specT` (safety: the slot `VecT` of 8-byte elements, `vecLen = count`, buffer fresh unless capacity `0`; `Out := SretOut 24`, the partial spec's) | Proof/Whir/NovelBasisT (773 lines) | WhirT6b.novelBasis | env; clmul table |

`WhirT6b.novelBasis`'s callees: `AllocT.reserveK`, `RuntimeT.alloc`, `RuntimeT.handleError`, `FieldT.baseMul`, `CopyUseT.memcpy`, `RuntimeT.panicNounwindFmt`, `RuntimeT.panicFmt`; stacks by `decide`; hypotheses `FieldT.ClmulTable` and the allocator's two facts, all in the legend. `#guard_msgs in #print axioms` pins `[propext, Classical.choice, Quot.sound]` for `NovelBasisT.total` and `WhirT6b.novelBasis`.

### Decisions

#### P2-D1. Safety contract; the functional one owed
- **Why**: class C; `basisSpec` (`Model.novelBasisRust`) needs a value invariant over two nested loops, a `memcpy` and a possible reallocation (the basis's words through `Grown`'s byte clause and `CopyPostT`). The caller (`novel_eval`, 80, then `E::sum` 18) needs for safety only the result's `VecT` and length. `Out` is the partial spec's `SretOut Layouts.Vec.byteSize`.
- **Claims**: an entry in "Owed by contracts already total" (116).

#### P2-D2. `PreT` and `PostT`
- **Definition**: `PreT`: the slot `InWin 24`, 8-aligned, `Owned`; `what` `SliceK` (`len = 0 ∨ (InWin ptr (8 len) ∧ ptr % 8 = 0)`). `PostT`: `VecT env m' a0 8`, `vecLen m' a0 = regs .x13` (as words), `vecCap = 0 ∨ next m ≤ vecPtr`.
- **Why**: `what` is only read (instruction 35, one word per pass), so neither `Live` nor ownership is asked: a read needs the window and the executor's alignment side goal only. `ExtRowT.SliceW` asks `Live` besides; I did not reuse it, to keep the call-site obligation weaker. `count` needs nothing: the outer loop exits when the length reaches it, the basis's bytes stay below the heap's end (`BV`), so `8 n` never wraps and an allocation the heap cannot serve aborts.
- **Claims (call site)**: only caller `novel_eval` (80), template step 11 (`sites2.py novelBasis`): slot `sp + 0` of its 112-byte frame (below its saved registers at `sp + 0x58`..`0x68`; `Owned` at the callee's stack pointer, the stack window, `sp` 16-aligned), `what` its `(a2, a3)`, `count` its `a1`. `novel_eval`'s total `PreT` must give `SliceK` of its `(a2, a3)`. Argued, not machine-checked; added to "Obligations".

#### P2-D3. Cuts and measures
- Labels are instructions; the executor's program counters are twice them (pass 1's "instruction 50" was a counter: `ExtRowT` stops at counters too). Cuts: `total` (entry to counter 68 = instruction 34, or 162 = 81), `outer` (68, `Total.loop`, measure `k` = `what`'s values left, `x18 + 8 k = what + 8 len`), `inner` (118 = 59, `Total.loop`, measure `j` products left, `x25 + 8 j = bptr + 8 n`), `app` (134 = 67), `fin_ok` (162). `app` runs `through [60]` (instruction 30, the increment block both `reserve`'s zero-length branch and the `goto` reach).
- **Nesting**: `outer`'s body takes `hin : ∀ k, (∀ R M, 2 ≤ k → OInv (k - 1) R M → Total at 68) → ∀ j R M, IInv k j R M → Total at 118`; `total` builds it as `inner (app ... hl)`, where `hl` is `outer`'s `ih (k - 1)`. So the outer measure drops by one through the inner loop and `app` (`hk2 : 2 ≤ k` from the branch `x18 + 8 ≠ x24`).
- **Claims**: no raised `maxHeartbeats`; both loops by `Total.loop`.

#### P2-D4. Memory invariant split: `MemOk` (frame, code, static, eleven saved slots), `BV` (the basis's header at `top - 136`), `Tmp` (the products' buffer `q`)
- **`BV`**: `1 ≤ len ≤ cap`, `cap * 8 < 2^63`, `next m ≤ ptr`, `0x10000000 ≤ ptr`, `ptr + 8 cap ≤ next M`, `ptr % 8 = 0`. `1 ≤ len` refutes the code's `len == 0` branches (instructions 38, 54, 72: six goals, by `zlen` on the named branch hypothesis).
- **`Tmp`**: `bptr + 8 cap ≤ q`, `q + 8 n ≤ next M`, `q % 8 = 0`. Gives the inner loop's stores fresh memory (`q ≥ bptr + 8 cap ≥ next m`) and `memcpy`'s ranges apart.
- **Lemmas** (each over the exact hypothesis shapes the executor leaves): `MemOk.call`, `MemOk.fresh`, `MemOk.slot`, `BV.keep`, `entry_bv`, `tmp_reads`, `after_tmp` (alloc, three slot stores, `reserve` of the products finding the room), `prod_step` (`base_mul` and a store), `after_basis` (`reserve(n)` of the basis: room case keeps `ptr`, `cap`; `Grown` case gives a block fresh after `q`'s, so `.inr` disjointness), `copy_ok` (`memcpy`'s `CopyOut` inside `[ptr + 8 n, ptr + 16 n)`, then the length `2 n` stored).

#### P2-D5. Callee preconditions discharged (machine-checked)
- `AllocPre` (both allocations: `8`, and `n <<< 3` below `2^63` from `BV`), `ReservePre ∧ VecT` (both `reserve`s: the products' header from `tmp_reads`, the basis's from `BV`), `CopyPreT false` for `memcpy` (no wrap; disjoint by `after_basis`'s disjunction; destination in the heap window and below `stackLimit`; source `inWindow` from `q ≥ 0x10000000` and `q + 8 n ≤ heapEnd ≤ 0x78000000`; both `OffStack` by `.inl`). This is a real call site of `memcpy`'s `CopyPreT` (an argued Pre of wave 1a) discharged.

#### P2-D6. Patterns avoided
- A `simp (disch := ...) only [getMem_setMem_ne, ...]` closer with `simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega` as discharger, run over the executor's goals, was killed (SIGTERM, about 4 minutes) once; replaced by explicit `rw` chains in small lemmas (`entry_bv`, `tmp_reads`). `‹_ : M.getMem … = 0#64›` and `contradiction` over the executor's contexts hit `maximum recursion depth`; replaced by `zlen <name>`. `first | zlen hc | zlen hc_1 | …` was flagged by the unused-tactic linter (warnings are errors), so each refuted goal names its hypothesis.

### Invariants of pass 2
- No existing statement changed: `git diff 26de971f86 --stat` touches the new `Proof/Whir/NovelBasisT.lean`, `Table/WhirT6b.lean` (one theorem, its imports and pin, the header's list), `notes/total-status.md` (row 116, one obligation, one owed entry), `README.md` (one layout mention).
- `git diff 26de971f86 | grep -nE '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by|maxHeartbeats|skipKernel)'` is empty; no em-dash or en-dash added; no `Tactic/` change; no executor bug found.

### Not done (pass 2)
- Item 1 from `subspace_roots` (126) on: `ring_coefficients` (133), `ring_target` (134), `instance_weights` (140), `Scaled::new` (96), then `Subspace::new` (76), `novel_eval` (80), `ring_switch` (61), 86. Not attempted: the pass's budget (its context) went to `novel_basis`. Notes for the next pass: `subspace_roots` calls the `memmove` wrapper (228), whose `Table` instance (`RuntimeT.memmove`) still takes `MemmoveSpecT` (225, wave 6a's) as a hypothesis, so its `Table` theorem would carry that until 6a lands; `Vec::remove(0)` on the layer never hits `remove::assert_failed` (the layer has `log_n - t ≥ 1` elements at pass `t`); `roots.push` needs `grow_one` stepped (capacity 1 at the start), unlike pass 1's three. `NovelBasisT`'s `after_basis`/`copy_ok` pattern (reserve then `memcpy` into the spare room) fits `ring_coefficients` (133), which also calls `reserve` and `memcpy`.
- Items 2 (`E::sum` 18, 24, 27, 29, 33), 3 (`Input::digest` 5, `is_valid_encoding` 216, `GenericShunt` 171), 4 (`K::inv` 127): not attempted.
- No golf: `MemOk`/`Saved` duplicate pass 1's `Saved`/frame patterns and `ColumnKappasT.MemOk`, each specialised to its frame's slot count.

### Where to look hardest
- **`outer`'s refutations** (`zlen hc`, `zlen hc_2`): which branch each goal's `hc*` is was read from a trace; the goals are the zero-length branches at instructions 38 and 54. A wrong name fails the build, it does not prove the wrong thing.
- **`after_basis`'s growth case**: disjointness `.inr` rests on `Grown`'s `Fresh M m1` (new block at or above `next M`) and `Tmp`'s `q + 8 n ≤ next M`. If `reserve` grows in place (it does not: `finish_grow` allocates), this would need revisiting; the proof uses only the contract.
- **`copy_ok`'s `hout`**: `CopyOut` is `DwordsOf dst (8 n)`, rewritten with `toNat_alignToDword` and `dst % 8 = 0` (from `ptr % 8 = 0`); the range lies in `[ptr + 8 n, ptr + 16 n) ⊆ [ptr, ptr + 8 cap)`, fresh since the entry.
- **`PostT`'s `vecLen = regs .x13`** comes from the exit storing `x8` (`count`) after the `assert!` (`¬ len < count`), not from the basis's length: `truncate(count)`.

## Pass 3

Head: f2bb10fff8 (one commit on d62e5c6b03: `feat(formal): subspace_roots total (SubspaceRootsT), at the image (WhirT6b)`). Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.SubspaceRootsT Rv64mc.Table.WhirT6b` -> `Build completed successfully (5400 jobs).` (the only warning in the log is the existing `Proof/Field/Reverse.lean` module-system note; `warningAsError` is on, so the new module has no warning). `SubspaceRootsT` alone by `/usr/bin/time ... lake env lean`: 73 s wall, peak RSS 4.3 GB.

### What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 126 | `verifier::whir::subspace_roots` | `SubspaceRootsT.specT` (safety: the slot `VecT` of 8-byte elements, `(vecLen).toNat = log_n + 1`, buffer fresh unless capacity `0`; `Out := SretOut 24`, the partial spec's) | Proof/Whir/SubspaceRootsT (987 lines) | WhirT6b.subspaceRoots | env; clmul table; MemmoveSpecT (225) |

`WhirT6b.subspaceRoots`' callees: `AllocT.reserveK`, `RuntimeT.alloc`, `RuntimeT.handleError`, `FieldT.baseMul`, `FieldT.spread`, `FieldT.reduce`, `RuntimeT.memmove`, `AllocT.growOneK`, `RuntimeT.panicNounwindFmt`; stacks by `decide`. Hypotheses: `FieldT.ClmulTable`, the allocator's two facts, and `MemmoveSpecT` of `compiler_builtins`' `memmove` (225), which `RuntimeT.memmove` takes; all four are in the status legend (the last is the legend's one non-environment entry, wave 6a's to discharge). `#guard_msgs in #print axioms` pins `[propext, Classical.choice, Quot.sound]` for `SubspaceRootsT.total` and `WhirT6b.subspaceRoots`. `awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `146 7477`.

### Decisions

#### P3-D1. Safety contract; the functional one owed
- **Why**: class C; `rootsSpec` (`Model.subspaceRootsRust`) needs the layer's words carried through `spread`, `reduce`, `base_mul`, `memmove`'s `CopyPostT` and `roots`' words through `grow_one`'s copied bytes, per pass. The caller `Subspace::new` (76) needs for safety the result's `VecT` and length (its `reserve` and its `K::inv` loop over the roots), and `Subspace::at`'s `PreT` asks `VecT` of `roots`. `Out` is the partial spec's `SretOut Layouts.Vec.byteSize`.
- **Claims**: an entry in "Owed by contracts already total" (126).

#### P3-D2. `PreT` without `log_n < 64`
- **Definition**: `PreT`: the slot `InWin 24`, 8-aligned, `Owned` (as `NovelBasisT`). `RootsPre` has `log_n < 64` besides; the total contract drops it: the code is safe for every `log_n` (the size check `log_n >> 61 = 0 ∧ 8 log_n ≤ 0x7ffffffffffffff8` sends larger ones to `handle_error`; `1 << (i & 63)` never faults; the layer's `alloc` aborts if the heap cannot serve it). So the call-site obligation is weaker.
- **`PostT`**: `VecT env m' a0 8 ∧ (vecLen m' a0).toNat = (regs .x11).toNat + 1 ∧ (vecCap = 0 ∨ next m ≤ vecPtr)`. The length as a `Nat` equation (not a word) since `log_n + 1` as a word would need the size check's bound to read.
- **Claims (call site)**: only caller 76, template step 11: slot `sp + 8` of its 112-byte frame (below its saved registers at `sp + 0x38`..`0x68`), `log_n` its own `a1` passed on (`sites2.py subspaceRoots`). Argued, not machine-checked; added to "Obligations".

#### P3-D3. Cuts, measures
- Program counters are twice the labels. Cuts: `total` (entry to 108 = instruction 54), `mid` (108: `reserve(log_n)` of the layer, or `reserve(0)` and the exit for `log_n = 0`; to 134, or to 184 for `log_n = 1`), `fill` (134 = 67, `Total.loop`, measure `j` words left, `x12 + j = log_n`; its exit stores the last word and reaches 184), `outer` (184 = 92, `Total.loop`, measure `k` = the layer's length `x26`, `len(roots) + k = log_n + 1`), `inner` (208 = 104, `Total.loop`, measure `j` words left, `x9 + 8 j = p + 8 k`), `rem` (240 = 120: `memmove`, the capacity test, `grow_one` if full; to 168), `push` (168 = 84: the push, `len + 1` stored, to 184 or 278), `fin_ok` (278 = 139).
- **Nesting** as `NovelBasisT`: `outer`'s body takes `hin : ∀ k, (∀ R M, 2 ≤ k → OInv (k - 1) R M → Total at 184) → ∀ j R M, IInv k j R M → Total at 208`; `total` builds it as `inner (rem (push hfin hl))`, `hl` being `outer`'s `ih (k - 1)`. `push`'s back edge has `2 ≤ k` from the branch `t + 1 ≠ log_n` (the passes counter at `sp + 0x18`, `t + 1 + k = log_n + 1`).
- **Why the cut at 168**: `rem` with the push stepped on both paths (with and without `grow_one`) ran out of the default 200000 heartbeats in the second path's closing (`timeout at whnf`); cutting at the join point 168 (a backward-jump target from `goto 84`) steps the push once. No raised budget anywhere.
- **Claims**: no raised `maxHeartbeats`; every loop is `Total.loop` with the measure above.

#### P3-D4. Memory invariants: `MemOk` (frame, code, static, 13 saved slots), `RV` (`roots`' header at `top - 152`), `Lay` (the layer's buffer `p`: allocated since the entry, `p + 8 log_n ≤ NEXT`, aligned), plus per-cut word facts
- The layer's header is not kept after `mid`: `remove` keeps the layer's length in `x26` only (the code never stores it back), so the invariants carry `p` as a parameter (`OInv`, `RInv`, `IInv`, `PInv` take `lp`) and the length in registers (`x26`, `x27 = 8 k`) and in the slot `sp + 0x10` (`8 k`, `memmove`'s size).
- Disjointness of `roots`' buffer and the layer's is not tracked: safety needs only that every store lands in memory allocated since the entry (`MemOk.fresh` / `heap_ok`), which both buffers are.
- **Lemmas** each over the hypotheses the executor leaves: `mv_ok` (`memmove`: `CopyOut` inside `[p, p + 8 log_n)`), `grow_ok` (`grow_one`: `Grown` gives capacity `+ 1` and a block fresh after `NEXT`, so `RV` with room), `res_ok` (`reserve` writing at most the layer's header), `call_ok` (`spread`, `reduce`, `base_mul`), `heap_ok`, `slots3` (the pass's three slot stores), `push_ok`; each returns that the frame's other words read as before, which the closing steps use by explicit offsets (`rd c q rfl ...`).

#### P3-D5. Callee preconditions discharged (machine-checked)
- `AllocPre` (both allocations: `8`, and `log_n <<< 3` below `2^63` from the size check, `SampleQueriesT.ovf`), `ReservePre ∧ VecT` (both `reserve`s of the layer's header, `rpre`), `GrowPreT 8 8` (`grow_one` of `roots`' header, from `RV` after `memmove`), `CopyPreT true` for `memmove` (no wrap; destination `p` in the heap window, `OffStack` by `.inl`; source `p + 8` `inWindow` by `inWindow_iff`; size `8 k - 8`, `0` allowed). `memmove`'s `CopyPreT true` is `MemmoveSpecT`'s stated precondition (wave 1b); this is its first total caller, and the call site discharges it.
- `remove::assert_failed` is refuted (`x26 = 0` against `1 ≤ k`), not stepped, so `total` takes no contract of it; `Table` passes none.

#### P3-D6. Import of `SampleQueriesT` for `ovf`
- `ovf` (the size check gives `x * 8 < 2^63`) is in `SampleQueriesT` (pass 1). I imported that module rather than duplicating the lemma or moving it (moving would restructure pass 1's commit). Cost: `SubspaceRootsT` now depends on the hash and transcript modules `SampleQueriesT` imports (already built). A later golf could move `ovf` to `VecWordT`.

### Invariants of pass 3
- No existing statement changed: `git diff d62e5c6b03 --stat` touches the new `Proof/Whir/SubspaceRootsT.lean`, `Table/WhirT6b.lean` (one theorem, its import and pin, the header's lists), `notes/total-status.md` (row 126, one obligation, one owed entry), `README.md` (one layout mention).
- `git diff d62e5c6b03 | grep -nE '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by|maxHeartbeats|skipKernel|trace_state|[—–])'` is empty; no `Tactic/` change; no executor bug found.

### Not done (pass 3)
- Item 1 from `ring_coefficients` (133) on: `ring_target` (134), `instance_weights` (140), `Scaled::new` (96), then `Subspace::new` (76, now unblocked by 126 except for `K::inv` 127), `novel_eval` (80), `ring_switch` (61), 86. Not attempted: the pass's budget went to `subspace_roots`. `ring_coefficients` fits `NovelBasisT`'s `after_basis`/`copy_ok` pattern (`reserve` then `memcpy`), and `SubspaceRootsT`'s `mv_ok`/`grow_ok`/`push_ok` shapes fit other push loops.
- Items 2 (`E::sum` 18, 24, 27, 29, 33), 3 (`Input::digest` 5, `is_valid_encoding` 216, `GenericShunt` 171), 4 (`K::inv` 127): not attempted.
- No golf: `MemOk`/`Saved` again duplicate the earlier modules' frame patterns (13 slots here); `ovf` imported from `SampleQueriesT` (P3-D6).

### Where to look hardest
- **`PInv`'s room** (`len < cap`): from the branch `x25 ≠ cap` with `len ≤ cap` (`rem`'s first goal), or `grow_ok`'s `cap' ≥ cap + 1` with `len = cap`. A reviewer should check the second: `grow_ok` derives it from `Grown`'s first clause and `RV`'s `len ≤ cap`, with `m1`'s length word kept (`GrowOut` is only the capacity and pointer).
- **`mv_ok`'s `hout`**: `CopyOut` is `DwordsOf p (8 k - 8)`, rewritten with `toNat_alignToDword` and `p % 8 = 0`; it must lie in `[next m, p + 8 log_n)`, which needs `k ≤ log_n` (from `len ≥ 1` and `len + k = log_n + 1`).
- **The `log_n = 1` path in `mid`**: it skips the fill loop and stores `1 << 1` at `p + (0 <<< 3)` (the layer's length word read after `reserve`, `0`); `mid` reads that word through `res_ok` (offset `top - 112` is not in `reserve`'s `GrowOut`).
- **`total`'s `RV` at entry**: closed by `rv_closeT` except `ptr + 8 cap ≤ NEXT`, done by hand through the stores (`next_stk`) and, for `log_n > 0`, through the layer's `alloc` (`keep3_1`): `q + 8 = NEXT(m1) ≤ p ≤ NEXT(m3)`.


## Golf

Head: 83344665d3 (one commit on f2bb10fff8: `refactor(formal): move ovf into VecWordT, drop SubspaceRootsT's import of SampleQueriesT`). Skills: lean4:golf and lean4:refactor loaded.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.VecWordT Rv64mc.Proof.Whir.SampleQueriesT Rv64mc.Proof.Whir.SubspaceRootsT Rv64mc.Table.WhirT6b` -> `Build completed successfully (5400 jobs).` It rebuilt all six new modules (`VecWordT` changed, so `ExtRowT`, `SubspaceAtT`, `SampleQueriesT`, `NovelBasisT`, `SubspaceRootsT` and `WhirT6b` were rebuilt too). The log's only warning is the existing `Proof/Field/Reverse.lean` module-system note. All axiom pins pass. `git diff f2bb10fff8 | grep -nE '^\+.*(sorry|admit|native_decide|bv_decide|maxHeartbeats|[—–])'` finds nothing.

### G1. `ovf` moved from `SampleQueriesT` to `VecWordT`; `SubspaceRootsT` no longer imports `SampleQueriesT` (P3-D6's suggested golf)
- **What**: the `ovf` lemma, with its docstring, statement and proof unchanged, now lives in `VecWordT` next to `shl3`. `SampleQueriesT` and `SubspaceRootsT` open it as `VecWordT (vecT_stores shl3 ovf)`. `SubspaceRootsT`'s one use, `SampleQueriesT.ovf hc_2`, becomes `ovf hc_2`, and its `import Rv64mc.Proof.Whir.SampleQueriesT` is removed. `VecWordT`'s header names `ovf`.
- **Why it keeps the meaning**: the lemma's text is unchanged. Only its namespace changes, from `...Whir.SampleQueriesT.ovf` to `...Whir.VecWordT.ovf`. Nothing outside the change referred to it: `grep -rn "SampleQueriesT.ovf"` found only the one use I rewrote. No statement of a contract or `Table` theorem changes. `SubspaceRootsT` used nothing else from `SampleQueriesT`, which the build shows: it compiles without that import. It no longer depends on the hash and transcript modules that `SampleQueriesT` imports.
- **Check**: the build above.

### G2. `Table/WhirT6b.lean`'s header rewrapped
- **What**: one line of the module docstring ended after "Left" and wrapped short. I rewrapped that paragraph to the file's 120-column width. The words are unchanged.
- **Why it keeps the meaning**: it changes only a comment. No line is over 120 columns (`awk 'length>120'` prints nothing).
- **Check**: the build above (`WhirT6b` rebuilt, its five pins pass).

### Considered and not done
- **Sharing `Saved`/`MemOk`/`Saved.keep` across `SampleQueriesT`, `SubspaceAtT`, `ExtRowT`, `NovelBasisT`, `SubspaceRootsT`**: each module saves a different number of registers (13, 12, 5, 11 and 13 slots) at its own offsets. The executor's closers and the explicit `rd`/`tn` steps match each conjunct by its literal address. One generic definition (a list of slots) would change how every part unfolds, which is a refactor of five proofs, not a golf, and could reopen the D7/P2-D6 memory blow-ups. Not done.
- **Generic header-accessor lemma** in place of `ExtRowT.hdr_words`, `NovelBasisT.hdr_eq`, `SubspaceRootsT.hdr` and `hdrL`: their uses rewrite at literal offsets (`top + 18446744073709551512#64`, not `top + c + 8#64`). A generic form would need a normalising step at every use, so it would not be shorter. They already use the upstream `GrowOne.rvCapAt_eq` and `VecHdrT.vecCap_eq`.
- **`NovelBasisT`'s local `ne` alias of `Tactic.ne_of_toNat`**: inlining it lengthens nine `rw` lines past the width limit, with no gain in directness.
- **`SubspaceRootsT.ne_off`**: the same as the existing `DeriveConfigT.ne_off`, but importing `DeriveConfigT` for a one-line lemma costs more than it saves.
- **The shared `tn`/`zlen` local macros**: making them global syntax in `VecWordT` would export `hygiene false` macros to every importer and could collide with other modules' `local macro "tn"`. Not done.

## Amendments, round 1

Head: 7b269c224f (one commit on 83344665d3, comments and notes only). Check after it: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Whir.VecWordT Rv64mc.Proof.Whir.SampleQueriesT Rv64mc.Proof.Whir.SubspaceAtT Rv64mc.Proof.Whir.ExtRowT Rv64mc.Proof.Whir.NovelBasisT Rv64mc.Proof.Whir.SubspaceRootsT Rv64mc.Table.WhirT6b` -> `Build completed successfully (5400 jobs).` (`NovelBasisT` 57 s and `SubspaceRootsT` 82 s rebuilt for their header comments, `WhirT6b` 4.1 s; the only warning is the existing `Proof/Field/Reverse.lean` module-system note).

### R1-1 (stale framing of the defence): fixed here
- This entry supersedes the title, line 3's head, D6's user count and the pass-1 "Invariants of the whole change" counts, which were stale. The earlier entries are not edited.
- Done in the whole change: five functions total with `Table` theorems: `sample_queries` (77), `Subspace::at` (79), `ext_row` (82), `novel_basis` (116), `subspace_roots` (126). Not done: the rest of the WHIR list, the `E::sum` family, `Input::digest`, `is_valid_encoding`, `K::inv`.
- Head: 7b269c224f (83344665d3 before this round).
- D6 corrected: `VecWordT`'s users are five modules, not three: `SampleQueriesT`, `SubspaceAtT`, `ExtRowT`, `NovelBasisT`, `SubspaceRootsT` (`grep -rln VecWordT formal/rv64mc/Rv64mc/` lists those and `VecWordT` itself). This contradicts D6's claim, which was true at pass 1 only.
- Whole-change invariants restated at 7b269c224f: `git diff --stat d067505500..HEAD`: seven new `.lean` files (`ExtRowT` 390, `NovelBasisT` 773, `SampleQueriesT` 611, `SubspaceAtT` 429, `SubspaceRootsT` 987, `VecWordT` 73, `WhirT6b` 123 lines), `notes/total-status.md` (26 lines changed) and `README.md` (4); no existing `.lean` file changed. `git diff d067505500..HEAD | grep -nE '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by|maxHeartbeats|skipKernel|axiom )'` is empty; no em-dash or en-dash added (`grep -c '^+.*[—–]'` over the diff is 0).

### R1-2 (module headers omit "unless it has no capacity"): fixed
- `NovelBasisT.lean` and `SubspaceRootsT.lean` headers now say "its buffer allocated since the entry unless it has no capacity", matching `PostT`'s `vecCap m' a0 = 0#64 ∨ next m ≤ vecPtr` and the `PostT` docstrings; the paragraphs rewrapped at 118 columns.
- Also, the same gap in the status table: rows 116 and 126 said "fresh;" and now say "fresh unless no capacity;", as row 82's already did.

### R1-3 (legend and fold_row obligation stale): fixed
- The legend's `log2 tables (InData)` entry now adds "and the same contents at `sample_queries`' (77) own link (`SampleQueriesT.tables`)". This corrects D10's "no legend entry added" claim: no new entry, but the existing entry had to be widened.
- The `fold_row` (83) obligation now notes that the `ext_row` half is met: "`ext_row`'s does: `ExtRowT.PostT` gives `VecT` of 16-byte elements; 86's is still owed".

### R1-4 (`WhirT6b.subspaceRoots` keeps `MemmoveSpecT` (225) as a hypothesis): deferred, tracked
- No change to the theorem: `memmove`'s total proof belongs to another wave, and the hypothesis is disclosed (legend, row 126, P3), as `RuntimeT.memmove` (228) already has it.
- Tracking added to the `subspace_roots` (126) obligation in `notes/total-status.md`: "`WhirT6b.subspaceRoots` takes `MemmoveSpecT` (225) as a hypothesis, as `RuntimeT.memmove` (228) does: `memmove`'s proof discharges both if it proves `MemmoveSpecT` as stated; a restated contract means re-plumbing both."
- What it would take: when the wave proving `memmove` lands, compose its theorem into `WhirT6b.subspaceRoots` (as `Table/MemT.lean`'s `memcpyT` is composed for `memcpy`) and drop the hypothesis.
