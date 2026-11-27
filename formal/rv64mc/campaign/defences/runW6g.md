# Defence: wave 6g, first pass: a `FlushesFormT` move lemma (`FlushesMoveT`), `Flushes::memory` (197), `Flushes::memory_if` (210), SUMARR_TITLE; a finding against the `Flushes` builders' postconditions (what `tables` (175) needs); everything else on the list not done

Base: 0152cc78ad. Head: HEAD_COMMIT (commits COMMITS).
Check: CHECK_LINE

Skills loaded: lean4:prove, lean4:refactor, writing-lean-proofs (all three available; I followed their no-statement-change and verify-mechanically rules, not their interactive prompts, since this is a scripted pass).

Total functions after this pass: COUNT_LINE. Summary counts left to the merge, as asked.

## Decisions

### D1. `Proof/Layout/FlushesMoveT.lean`: `FFoot`, `FFoot.lt`, `elems_move`, `move`, `move_below`
- **Why**: deliverable 1 (wave 6e's "Not done": every `flushes_*` builder returns its `Flushes` by copying 48 bytes into `sret`, and `tables` copies each into frame slots and then into a `Table`).
- **What**: `FFoot m a x` is the footprint of the `Flushes` at `a`: either buffer to its capacity (`[lo, hi)`, the same bounds `PairFormT.HeldT` uses) or an element's `ExtendTrustedT.InFoot`. `move`: from `FlushesFormT env m a`, `NEXT` no lower, `d` in a window (`InWin env d 48`) and 8-aligned, the six words at `d` in `M` equal to those at `a` in `m`, and `M` agreeing with `m` on `FFoot m a`, it gives `FlushesFormT env M d`, `FFoot M d ⊆ FFoot m a`, and the four `lo`/`hi` equalities. `move_below` is the corollary with "agreeing below `NEXT`" (`FFoot.lt`).
- **Why the footprint form of `hf`** (rejected: only "agreeing below `NEXT`", as `StateDerivedT.FlushesFormT.keep` has): `tables`' last copies go into a heap block below `NEXT` (the `Vec<Table>` buffer), so the below-`NEXT` form cannot be used there; the footprint form is what a heap destination needs. The conclusion `FFoot M d ⊆ FFoot m a` lets a caller keep chaining moves.
- **Why capacity, not length, for the buffers in `FFoot`**: a pushed element lands in the old capacity's spare slot when the buffer is kept; with capacity bounds a footprint monotonicity across `pair` holds (see D4); `lo`/`hi` already use capacity.
- **Claims**: no statement of an existing module changed; `move` uses only `CloneFormsT.vecT_copy`, `VecFormT.keep'` (existing).
- **Unused yet**: no proof in this pass calls `move` or `move_below` (no builder that copies a `Flushes` was finished). They are stated for the `flushes_*` builders and `tables`.

### D2. `Flushes::memory` (197): `Proof/Layout/MemoryT.lean`, `Table/FlushesT6g.memory`
- **Contract**: `PreT` = `self` (`a0`) `PairT.FlushesT` at the stack pointer, 8-aligned, `FlushesFormT`; `address` (`a1`) `StackObj` and `FormT`; `values` (`a3`) `ConcatFormT.SliceFT ... 2#64`. `PostT` = `StateDerivedT.PostT` (what `counted` gives), `Out = PairT.OutT`, `Stop = AbortStop`. Safety only (class D, no partial proof).
- **Why this Pre**: it is `CountedT.PreT` minus what `memory` builds itself: `counted`'s `a` is memory's frame array `[constant(SEP_MEM), address]`, its `form` is `col(count, 1)` in memory's frame, its `b` is `(values, 2)`. `address` must be a frame object (`StackObj`) because `memory` reads it *after* `constant` runs (template steps 15 to 17 after the call at 14); a header below the stack pointer could be clobbered, below `NEXT` or at/above the stack pointer it is kept.
- **Call-site check of this Pre** (`sites2.py memory`, cg.json callers 187, 188, 190, 196): `self`, `address`, `values` are frame slots of the caller at 188 (`sp+8`, `sp+0x140`, `sp+0x50`), 190 (`sp+0x30`, `sp+0x120`, `sp`), 187 (`sp+0x30`, `sp+0x448`, `sp+0x400`); at 196 they are `memory_cols`' own `a0`, `a1` and its frame `sp`. Argued, not proved (none of those callers is done). New obligation entry in `notes/total-status.md`.
- **Callee Pres discharged at the call** (earlier obligation "bytecode (195), memory (197), memory_if (210) call counted"): `cnt_pre` proves `CountedT.PreT` at template step 33: `FlushesFormT` kept (`StateDerivedT.FlushesFormT.keep`), the prefix slice at the frame (`constant`'s `Form` by `TermAlT.formT_of` kept across the copy and `col` by `FormT.keep`; `address`'s header moved by `StateDerivedT.FormT.move`, its terms below `NEXT` kept), `form` `col`'s (`formT_of`), `b` by `CountedT.SliceFT.keep`. `constant`'s and `col`'s preconditions were closed by the executor. The obligation entry now says "For 197 and 210 this is proved".
- **`constant`'s value**: the code passes limbs `(2, 0)`; I use `hconst (Model.ofLimbsW (2#64, 0#64))`. `2 : E` would be wrong (characteristic 2). The limbs goal is closed by the executor's own simp (no `limbs_ofLimbsW` rewrite was needed; I tried one and the unused-tactic linter fired, so I removed it).
- **Post's use by callers**: `memory`'s callers (`memory_cols`, the `flushes_*`) treat it as they treat `counted`/`state_step`: `FlushesFormT` to call the next builder step, `KeptOrFresh` and the lengths as before. See D4 for what this post does not give.
- **Engineering**: `counted`'s pre/post sealed (`KPre`, `KPost`) and own pre sealed (`PreS`), as in `StateStepT`. `chain` is the copy's store chain as a definition; `frame2` composes the frame up to `counted`'s call. No `maxHeartbeats`.

### D3. `Flushes::memory_if` (210): `Proof/Layout/MemoryIfT.lean`, `Table/FlushesT6g.memoryIf`
- **Contract**: `MemoryT`'s with arguments one register later (`address` `a2`, `values` `a4`), same `PostT` (`StateDerivedT.PostT`), `Out` and `Stop`.
- **Call site** (cg.json: only 187): `flushes_keccak` step 251, `self = sp+0x30`, `address = sp+0x448`, `values = sp+0x400`: frame slots. Argued.
- **The two `add` calls** (earlier obligation entry for 193's sites; these are two of the fourteen): `add_pre` proves `FormAddT.PreT` from `self` a `FormT` whose whole block (to capacity) ends by some `N`, and `other`'s `Form` whose block starts from `N`. `self` is `col`'s result (first add) or the first sum (second add); `other` is a `prod` allocated after it. `Fresh40 M a lo hi` records a `Form`'s whole block in `[lo, hi)` (or capacity 0); `add_res` derives it for `add`'s result from `FormAddT.PostT`'s "kept or fresh" (when kept, the block is `self`'s, fresh since the entry). Both sites proved (`at2`, `at4`); the obligation entry for 193 says so.
- **`add`'s Out includes `self`'s buffer** (a heap block): the frame composition (`hF.trans`) needs it inside `MayWrite top F m _`: it is `[next m, next M')` because `self`'s block is fresh since the entry (`Fresh40`), `add_out`.
- **`counted`'s Pre** at step 59: `cnt_pre` (prefix `[constant, address copy]` at `sp+0x30`, `form` the second sum at `sp+0x18`).
- **Engineering (a reviewer may question)**: first attempt kept all the reasoning inside `total` after `rv_autoT`; it timed out (200000 heartbeats at `whnf`). The fix moved every arithmetic step into lemmas with small contexts (`at2`, `at4`, `at6`, `cnt_pre`, `saved_read`, `post`, `saved_frame`, `chain_frame`), so `total` only applies them. One executor run over the whole body (seven calls). `exact cnt_pre ... rfl ...` hit `maxRecDepth` (the 6e pitfall); `refine ... ?_` then `all_goals rfl` works. No `maxHeartbeats` raised.

SUMARR_ENTRY

### D4. Finding: the `Flushes` builders' postconditions do not give what `tables` (175) needs
- **Checked as the task asks** ("each Flushes builder's result against tables (175)"). `tables` allocates the `Vec<Table>` buffer (`x9 = alloc(480)`, template instruction 57) after `flushes_keccak` but before `flushes_arith` (twice), `flushes_set`, `flushes_deref`, `flushes_jump`; at the end it `memcpy`s each 72-byte `Table` (its `Flushes` at `+0x18`) into that buffer (instructions 169 to 202). For each `Flushes` copied earlier to stay `FlushesFormT` (D1's `move`, `hf`), every builder result's footprint must avoid that buffer. `FlushesFormT` says the footprint is below `NEXT` and apart from the `Flushes`' own buffers only; the buffer `x9` is below `NEXT` at the builders' entries, so nothing in the current posts excludes a footprint word inside it.
- **What would fix it**: builders' posts with "the result's `FFoot` lies at or above `NEXT` at entry" (true: each starts from `Flushes::default()`), which needs a footprint monotonicity (`FFoot m' self x → FFoot m self x ∨ next m ≤ x`; for `state_derived` also `npc`'s/`nfp`'s terms) of `pair`, `state_derived`, `state_step`, `counted`, `memory`, `memory_if`, `bytecode`, `memory_cols`. `pair`'s follows from `PairT.PostT` alone; `state_derived`'s and `counted`'s need new proofs of their last parts (`fin`) because `StateDerivedT.PostT` drops the pushed vectors' freshness (`NewV`, `held3`) that their proofs have at `pair`'s call. `CountedT.mid` and `StateDerivedT.mid` take their continuation as a hypothesis, so only `fin` and `total` would be re-run.
- **What I did**: recorded it as an obligation (`notes/total-status.md`, "Obligations", the `tables` entry) and under "Owed by contracts already total". I kept `MemoryT`/`MemoryIfT`'s posts equal to `counted`'s (`StateDerivedT.PostT`), since a stronger post cannot be derived from `counted`'s current one. When the second contracts exist, `memory` and `memory_if` need second contracts too (their proofs are post-agnostic up to `post`, which forwards `counted`'s).
- **Rejected**: (a) giving `memory`/`memory_if` a fresh-footprint post now: not provable from `CountedT.SpecT`. (b) Re-proving `state_derived`, `state_step`, `counted` with the stronger post in this pass: a 1000-line and a 630-line module's `fin` and `total`; I judged it would have consumed the pass (it is the next thing I would do). (c) Ignoring it: `tables` would then be unprovable with these posts, and the task names this check explicitly.

## Invariants of the whole change
- Only new Lean files plus README and notes: `git diff --name-status 0152cc78ad HEAD` lists `A` for NEWFILES and `M` for `formal/rv64mc/README.md`, `formal/rv64mc/notes/total-status.md`.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `maxHeartbeats`: `git diff 0152cc78ad HEAD -- '*.lean' | grep -cE '^\+.*\b(sorry|admit|native_decide|bv_decide|implemented_by|maxHeartbeats)\b|^\+axiom'` -> `0`.
- IRREDUCIBLE_LINE
- `#guard_msgs in #print axioms` pinning `[propext, Classical.choice, Quot.sound]` on `FlushesMoveT.move`, `MemoryT.total`, `MemoryIfT.total`, SUMARR_PINS `FlushesT6g.memory`, `FlushesT6g.memoryIf`.
- No em or en dash added: `git diff 0152cc78ad HEAD | grep "^+" | grep -c "—\|–"` -> `0`.
- Open hypotheses of the new `Table` theorems: `memory`, `memoryIf`: env; clmul table; `Vec<Form> spec_extend bound (InData)`, `[&[Form]] concat bound (InData)` (all through `counted`, as `FlushesT6e.counted` has them; all already in the legend). SUMARR_TABLE No new environment fact.
- `Tactic/`, `Gen/`, every existing `.lean` file untouched.

## Not done (in list order)
- **`bytecode` (195)**: not started. Shape read: `alloc(24 (1 + len))`, two `Vec<Form>::spec_extend`s into it (`SpecExtendFormT`, one source the 24-byte block `constant` filled, one the argument vector), a drop, `gpow`, `col`, `counted`. Every callee is total; the obstacle is volume only.
- **`memory_cols` (196)**: not started. Shape read: it loads `columns[0]` without a length check (the callers pass lengths 1 or 2), so its `Pre` must ask `1 ≤ len` and the words readable; it moves `Form` headers through several frame slots before calling `memory`. Every callee is total.
- **The `Form::sum` family**: SUMARR_NOTDONE `207` (a loop over a mapped iterator with `prod`), `211` (a flattening loop with `memcpy`), `203` (a chain of two array iterators with `memcpy` and a partial drop): not started.
- **`layout_limb` (209)** (needs 211), the `flushes_*` (187 to 191), `tables` (175), `build_layout` (45), `group_by_word` (218), `StackWeight::evaluate` (99), `ColumnClaim::on_stack` (130): not started. `tables` is additionally blocked by D4. `flushes_jump`'s discharge of 6e's argued `TermsApart` (the empty `Flushes`) is therefore not proved yet.
- `notes/total-status.md` summary counts: left to the merge.

## Known risks (where to look hardest)
- **D4 is a claim about `tables`' template that I checked by reading it, not by a proof.** The instruction indices are from `Gen/Tmpl/Verifier/Layout/Tables.lean` (counting non-label instructions). If the reviewer finds a reason the footprints are apart from `x9` with the current posts, D4's owed item is moot.
- **`MemoryT.PreT`/`MemoryIfT.PreT`'s `StackObj` of `address`**: argued at all five image sites (frame slots, or `memory_cols`' argument), not proved. A heap `address` would make the contract vacuous there.
- **`SliceFT` of `values`**: argued (frame arrays at every site), as for `counted`'s `b`.
- **`FlushesMoveT` is unused** in this pass (D1); its hypotheses were designed for `tables`' heap copy, but no proof has exercised them yet.
- **Sealed aliases**: `MemoryT.PreS`, `KPre`, `KPost`, `MemoryIfT.PreS`, `APre`, `APost`SUMARR_SEALED, each a definitional alias of an existing pre/post, unfolded only where proved or applied.
