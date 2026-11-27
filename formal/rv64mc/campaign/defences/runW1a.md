# Defence: wave 1a, total contracts of the low layers' class-A functions, Table instances, notes/total-status.md

Base: e8794dc66a. Head: 69304cd4c3 (branch formal/rv64mc-total-w1a, worktree /home/devops/leanEthereum/leanVM-t-comb, 8 commits, not pushed).
Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build <the 29 changed .lean modules>` -> `Build completed successfully (5440 jobs)`, no error, no warning from a new module (every new module was built from cold during the work; the last run replays). Module list: `git diff --name-only e8794dc66a HEAD | grep '\.lean$' | sed 's|formal/rv64mc/||; s|\.lean$||; s|/|.|g'`.

Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

## What is done

Total (template proof in `Proof/**` and `Table` instance in `Table/*T.lean`), new in this wave: `clmul_low` (22), `clmul` (20), `base_mul` (19), `E::mul` (25), `E::sum::<Copied>` (35), `grinding_bits` (50), `bus_grinding_bits` (151), `Layout::committed` (57), `Transcript::finish` (67), `Transcript::next` (111), `whir_queries` (128), `qkeccak_slot` (184), `is_output_lane` (185), drops 68, 73 and 206, `frobenius_8` (136), `Digest::words` (144), the `memcpy`/`memmove` C wrappers (227, 228), `finish_grow` (41). `Table` instances also for the earlier total ones: `halt`, the panic chain (2, 8 to 17), `alloc`, `Input::word`, `memset` (224, 229), `memcmp`, `reduce`, `spread`, `E::square`, `Digest::from_halves`. 42 functions, 868 instructions (`notes/total-status.md`).

## Decisions

### D1. Cherry-picked wave 1b's statement commit 5cd0a65a88 (`Spec/Runtime/MemT.lean`, `Proof/Runtime/MemcpyT.lean`, `MemmoveT.lean`) as 9f641f34ad.
- **Why**: the C wrappers, `finish_grow` and `Digest::words` must call `compiler_builtins`' memcpy/memmove through a total contract whose `Pre` they discharge and whose `Post` (`CopyPostT`) they read. The task says to state them over "a contract of that shape"; 1b had published the exact statements, so the hypotheses are literally `MemcpySpecT`/`MemmoveSpecT`.
- **Rejected**: (a) wrappers generic in `Pre`/`Post`/`Out` (works for the 2-instruction wrappers only: `finish_grow` needs `CopyPreT`'s concrete conjuncts); (b) my own copy of the shape under another name (a merge would then need a bridge lemma).
- **Claims**: the three files are byte-identical to 5cd0a65a88's; I authored none of their content; I created no `MemcpyT.lean`/`MemmoveT.lean` of my own.
- **Evidence**: `git diff 5cd0a65a88 9f641f34ad --stat` against its parent shows the same 3 files; `git show 9f641f34ad --stat`.

### D2. Two recipes, chosen per function.
- Port by `rv_autoT` (copy of the partial proof, the partial `Post`/`Out` stated in the `HoldsT`): `ClmulLowT`, `ClmulT`, `BaseMulT`, `EMulT`, `ESumCopiedT`, `GrindingBitsT`, `BusGrindingBitsT`, `QkeccakSlotT`, `IsOutputLaneT`, `WhirQueriesT`, `Frobenius8T`, `DigestWordsT`, `FinishGrowT`.
- Safety contract (`Post := True`, `Out := True`) by `rv_autoT`, then `HoldsT.of_holds_post` with the partial `ok`: `FinishT`, `NextT`, `CommittedT` (their partial proofs are long frame bookkeeping that a port would redo).
- **Why `DigestWordsT` and `FinishGrowT` are ports, not `of_holds_post`**: their partial `ok` takes the partial `MemcpySpec` (and `AllocSpec`) of callees; `of_holds_post` would leave a partial (class C, unproved) `MemcpySpec` hypothesis in the `Table` theorem, which the task forbids. 1b's `MemT.lean` header also says `CopyPost`'s `ByteFrame` does not hold of the template, so that hypothesis may be false.
- **Claims**: every `of_holds_post` use passes the partial `ok` of the same template and `hpre := fun _ _ h => h.1` (`PreT` is `Pre ∧ ...`).

### D3. Preconditions: `Pre ∧` windows and alignment (`InWin` of `MemsetT.lean`, `x.toNat % 8 = 0`), each under "or empty" where a pointer can dangle.
- `ESumCopiedT.PreT`: `es.length = 0 ∨ (InWin x10 (16 len) ∧ x10 % 8 = 0)`.
- `FinishT.PreT`: transcript `InWin x10 360`, aligned; proof (`m.getMem (x10 + 0x148#64)`) `InWin 48`, aligned.
- `NextT.PreT`: transcript `x11`, result slot `x10` (24), proof, each `InWin` and aligned; `StreamWin`: stream length 0 or its buffer `InWin (16 len)` and aligned.
- `CommittedT.PreT`: slice `x12 = 0 ∨ (InWin x11 (24 len) ∧ aligned)`; slot `InWin x10 24`, aligned.
- `DigestWordsT.PreT`: slot `InWin x10 32`; digest `inWindow x11 32` and `OffStack x2 x11 32` (exactly `CopyPreT`'s source conjuncts; the source may be static data).
- `FinishGrowPreT`: slot `InWin x10 24`, aligned; `x11 = 0 ∨ 0x10000000 ≤ x12` (old block's lower bound, the one `CopyPreT` fact not derivable from `FinishGrowPre`'s `Live`).
- `Frobenius8T`, `BusGrindingBitsT`: the partial `Pre` unchanged; all others `True`.
- **Why** the windows' facts are stated on the exact address terms the code computes (`m.getMem (x10 + 0x148#64)`, not `proofAddr`), so `rv_autoT`'s `omega` closer matches atoms; alignment is redundant with `TranscriptAt.sponge.aligned` for the transcript but harmless.
- **Rejected**: an `InWin`-free precondition with bounds derived from `Live` (no lower bound on heap pointers exists anywhere, `notes/total-correctness.md` says so).
- **Claims (non-vacuity, call sites in `Gen/Tmpl`)**: each conjunct is discharged at the image's call sites by these facts, which the callers' own total proofs will have to carry:
  - stack objects (`Walk`'s transcript `sp + 0x98` for `finish`, `Walk`'s slot `sp + 0x2c0` for `committed`, `grow_amortized`'s slot `sp + 0` for `finish_grow`, `Sponge::new`/`Digest::halves`' slot `sp + 0` for `Digest::words`, `NextScalar`/`GrindCheck`'s result slots, transcripts in callers' frames, `main`'s `Proof`): `InWin`'s stack disjunct from `stackLimit ≤ top ≤ sp + k` and `+ n ≤` the initial stack top `≤ 0xc0000000` (`Windows.top_le`); alignment from `sp` 16-aligned and 8-multiple offsets;
  - heap buffers (`Vec<E>` slices given to `E::sum` from `x21` in `SumcheckRoundPoly`, the stream, the placements, `finish_grow`'s old block): a block `alloc` returned lies at or above `NEXT` at that time, `≥ 0x10000000` (`Windows.next_ge`), ends `≤ NEXT ≤ heapEnd`, and is 8-aligned (`AllocPost`, seen as `hret2_17` in `FinishGrowT`); the input's words from `inputBase = 0x10000000`; empty vectors take the `= 0` disjunct;
  - `Digest::words`' source: a digest in a caller's frame (stack window, `≥ sp`) or a heap object (heap window, below `stackLimit`), or a static constant (`inWindow` from `Windows.data_ok` if all four words are in `env.data`, see Known risks).
  I checked the call sites named above in the templates (`Verifier/Walk.lean`, `Alloc/RawVec/RawVecInner/GrowAmortized.lean`, `Verifier/Transcript/Sponge/New.lean`, `Verifier/Hash/Digest/Halves.lean`, `Verifier/Transcript/Transcript/SumcheckRoundPoly.lean`); I did not prove any of these discharges (no caller is total yet).

### D4. `ClmulLowT.total` takes `DataRef.InData env [(L.d_c8_d07a1b83, d_c8_d07a1b83_words)]` instead of the partial's `DataRef.Words`.
- **Why**: the total proof needs the load's address in a window and aligned, which only membership in `env.data` gives (`Windows.data_ok`); `DataRef.Words` is a statement about every `Static` memory and does not imply membership. `InData` gives both (`InData.words`).
- **Claims**: it is an environment fact of the same kind as `Table/Whir.lean`'s `InData` hypothesis; `FieldT.ClmulTable` is its name at the image. Not discharged here (the partial `Table/Field.lean` leaves `DataRef.Words` open too).

### D5. `Proof/Runtime/WinT.lean`: shared lemmas; two of them declared as `_root_.Rv64mc.Proof.Runtime.MemsetT.InWin.dword` and `.ne_next`.
- **Why**: dot notation on an `InWin` hypothesis (`hS.dword`) resolves in `MemsetT.InWin`'s namespace; `MemsetT.lean` is an existing file I did not edit.
- **Rejected**: editing `MemsetT.lean` (an existing module); a new predicate (would break the shared `InWin` vocabulary with 1b's `CopyPreT`).
- **Claims**: no existing declaration is shadowed (`MemsetT.InWin.dword`/`ne_next` did not exist at base: `git grep -n "InWin.dword\|InWin.ne_next" e8794dc66a` is empty).

### D6. `FinishGrowT`: `Stop := AbortStop`, `alloc`'s `AllocStop` weakened by `HoldsT.mono_stop` (`h.1`); `set_option maxHeartbeats 2000000 in` kept.
- **Why**: the stop set the campaign standardises on. The budget is the partial proof's (`FinishGrow.lean` has the same line); without it the build fails with `(deterministic) timeout at whnf, maximum number of heartbeats (200000)` at the theorem (measured once, then restored).
- **Claims**: the proof is the partial proof's text with `rv_auto`/`rv_sym` replaced by `rv_autoT`/`rv_symT`, the four alloc-null goals gone (the executor closes them), one `exact Nat.le_refl _` removed (the `rw` closes it), and one new goal, `CopyPreT`'s windows, closed by `omega` from `Windows`, `hret2_14` (`alloc`'s frame), `hlive` and `FinishGrowPreT`'s new conjunct.

### D7. `Table/*T.lean` naming: `RuntimeT`, `FieldT`, `TranscriptT`, `BusT`, `LayoutLeafT`, `WhirT`, `DigestT`.
- **Why**: 1b owns `MemT.lean`, `HashT.lean` and may write `LayoutT.lean`; `FieldT.lean` is mine per 1b's task text. `Digest::from_halves`/`words` therefore went to `DigestT`, not `HashT`.
- **Claims**: each `Table` theorem has its own `#guard_msgs in #print axioms` block pinning `[propext, Classical.choice, Quot.sound]` (42 blocks, 42 theorems: `grep -c "^theorem" Rv64mc/Table/*T.lean` vs `grep -c "^#print axioms" Rv64mc/Table/*T.lean`). Open hypotheses are only: `hnext`/`hend` (alloc's environment facts, as `Table/Runtime.lean`), `FieldT.ClmulTable`, `WhirT`'s `InData` of `WHIR_QUERIES`' tables, and `MemcpySpecT`/`MemmoveSpecT` at `Idx.CompilerBuiltins.Mem.Memcpy`/`Memmove`.
- `WhirT.whirQueries` imports `Table/Whir.lean` for its data lemma `whirQueriesTable` (a fact about `env.data`, not a partial contract).

### D8. `notes/total-status.md` generated by a script (`runW1a/gen_status.py`, from `cg.json` and `waves.md`), not committed.
- **Claims**: its counts reproduce from the file itself: `awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `42 868`; with `&& $10 ~ /none/` -> `32 460`; `$2 ~ /^ [0-9]+ $/` -> `229 20878`; `$7 ~ /stated/` -> `2 395`; `$7 ~ / no /` -> `185 19615`. The "only environment facts open" row (38, 795) counts `none`, `env`, `clmul table` and `WHIR query tables` rows.

## Invariants of the whole change
- No existing file changed but `README.md`: `git diff --diff-filter=M --name-only e8794dc66a HEAD` -> `formal/rv64mc/README.md` only; every other path is added (31 files, 2152 insertions, 4 deletions, all in README).
- No `sorry`/`admit`/`native_decide`/`bv_decide`/`implemented_by`/`axiom` added: `git diff e8794dc66a HEAD | grep -cE '^\+.*(sorry|admit|native_decide|bv_decide|implemented_by|^\+axiom)'` -> `0`.
- One raised heartbeat budget (D6): `git diff e8794dc66a HEAD | grep -E '^\+.*maxHeartbeats'` -> one line.
- No em or en dash in changed files (grep for U+2013/U+2014 over them is empty).
- Every new `total`/`Table` theorem is axiom-pinned in its module (Proof modules: all `total`s except `DropT`'s three and `WinT`'s lemmas; Table modules: all).

## Not done
- `Input::digest` (5): draft in `runW1a/InputDigestT.draft.lean` (safety plus `DigestOut` frame, `Post` "the reader still satisfies `WordPreT`", `ReaderT.next` lemma). The symbolic run (4 calls, 32 byte stores, heap on) needs a 4M heartbeat budget, and six goals remain: `Input::word`'s `WordPreT` at calls 1 to 4 (rebuilt from the previous call's `WordPost` through the frame's stack stores) and the return address read back. Deleted from the tree, with the failed build's own artifacts under `.lake/build/.../InputDigestT.*` (`rm -f`, nothing else under `.lake` touched).
- Drops 69, 71, 72 (loops): need a representation precondition. 69 and 72 read each element's two words (needing the element slice `InWin` and aligned, a `Total.loop` with the elements left as measure); 71 passes each `Table`'s two inner `Vec<Vec<Form>>` slices to 69, so its `Pre` must state every element's inner slices in windows, and memory read after 69's calls must be kept (69's frame allows `[NEXT, NEXT')`, so heap objects need `Live`). Not started.
- `try_allocate_in` (3, 37): class C, a loop and `alloc`/`memset` calls; not started.
- `E::sum::<Chain>`, `xor_block`, `keccak_f`, `keccak_cell_lanes`, memcpy/memmove proofs: wave 1b's.
- No caller-side proof that the new `Pre`s hold (D3 is an argument from the templates, not a theorem).

## Known risks
- **Vacuity at call sites (D3)**: the heap lower bound `0x10000000 ≤ ptr` for vectors relies on every heap object coming from `alloc` or the input; a pointer into static data with nonzero length passed as an `E` slice or a stream buffer would make `ESumCopiedT`/`NextT` unusable there (InWin excludes the static data). I did not find one, but I checked only the call sites listed in D3, not every path that builds those vectors.
- `DigestWordsT`'s `inWindow x11 32` for a digest that is a static constant (e.g. an IV) is dischargeable only if all four of its words are in `env.data`; `env.data` lists the tables templates reference, which may not include it. Look at `Transcript::new`'s argument to `Sponge::new`.
- `FinishGrowT`'s `x11 = 0 ∨ 0x10000000 ≤ x12`: a vector whose capacity is nonzero but whose buffer is not from `alloc` would break it; all `grow_*` paths allocate.
- `FinishT`/`NextT` state window facts on `m.getMem (x + 0x148#64)` while `TranscriptAt` speaks of `proofAddr`; they are the same word, but a caller must prove the literal form.
- D1 couples this branch to 1b's statements: if 1b amends 5cd0a65a88, the merge conflicts in the three files and `MemWrappersT`, `FinishGrowT`, `DigestWordsT`, `RuntimeT`, `DigestT` must follow.
- `ESumCopiedT`'s loop and `Frobenius8T`'s loop are `Total.loop` with `LoopInv` defined by `Inv` at `len - 1 - k`; the measure is `k` (elements or squarings left), decreasing by one per back edge (`ih k` at `k + 1`).

## Golf

Commit 919edfb5a4 on 69304cd4c3 (5 files, +40 -33). No statement of an existing or a wave-1a declaration changed; only proofs, plus three new lemmas in `WinT.lean`. Skills: lean4:golf and lean4:refactor loaded.

### G1. `WinT.lean`: three new lemmas, `MemsetT.InWin.lt`, `.dword_add`, `.ne_next_add` (declared in `MemsetT.InWin`'s namespace for dot notation, as D5's two).
- `InWin.lt`: `q.toNat + n < 2 ^ 64`, the bound every `by unfold InWin at hS; omega` in the change derived inline.
- `InWin.dword_add`: `InWin.dword` at `x + k` from `x.toNat = q.toNat + o`; its proof is exactly the `toNat_add_ofNat ... |>.trans ... |>.trans Nat.add_assoc` chain `NextT` and `CommittedT` wrote at each use.
- `InWin.ne_next_add`: `InWin.ne_next` at `q + o` for `o < n`; its proof is exactly the `(by rw [toNat_add_ofNat (by omega)]; omega)` pair written at each use.
- **Why equivalent**: each lemma's body is the inlined text it replaces, abstracted over the offset; the call sites now instantiate it (`k := 8`, `16`, `o` by unification with the goal), and the resulting hypothesis types are the same terms (`x + BitVec.ofNat 64 k`, which is what `8#64` elaborates to), so the `exact hd8.1`-style closers are unchanged.
- Also wrapped D5's two declarations to the 120-column limit (signature text unchanged).
- **Claims**: no clash with the sibling worktrees: `grep -rln "InWin\.\(lt\|dword_add\|ne_next_add\)\b" leanVM-t*/formal/rv64mc/Rv64mc` finds only `WinT.lean`.

### G2. `NextT.safe`, `CommittedT.safe`: use G1.
- `n8`/`n16` become `hW.ne_next_add (by omega)`; `hd8`/`hd16` become `hS.dword_add ... (k := 8|16) (by omega) (by omega)`; `NextT`'s unused-after-golf `hx8` removed; the `elem_toNat` side conditions use `hS.lt` instead of unfolding `InWin`.
- `NextT`'s last frame chain: the `|> fun h => frame_true_setMem h n8` tail folded into the nested application (same four `frame_true_setMem` steps in the same order, same `ne` arguments).
- **Why equivalent**: same proof terms up to the lemma abstraction of G1; theorem statements untouched.

### G3. `ESumCopiedT.total`: two pairs of identical bullets become `all_goals`.
- Inside the `succ` branch after `rv_closeT`, the two `rw [← body_val (j := j) ...]` goals; after the `cases`, the two `rw [← acc_len, ...]` goals. In both places these are exactly the remaining goals of their block (the bullet before them is the only other), so `all_goals` runs the same tactic on the same goals.

### G4. `FinishGrowT.total`: removed `all_goals simp only [Layouts.ResultBlockTryReserve.byteSize] at *; have hW : InWin env (regs .x10) 24 := hpre_14`.
- **Why equivalent**: `hW` was never referenced (`grep -n hW` after the block found only its definition), and no tactic in `Tactic/` matches `InWin` (`grep -n InWin Rv64mc/Tactic/*.lean` is empty), so neither a closer nor `omega` could use it; the `simp` only served it (the partial proof `FinishGrow.lean` runs the same subsequent text without it). The port is now closer to the partial proof's text (D6's claim still holds, with this block no longer among the differences).
- `maxHeartbeats 2000000` left as it was.

### Check
- `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Runtime.WinT Rv64mc.Proof.Field.ESumCopiedT Rv64mc.Proof.Transcript.NextT Rv64mc.Proof.Layout.CommittedT` -> `Build completed successfully (4475 jobs).` (oleans rebuilt, timestamps checked).
- `... lake build Rv64mc.Proof.Runtime.FinishGrowT` -> `Build completed successfully (4423 jobs).`
- All 29 changed modules (`git diff --name-only e8794dc66a | grep '\.lean$' | ...`) -> `Build completed successfully (5440 jobs).`; the only warning printed is the pre-existing `Proof/Field/Reverse.lean` module-system import note; no warning or error from the five golfed modules (unfiltered output grepped for `warn|error`).
- No sorry/admit/native_decide/axiom added; no em or en dash in the touched files; the `#guard_msgs` axiom pins of `NextT.total`, `CommittedT.total`, `ESumCopiedT.total`, `FinishGrowT.total` still pass (part of the build).

### Considered, not done
- `Table/*T.lean`: already one term per theorem; `BusT` inlines `GrindingBitsT.total` rather than citing `TranscriptT.grindingBits` because the tail call needs `grinding_bits` at `bus_grinding_bits`' stack bound, not its own.
- `MemWrappersT`'s two theorems share a shape but each is three short `simpa`s; a helper would not be shorter.
- The ported proofs (`FinishGrowT`'s `hn8`/`hin8` arithmetic, `Frobenius8T`, `GrindingBitsT`, `DigestWordsT`) kept as the partial proofs' text, so a reader can diff port against partial.

## Amendments, round 1

Head after this round: `1691c4c658`.

### R1-1 (D5's rejected alternative): fixed in the defence; header deferred to wave 1b.
- The reviewer is right: `CopyPreT` (`Spec/Runtime/MemT.lean:36-41`) inlines the heap-or-stack disjunction and does not use `InWin`, so D5's stated reason was wrong. This contradicts D5's "**Rejected**: ... a new predicate (would break the shared `InWin` vocabulary with 1b's `CopyPreT`)". Corrected reason: a new predicate would split the vocabulary from `MemsetT.InWin`, which `MemsetPreT` (existing, `Proof/Runtime/MemsetT.lean:38`) already states its windows with; the shared lemmas of `WinT.lean` apply to `MemsetT`'s hypotheses and the new ones alike.
- `MemT.lean`'s header lists `InWin` under "Main definitions" (line 19) and names it at line 13, but the file defines none (`git grep -n "def InWin" -- formal/rv64mc` -> only `Proof/Runtime/MemsetT.lean:38`). Not edited here: `MemT.lean` is wave 1b's file cherry-picked from `5cd0a65a88`, and editing it on this branch would conflict with 1b's copy. Note for wave 1b: drop `InWin` from `MemT.lean`'s "Main definitions" and either say "the heap or stack window (as `MemsetT.InWin`)" at line 13 or restate `CopyPreT` with `MemsetT.InWin`.

### R1-2 (D3's call sites of `E::sum::<Copied>`): fixed in the defence.
- `ESumCopiedT`'s second caller is `VerifyLayer`, twice (`Gen/Tmpl/Verifier/Keccak/VerifyLayer.lean:372` at `base + 0x224`, `:466` at `base + 0x2e0`). D3's list omitted it.
- Call 1 (`:372`): `x10 := [x18 + 8]`, `x11 := x10 + ([x18 + 16] << 4)`, the `ptr`/`len` of `claim.mu` (`crates/verifier/src/keccak.rs:151`). Call 2 (`:466`): `x10 := [sp + 0x48]`, `x11 := x10 + ([sp + 0x50] << 4)`, the local `mu` (`keccak.rs:160-161`).
- What discharges `PreT` there: `claim.mu` is built only at `keccak.rs:270` (`eq_kernel(..)`, a `vec![ZERO; 1 << n]`) and `:199` (`instance_weights(s)`'s `.collect()`), the local `mu` at `:160` (`instance_weights`); `grep -n "\bmu\b" crates/verifier/src/keccak.rs` shows no other construction. All are `Vec<E>` from `alloc`, so D3's heap-buffer argument applies: `0x10000000 ≤ ptr` and `ptr + 16 len ≤ NEXT ≤ heapEnd` (`Windows.next_ge`, `AllocPost`), 8-aligned, or the `es.length = 0` disjunct. As in D3, this is an argument from the templates and the Rust, not a proof.
- D3's "I checked the call sites named above" should read with `Verifier/Keccak/VerifyLayer.lean` added; Risks' vacuity entry stands (no static-data `E` slice found at either call).

### R1-3 (Invariants' diff counts): fixed in the defence.
- The line gave `69304cd4c3`'s numbers. At `919edfb5a4`: `git diff --shortstat e8794dc66a 919edfb5a4` -> `31 files changed, 2159 insertions(+), 4 deletions(-)`. At the new head `1691c4c658` (R1-4 adds a line): `git diff --shortstat e8794dc66a HEAD` -> `31 files changed, 2160 insertions(+), 4 deletions(-)`. The rest of the claim reproduces: `git diff --numstat e8794dc66a HEAD | awk '$2>0'` -> only `4 4 formal/rv64mc/README.md`; `git diff --diff-filter=M --name-only e8794dc66a HEAD` -> `formal/rv64mc/README.md` only.

### R1-4 (`RuntimeT.lean:152` at 122 columns): fixed, `1691c4c658`.
- Broke `partialDropForm`'s term after `env _ _ _`; text otherwise unchanged.
- Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Table.RuntimeT` -> `✔ [4935/4936] Built Rv64mc.Table.RuntimeT (3.7s)`, `Build completed successfully (4936 jobs).`
- `awk 'length > 120'` over the added `.lean` files now hits only `Proof/Runtime/MemWrappersT.lean:50` (121), the `#guard_msgs` info line the reviewer already excused (its text must match the message verbatim).
