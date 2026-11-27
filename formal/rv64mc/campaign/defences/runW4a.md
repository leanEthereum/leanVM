# Defence: wave 4a, first pass: `Vec<E>::spec_extend` (106), `Vec<E>`'s `spec_from_iter_nested` for `verify_layer` (143) and `<[usize; 2]>::try_map` for `verify_bus_balance` (153) total with `Table` instances; the rest of the list not reached

Base: 0e6127ec04. Head: 6c359dedac after pass 3 (93c96cc5f3 after pass 2, 6327fe3b80 after pass 1; branch formal/rv64mc-total-w4a, worktree /home/devops/leanEthereum/leanVM-t-comb, 9 commits, not pushed). Not done after pass 3: see the pass 3 section, "Not done (pass 3)" (pass 2's list less 102, 53 and 36).

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Runtime.SpecExtendT Rv64mc.Proof.Runtime.FromIterET Rv64mc.Proof.Bus.TryMapT Rv64mc.Table.BuildT` -> `Build completed successfully (5190 jobs).` (6 s, all replayed; output in runW4a/scratch/final.txt). Each module was built by the same command when it was added: SpecExtendT 81 s, FromIterET 165 s, TryMapT 92 s, BuildT 3 to 5 s. The output carries two lines that are not errors: the pre-existing `Reverse.lean` module-system note, and `info: Rv64mc/Proof/Bus/TryMapT.lean:122:0: PANIC at Lean.Expr.appArg! ... application expected` (see Known risks, R1).

Skills: lean4:prove, lean4:refactor and writing-lean-proofs loaded.

## What is done

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 106 | `<Vec<E> as SpecExtend<&E, Iter<E>>>::spec_extend` | `SpecExtendT.SpecT` (`AbortStop`) | Proof/Runtime/SpecExtendT | BuildT.specExtendE | env |
| 143 | `<Vec<E> as SpecFromIterNested<E, Map<Range, verify_layer::{closure#5}>>>::from_iter` | `FromIterET.SpecT` (`AbortStop`) | Proof/Runtime/FromIterET | BuildT.fromIterE | env; clmul table |
| 153 | `<[usize; 2]>::try_map` (`verify_bus_balance`'s claims) | `Bus.TryMapT.SpecT` (`AbortStop`) | Proof/Bus/TryMapT | BuildT.tryMapClaims | env |

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `107 4057` (104, 3803 at base). The summary table is left to the merge.

## Decisions

### D1. `SpecExtendT.SpecT`: `PreT`, `PostT`, `OutT` for `spec_extend` (no partial spec: class D)
- **Pre**: `VecT env m a0 16 ∧ env.Owned m sp a0 24 ∧ HdrApart m a0 16 ∧ a1 ≤ a2 ∧ (a2 - a1) % 16 = 0 ∧ SrcT env m sp a0 a1 (a2 - a1)`. `HdrApart`: capacity `0`, or the header's 24 bytes apart from `[ptr, ptr + 16 cap)`. `SrcT`: no bytes, or `inWindow a1 n`, `OffStack env sp a1 n`, `a1 + n ≤ NEXT ∨ heapEnd ≤ a1`, and apart from the vector's buffer at entry.
- **Post**: `VecT env m' a0 16`, `len' = len + (a2 - a1) / 16`, and the buffer the one at entry (capacity and pointer equal) or `Fresh m m' ptr' (16 cap')`.
- **Out**: the header's 24 bytes or the buffer at entry (`InRange (vecPtr m a0) (16 * vecCap m a0)`); `memcpy` into a grown buffer is covered by the frame's fresh range.
- **Why**: `memcpy`'s `CopyPreT false` needs the destination (the spare room, in the old or a fresh buffer) apart from the source whichever way `reserve` went: from `SrcT`'s last conjunct if not grown, from the source's `a1 + n ≤ NEXT ∨ heapEnd ≤ a1` if grown (fresh blocks lie in `[NEXT, heapEnd)`). The header must survive `memcpy` and be re-read: `HdrApart` if not grown, `Owned` if grown. `PostT`'s last conjunct is there for the callers' second call (D6).
- **Rejected**: a lemma deriving header/buffer apartness from `RawVecT` (the backlog item): false in general for a header in the heap, which `RawVecT` admits; so an explicit conjunct, plus `HdrApart.of_stack` (a header at or above `stackLimit` with a `RawVecT` buffer has it), which covers both image call sites. `SrcT` with `InWin`: excludes the static data and a slice above `heapEnd` in the heap window, which the source may be (`inWindow` admits both).
- **Claims**: (a) `ReserveT.ReserveSpecT env 8 16`'s precondition (`ReservePre ∧ VecT`, earlier wave) is a closed goal at the real call (`total`'s first block: `hpre_9`, `hpre_10`, `hpre_11` through the prologue's stores). (b) `MemcpyT.MemcpySpecT`'s `CopyPreT false` (wave 1a) is closed at the real call from `room`'s five facts. (c) `Out`'s two disjuncts cover every write: `GrowOut` by `grow_in`, the copy by `copy_out_ok`, the length store by `InRange a0 24 (a0 + 16)`.
- **Evidence**: build above; `sed -n '/^def PreT/,/^def SpecT/p' formal/rv64mc/Rv64mc/Proof/Runtime/SpecExtendT.lean`.

### D2. `SpecExtendT`'s proof: the frame's slots and the buffer by hand (`hk1`, `hk2`, `room`, small `Nat` lemmas)
- **Why**: `rv_autoT` does not read the prologue's slots through `reserve`'s frame (`¬ GrowOut …` premise of `keep1_1`) or `memcpy`'s (`¬ CopyOut …`); `hk1`/`hk2` give them from `not_grow`/`not_slot`. An `omega` over the main context (a dozen disjunctions) ran out of 12 GB once (observed, killed by `MemoryMax`), so every comparison is a lemma over `Nat` (`room`, `dst_ok`, `copy_out_ok`, `disj`, `not_slot`, `not_hdr`, `hdr_word`).
- **Claims**: `room`'s conclusion follows from `reserve`'s `ReservePost` in both branches (`by_cases h : k ≤ C0 - L0`).

### D3. `FromIterET.SpecT` (143): `IterT` and the loop
- **Pre**: `SretPre`, the slot `InWin` 24 and aligned; `IterT env m sp it`: the iterator's 32 bytes in a window, aligned, `Owned`; the array `*(it)` `InWin` 400 and aligned; the vector `*(it + 8)` `VecT` and `Owned`.
- **Post**: `VecT env m' sret 16`, `len = count s e` (`e - s` truncated, `count`), and `len = 0 ∨ Fresh m m' ptr (16 len)`. Products not stated.
- **Loop**: `Total.loop` at instruction 124 over `LInv … k` with `x19 + (k + 1) = e`; the back edge takes `ih (k - 1)` when `e ≠ x19 + 1` (`hk0 : k ≠ 0`), exit otherwise. The bound register `x22` is `max(s, 1600)`; `LInv`'s `(X = 1600 ∧ i ≤ 1600) ∨ X = i` with the branch `X ≠ i` gives `i < 1600` (`idx_lt`), so `i / 64 < 25` (`arr_ok`); the vector's element is in its buffer by the code's own check `i % 64 < len` (`vec_ok`).
- **Why**: `IterT` is what the loads need; `Owned` keeps the vector's header readable through `alloc`, `reserve`, `E::mul` and the stores into the fresh block (`hKeep`, from `LInv`'s `env.Frame`).
- **Rejected**: `NEXT M = NEXT M0` in the invariant (as `FromIterOptT`): `E::mul`'s frame lets `NEXT` grow, so `LInv` has `NEXT M0 ≤ NEXT M`.
- **Claims**: `reserve`'s precondition and `E::mul`'s (`True`) are closed at the real calls; the measure strictly decreases on the back edge.

### D4. `Bus.TryMapT.SpecT` (153): `ClosureT`, `ClaimT`, and the cut at the joins
- **Pre**: the slot (96 bytes) `Owned`, `InWin`, aligned; `ClosureT env m sp f`: `f`'s 32 bytes `InWin`, aligned, `Owned`; the point `BufT env m n S 16` (`n` at `f + 16`, `S` at `f + 8`); the values `VecT` (at `*(f + 24)`) and `Owned`.
- **Post**: for `j = 0, 1`, `ClaimT env m m' (sret + 48 j) n j`: `VecT`, `vecLen = n`, `n = 0 ∨ Fresh`, column word `j`. The values and the copied bytes are not stated.
- **Proof structure**: `rv_autoT … stop [86, 96]`; `mid` from 96 (the second clone), `fin` from 134 (the stores), each over `CloneT` (a clone's buffer: `n = 0 ∧ c = 0`, or `c = n`, fresh, aligned, in `Nat` form so the closer and `omega` read it). Dead paths (no bytes but a point, bytes but none) close by `exfalso` from `ovf`.
- **Why the cut**: the joins 86, 96, 124, 134 are backward-jump targets; `rv_autoT` stopped there with `through *` and with `through [86, 96, 124, 134]` alike (observed, runW4a/scratch/tm2.txt: `left at 86/96: a stop or a loop's head`); continuing each stopped goal with `rv_symT` ran out of 2,000,000 heartbeats (observed). Lemmas over clean states took 92 s in all.
- **Claims**: `alloc`'s, `memcpy`'s (`CopyPreT false`), `handle_error`'s and `panic_bounds_check`'s preconditions are closed at the real calls; the values' two elements' windows are closed by the executor from `hVb`/`hVl` and the code's length checks.

### D5. `Table/BuildT.lean`: the three instances
- `specExtendE` from `AllocT.reserveE` and `CopyUseT.memcpy`; `fromIterE` from `RuntimeT.alloc`, `AllocT.reserveE`, `RuntimeT.handleError`, `FieldT.eMul env hd`, `RuntimeT.panicBoundsCheck`; `tryMapClaims` from `RuntimeT.alloc`, `CopyUseT.memcpy`, `RuntimeT.handleError`, `RuntimeT.panicBoundsCheck`. Open hypotheses: `hnext`, `hend` (env) and `hd : FieldT.ClmulTable env` for `fromIterE`. Each stack inequality by `decide`.
- **Claims**: three `#guard_msgs in #print axioms` blocks pin `[propext, Classical.choice, Quot.sound]`. The guard caught a real error during the pass (the instance named `TryMapT` out of scope elaborated to an error term reported as "does not depend on any axioms"); fixed by `Bus.TryMapT`.

### D6. Obligations recorded (`notes/total-status.md`, "Obligations")
- 87 and 110 (`concat`) for 106's `PreT`, 138 (`verify_layer`) for 143's, 48 (`verify_bus_balance`) for 153's: which call-site fact gives each conjunct, read from the templates (sites: 110 steps 61 and 67 with the header at `sp + 0`; 87 step 53 at `sp + 8`; 138 step 385, iterator at `sp + 0x248`; 48 step 177, closure at `sp + 0x3d0`). Where a conjunct needs a builder's `VecT` (the vector at 138's `sp + 0x70`, the values at 48's `sp + 0x1e0`) it is stated as owed, not checked.

### D7. Raised `maxHeartbeats`
- `SpecExtendT.total` 1,000,000; `FromIterET.loop` 2,000,000, `tail` 1,000,000, `total` 2,000,000; `TryMapT.fin` 1,000,000, `mid` 2,000,000, `total` 2,000,000.
- **Why**: the `rv_autoT`/`rv_symT` runs plus the closing script exceed the default in one declaration. Observed at the default: `SpecExtendT.total` (timeout at `isDefEq`), `FromIterET.loop` and `tail` (timeout at `whnf`, runW4a/scratch/fi5.txt), `FromIterET.total` (first draft). Not measured at the default: the three `TryMapT` declarations (raised from the start), and no smaller value was searched for any of them.

## Invariants of the whole change
- No existing statement changed: `git diff 0e6127ec04 --stat` lists only the four new `.lean` files, `README.md` (two layout sentences) and `notes/total-status.md` (three rows, three obligation bullets).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`: `grep -n "sorry\|admit\|axiom \|native_decide\|bv_decide\|implemented_by" <the four files>` is empty (the `#print axioms` lines aside).
- No em or en dashes in the changed files (`grep -c "—\|–"` -> 0 each).

## Not done (this pass; the list continues in later passes)
- 142 `try_from_fn`, 183 `GenericShunt::next`, 148 `jump_constraints`, 200 `Flushes::pair`; class A 102, 53, 36; zeroed-buffer loops 219, 220, 174, 181, 186; `Form` 168, 163, 159, 202 and what they unlock; drops 71, 70. Not attempted: the budget went to the three above. A first look at 183: it reads through `*(it + 0x18)` into a nested table structure and calls `qkeccak_slot`/`is_output_lane`; its precondition needs a representation of that structure, not just windows.
- 143's and 153's products, values and copied bytes, and 106's copied bytes, are not stated: a functional proof of their callers will need them.

## Known risks
- R1. `TryMapT.lean:122` prints `PANIC at Lean.Expr.appArg!` during `fin` (from the executor in `Tactic/`, not from this change's code). The build succeeds and `#print axioms TryMapT.fin`/`total` give the three standard axioms (checked from a scratch file importing the module), but a CI that greps for `PANIC` would flag it. Not investigated.
- R2. `rv_autoT`'s `through` had no effect here (D4). If it is a parse bug in `Tactic/Sym.lean`'s `elabArgs` (`rvThrough`'s node layout), other proofs relying on `through` would silently stop at heads; I did not touch `Tactic/` and did not confirm the cause.
- R3. `SrcT`'s apartness from the vector's buffer is stated at entry. At 110's second call the buffer is the one 110 allocated; 110's proof needs `PostT`'s kept-or-fresh conjunct to carry it. Check that this is enough for 87's loop (each call's source is a caller's slice, the buffer 87's own fresh block, or the same one after a call that did not grow).
- R4. `FromIterET.IterT` asks the 400-byte array in a window even for an empty range; at the one call site the range is `0..1600`, and the array is a frame object, so it holds there.
- R5. `HdrApart` is a new conjunct callers must prove; both image callers have a stack header (`HdrApart.of_stack`). A heap header (none in the image for 106) would need it from its builder.
- R6. The obligations in D6 were read from the templates, not proved; the values' and `sp + 0x70` vectors' `VecT` depends on builders not yet total.


## Pass 2

Base of this pass: 6327fe3b80. Head: 93c96cc5f3 (5 commits: 1fd7b42925, 441dc7793c, 393a470a17, 4c0f7915d0, 93c96cc5f3; not pushed). No defect found in pass 1's commits; nothing of it changed except one line of `Table/BuildT.lean` (a new import, a new theorem, the header's list) and README's layout sentence.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Runtime.SpecExtendT Rv64mc.Proof.Runtime.FromIterET Rv64mc.Proof.Bus.TryMapT Rv64mc.Table.BuildT Rv64mc.Proof.Keccak.TryFromFnT Rv64mc.Proof.Layout.PlacementNextT Rv64mc.Proof.Layout.JumpConstraintsT Rv64mc.Proof.Layout.ConstraintsT Rv64mc.Table.LayoutT2` -> `Build completed successfully (5282 jobs).` (all replayed; output runW4a/scratch/final2.txt; the only noise is pass 1's R1 `PANIC` backtrace from `TryMapT`). Each module was built by the same command when added: TryFromFnT 42 s, PlacementNextT 52 s, JumpConstraintsT 39 s, ConstraintsT 6.9 s, LayoutT2 3.6 to 4.7 s, BuildT 4.7 s.

Skills: lean4:prove, lean4:refactor, writing-lean-proofs loaded.

### What is done (pass 2)

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 142 | `core::array::try_from_fn` (`verify_layer`'s 25 lane weights) | `Keccak.TryFromFnT.SpecT` (`AbortStop`) | Proof/Keccak/TryFromFnT | BuildT.tryFromFnLanes | clmul table; the lane constant's data word (`DataRef.InData`) |
| 183 | `GenericShunt::next` over `build_layout`'s placements | `Layout.PlacementNextT.SpecT` (`AbortStop`) | Proof/Layout/PlacementNextT | LayoutT2.placementNext | none |
| 148 | `layout::jump_constraints` | `Layout.JumpConstraintsT.SpecT` (`AbortStop`) | Proof/Layout/JumpConstraintsT | LayoutT2.jumpConstraints | env; clmul table |
| 145 | `Table::constraints` | `Layout.ConstraintsT.SpecT` (`AbortStop`) | Proof/Layout/ConstraintsT | LayoutT2.constraints | env; clmul table |

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `111 4323` (107, 4057 after pass 1). The summary table is left to the merge.

### D8. `TryFromFnT.SpecT` (142, class D): `SliceT`, `PreT`, `OutT`, a `True` postcondition
- **Pre**: `env.Owned m sp sret 400 ∧ InWin env sret 400 ∧ sret % 8 = 0 ∧ SliceT env a1 a2` with `SliceT env q n := n = 0 ∨ (InWin env q (16 n) ∧ q % 8 = 0)` (a slice of `E`: a heap vector's buffer or a caller's stack array; `SliceT.of_buf` gives it from `BufT` and `len ≤ cap`). **Post**: `True`. **Out**: `InRange sret 400`.
- **Why**: no partial spec; the one caller (138) then hands the array to 143, whose `FromIterET.IterT` asks only the array's window and alignment, which are frame facts of 138, not contents. The three indices (the lane and the two shifted lanes, computed through a multiply-high by the static word `0x3333333333333334`) are each checked against the slice's length by the code, so safety needs no arithmetic on `mulhu`: the loads' windows come from the checks (`elem_ok`, `cur_ok`).
- **Proof structure**: `rv_autoT` to the loop's head (instruction 50); `loop` (`Total.loop`, `LInv`, measure `k` with `x22 + k + 1 = 25`), cut at 98 (`body`, `BInv`: past the three checks, the indices abstract) and at 164 (`tail`, `TInv`: the copy and the return). One lane's frame and saved words: `step_ok`.
- **Rejected**: one `rv_symT` from the head through the body: timed out at 1,000,000 heartbeats (observed, runW4a/scratch/tf1.txt), the `mulhu` terms in the context. A functional postcondition (the weights): not needed by any caller's safety.
- **Claims**: (a) `memcpy`'s `CopyPreT false` (wave 1a) is a closed goal at the real call (`tail`: `sret` from `hown`/`hwin`, the source the frame's array). (b) `E::mul`'s `Pre` is `True`. (c) The measure decreases: the back edge has `x22 + 1 ≠ 25`, so `k ≠ 0` (`hk0`). (d) `LInv` holds at entry with `k = 24`.
- **Call site**: 138 step 375 (`sret = sp + 0xa0`, the slice `(*(sp + 0x90), *(sp + 0x98))`, the header at `sp + 0x88` that `eq_kernel` (137, not total) builds): recorded in notes/total-status.md's Obligations.
- **Raised heartbeats**: `body` at 400,000 (observed timeout at the default 200,000, runW4a/scratch/tf15.txt; 400,000 measured to pass, nothing between searched). `loop`, `tail`, `total` run at the default.

### D9. `PlacementNextT.SpecT` (183): frame objects, `PostT` the caller's measure
- **Pre** (`IterT`): the shunt `it` (40 bytes), `sret` (24), the closure's environment `c` (8), the header `V = *c` of `offsets` and the residual `r` (8) are caller frame objects (`StackObj sp a n`: `sp ≤ a`, `a + n ≤ 0xc0000000`), aligned; `c + 8 ≤ it`, `V + 24 ≤ it`, `it + 8 ≤ sret`, `r` apart from the cursor's word (a disjunction); `offsets` `VecT env m V 16`; the slice `[cur, end)` whole words, in a window and aligned unless empty.
- **Post**: `*sret = 2` (the end, or a `None` offset with the error stored at `r`), or `cur < end` and `*it = cur + 8`. **Out**: `sret`'s 24 bytes, the shunt's first 24, `r`'s 8.
- **Why**: the function stores the advanced cursor at `it` before it reads `c`, `*c` and the vector, and stores `sret` and `r` after; the apartness facts are what the reads and `PostT` need. `PostT` is what `build_layout`'s collecting loop needs to end (the cursor's distance to `end` decreases). Frame objects as linear facts: a first draft with each object `InWin`/`Owned` (disjunctions) ran out of 4,000,000 heartbeats in 9 minutes (observed, runW4a/scratch/pn2.txt); with linear facts the whole body runs at the default in 47 s.
- **Rejected**: the general (heap or frame) form, for the cost above; every image call site has them in `build_layout`'s frame (read from `Gen/Tmpl/Verifier/Layout/BuildLayout.lean`: `c = sp + 0xd0` holding `sp + 0xb8`, the shunt at `sp + 0x148` and `sp + 0xd8`, `sret = sp + 0x188` and `sp + 0x1a0`, `r = sp + 0x138`).
- **Claims**: `qkeccak_slot`'s and `is_output_lane`'s `Pre` are `True`; `offsets[4]` and `offsets[count]` are read only past the code's length checks (`elem4_ok`, `elem_ok` via `SliceT.of_buf`); the obligation on 45 (which conjunct comes from which offset, and that `offsets`' `VecT` is `stack`'s (182) to give) is in notes/total-status.md.

### D10. `JumpConstraintsT.SpecT` (148) and `ConstraintsT.SpecT` (145)
- **148 Pre**: `SretPre`, `sret` in a window, aligned, the columns `SliceT`. **Post**: `VecT env m' sret 16`, length `2`, buffer `Fresh m m' ptr 32` (as the other builders). `alloc` through `HoldsT.mono_stop` (`AllocStop` to `AbortStop`), as `FromIterET`. The loads of columns 13 need `len ≥ 14`, from the code's two checks (`h14`).
- **145**: the jump opcode tail-calls 148, any other stores the empty vector; `PostT`: `VecT`, length `0`, or `2` with a fresh buffer. Taken out of the list's order (item 4, "what they unlock") because 148 unlocked it and it is 11 instructions; its `Table` theorem uses 148's through `mono_need` (same `Needs`).
- **Claims**: 145's `Pre` is 148's with the columns in `(a2, a3)`, closed at the tail call; the call site 54 (`table_sumcheck`, step 365, `sret = sp + 0x90`) is recorded as an obligation.

### D11. `Table/LayoutT2.lean`
- `placementNext` from `LayoutLeafT.qkeccakSlot`, `isOutputLane`, `RuntimeT.panicBoundsCheck`: no open hypothesis. `jumpConstraints`, `constraints`: `hnext`, `hend` (env) and `FieldT.ClmulTable`. Each stack inequality by `decide`. Each pinned by `#guard_msgs in #print axioms` to `[propext, Classical.choice, Quot.sound]`; so is each `total`.
- `BuildT.tryFromFnLanes` is `omit hnext hend in` (no `alloc` below it).

### Invariants of pass 2
- No existing statement changed: `git diff 6327fe3b80 --stat` lists four new `.lean` files under `Proof/`, the new `Table/LayoutT2.lean`, `Table/BuildT.lean` (an import, a theorem, its docstring line), `README.md` (two edits), `notes/total-status.md` (four rows, three obligation bullets).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`: `grep -n "sorry\|admit\|axiom \|native_decide\|bv_decide\|implemented_by" <the new files>` is empty but for the `#print axioms` lines.
- No em or en dashes in the changed files (`grep -c "—\|–"` -> 0 each).

### Not done (pass 2)
- **200 `Flushes::pair`, abandoned with an obstacle** (about 75 minutes): the stores into `self.push`'s buffer followed by `grow_one` on `self.pull` make `rv_symT` run out of heartbeats even from slim invariants. Measured: the whole body at 1,000,000 timed out (2 min); with the cut at instruction 30 the entry part takes 10 s; 30 to 52 (loads) is fast; 52 to 86 (three stores, the length, `grow_one(self + 24)`) timed out at 1,000,000 with and without the `VecT` hypothesis in context (2.5 to 3 min, runW4a/scratch/pa16.txt, pa18.txt), while 52 to 62 (before the call) takes 26 s; 86 to the return closes in 20 s once the postcondition is an opaque `Post` (the concrete `PostT` made `closeSide` run past 3,000,000). The draft, with `fin` (86 to the return) and the lemmas `vecT_mk`, `frame_buf`, `frame_elem`, `get_elem` proved, is runW4a/scratch/PairT.lean.wip (not committed; it has `sorry`). Proposed route: cut once more at 62 and make the call to `grow_one(self + 24)` by `HoldsT.call` by hand, its `GrowPreT` proved from the invariant's equalities of `self.pull`'s header words with the entry's (`RawVecT.keep`); `self` lies in a caller's frame at every image path (`tables()` passes `sp + 0x20`, `sp + 0x118`, `sp + 0x330` to the `flushes_*` builders), which is what the draft's `FlushesT` asks.
- **Class A 102, 53, 36**: not attempted (budget). Finding for the route: `HoldsT.of_holds_post` needs the partial contract at the image, and `Table/Multilinear.selectorPoint` takes `Vec<E>::reserve`'s partial contract (38) as an open hypothesis; `HoldsT.holds` cannot give it from `ReserveT.ReserveSpecT`, whose `Stop` is not empty. So the `Table` instance by that route would leave a non-environment hypothesis: these need a port of the partial proof (`Proof/Multilinear/SelectorPoint.lean`, 567 lines) with `rv_autoT`/`rv_symT`, on `FromIterET`'s structure.
- **Zeroed-buffer loops 219, 220, 174, 181, 186; `Form` 168, 163, 159, 202 and what they unlock (218, 182, 150, 194); drops 71, 70**: not attempted (budget). 194 (`state_derived`) waits on 200.

### Where to look hardest (pass 2)
- `PlacementNextT.IterT`'s specialisation to frame objects and its order facts (`c + 8 ≤ it`, `V + 24 ≤ it`, `it + 8 ≤ sret`): check them against `BuildLayout.lean`'s two call sites (template steps 361 and 414) and the copy of the shunt to `sp + 0xd8` between them.
- `TryFromFnT`'s `True` postcondition: whether 138's later reads of the array at `sp + 0xa0` (through 143) need more than its window, which 138's frame gives.
- `SliceT` sits in `Proof/Keccak/TryFromFnT.lean` and the `Layout` modules import it from there (new modules only; moving it into `VecReprT` would edit an existing file).
- `PlacementNextT.PostT`'s right disjunct is proved with `m'` read through the stores to `sret`, `it + 16` and `r` (by the executor, from the apartness facts): a reviewer can check it by replacing `it + 8 ≤ sret` with its negation and watching the build fail.


## Pass 3

Base of this pass: 93c96cc5f3. Head: 6c359dedac (7 commits: b4106e0056, 18ab3be666, b71ceee30e, 3baf11bbe1, 3c51b35765, 08dd9d9e3c, 6c359dedac; not pushed). No defect found in passes 1 and 2's commits; nothing of them changed except README's layout sentences (names added) and new rows and bullets in notes/total-status.md.

Item 200 (`Flushes::pair`) skipped: pass 2 abandoned it with a stated obstacle (heartbeats at the `grow_one(self + 24)` call after the stores), and its proposed route (cut at 62, the call by hand) is not new to this pass.

Skills: lean4:prove, lean4:refactor, writing-lean-proofs loaded.

### What is done (pass 3)

| idx | function | contract | module | `Table` theorem | open hypotheses |
|---|---|---|---|---|---|
| 102 | `multilinear::selector_point` (class A) | `Multilinear.SelectorPointT.SpecT` (`AbortStop`) | Proof/Multilinear/SelectorPointT | MultilinearT2.selectorPoint | env |
| 53 | `field::powers` (class C) | `Field.PowersT.SpecT` (`AbortStop`) | Proof/Field/PowersT | FieldT2.powers | env; clmul table |
| 36 | `keccak::linear_transpose::<E>` (class A) | `Keccak.LinearTransposeT.SpecT` (`AbortStop`) | Proof/Keccak/LinearTransposeT | KeccakT.linearTranspose | env; the three tables (`InData`), `KECCAK_RHO` as `u32`s (`RhoAt`) |

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Multilinear.SelectorPointT Rv64mc.Table.MultilinearT2 Rv64mc.Proof.Field.PowersT Rv64mc.Table.FieldT2 Rv64mc.Proof.Keccak.LinearTransposeT Rv64mc.Table.KeccakT` -> `Build completed successfully (5274 jobs).` (all replayed; runW4a/scratch/final3.txt; the only noise is the pre-existing `Reverse.lean` module-system note). Each was built by the same command when added: SelectorPointT 24 s, MultilinearT2 3.0 s, PowersT 38 s, FieldT2 6.5 s, LinearTransposeT 150 s (`loop3` about a minute of it), KeccakT 6.7 to 9.0 s. One raised `maxHeartbeats` (D15).

`awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` -> `114 4673` (111, 4323 after pass 2). The summary table is left to the merge.

### D12. `SelectorPointT.SpecT` (102, class A): a port keeping the partial postcondition
- **Pre** (`PreT`): the partial `Pre` (`Owned` sret) and the slot `InWin` 24 and 8-byte aligned: `FromElemT.FromElemPreT`'s shape, the same prologue. **Post** (`PostT`): the partial `Post` (`FreshVecE` of `selectorPointRust`) and `CloneT.ClonePostT env 16` (`VecT` of the result, `vecLen = a2`, the buffer fresh unless empty). **Out**: the partial `Whir.SretOut 24`. **Stop**: `AbortStop` (`alloc` through `mono_stop`, as `FromElemT`).
- **Strengthening**: `PreT` is the partial `Pre` and two conjuncts, `PostT` is the partial `Post` and one conjunct, `Out` unchanged: the total contract implies the partial postcondition by `.1` (no separate lemma written, the conjunction is literal).
- **Proof**: the partial proof's structure (`after_of`, `TailInv`, `Inv`, `MemInv`, `mem_step`, `exit_fin`, `fin`, imported, not restated) stepped by `rv_autoT`/`rv_symT`. `loop` is `Total.loop` at instruction 94 over `LInv` (`∃ j, j + k + 1 = n ∧ Inv … j ∧ code kept`), measure `k`; the back edge takes `ih (k - 1)` from `hc : regs .x12 ≠ ofNat j + 1` (`cnt_iff`). At the exit the loads are stepped with `rv_sym.heap false` so that the final memory matches `exit_fin`'s statement (with it on, the executor reads the slots through the two heap stores and the terms differ); `ClonePostT`'s goals are closed by rewriting the slot reads through `MemInv`'s stack conjunct and `rv_closeT`. `tail` from `reserve`'s return (78), `total` from the entry, with `on_goal 11`/`on_goal 5` picking the two `tail` goals (the `first | refine tail …` form failed silently under `try`).
- **Call sites**: 101 (`Placement::eq_above`, `sret = sp + 0`) and 131 (`Placement::stack_point`, `sret = sp + 8`), both slots of the caller's frame, 8-aligned (read from `Gen/Tmpl/Verifier/Multilinear/Placement/{EqAbove,StackPoint}.lean`). Recorded in notes/total-status.md's Obligations.
- **Callee Pres closed at the real calls**: `alloc`'s, `ReserveT.ReserveSpecT`'s (`ReservePre ∧ VecT` of the header at `sp`), `handle_error`'s.

### D13. `PowersT.SpecT` (53, class C): the spec's functional contract, proved
- **Pre**: `Powers.Pre` (`Owned` sret), `InWin` 24, 8-aligned. **Post**: `Powers.Post` (`FreshVecE` of `powersM (a1, a2) a3` through `ofLimbsW`) and `VecT env m' sret 16 ∧ vecLen = a3 ∧ (a3 = 0 ∨ Fresh …)` (`ClonePostT`'s shape with the length register `a3`). **Out**: `SretOut 24`. **Stop**: `AbortStop`.
- **Why functional**: the task asks to prefer the existing spec's contract for class C; `E::mul`'s total contract carries `EMul.Post`, so the products are available.
- **Proof structure**: `st base j` is `powersM`'s fold after `j` steps (`st_succ`, `st_length`, `st_getElem`, `powersM base n = (st base n).1` by `rfl`). `total` runs `rv_autoT` to the loop's head (118) and the copy (140): two of the four paths are dead (`n << 4 = 0` with `n ≠ 0`, and the reverse), by `SelectorPoint.ovf`. `loop` (`Total.loop`, `LInv` with `j + k + 1 = n`, measure `k`) runs the body in two `rv_symT` calls, because instruction 48 is a jump target where the executor stops; the `grow_one` branch (instruction 60) is dead: `ofNat j = n` against `j < n`. `step_mem` (the stores, then `E::mul`'s `keep`), `step_frame`, `exit` (the copy, `post_of` for `FreshVecE`), `pro_frame`, `saved_frame`, `hdr_congr` carry the memory.
- **`grow_one` is not a hypothesis** of `total`: the branch to it is refuted before the call, so `FieldT2.powers` does not take `growOne`'s instance.
- **Call sites**: 42 (`walk`, `sp + 0x3b0`, step 250), 66 (`verify_stacked_opening`, `sp + 0`, step 70), 74 (`verify_whir::<…{closure#1}>`, `sp + 0x240`, step 342): slots of the caller's frame, 8-aligned, within it (frames `0x4f0`, `0x80`, `0x2c0`). Recorded in Obligations.

### D14. `Table/MultilinearT2.lean`, `Table/FieldT2.lean`
- New files (MultilinearT and FieldT exist and are not edited). `selectorPoint` from `RuntimeT.alloc`, `AllocT.reserveE`, `RuntimeT.handleError`; `powers` from `RuntimeT.alloc`, `FieldT.eMul env hd`, `RuntimeT.handleError`. Stack inequalities by `decide`. `#guard_msgs in #print axioms` pins `[propext, Classical.choice, Quot.sound]` for both `Table` theorems and both `total`s.

### D15. `LinearTransposeT.SpecT` (36, class A): the partial proof ported segment by segment
- **Pre** (`PreT`): the partial `Pre`, the slot `InWin` 24 and 8-aligned, the slice `TryFromFnT.SliceT env a1 a2` (none, or in a window and 8-aligned: its 25600 bytes are read through computed indices). **Post** (`PostT`): the partial `Post` and `VecT env m' sret 16`. **Out**: the partial's. **Stop**: `AbortStop` (`assert_eq!` on another length, `alloc`, `handle_error`, the bounds check). Literal strengthening of the partial contract: `.1` of each.
- **Structure**: the partial's segments, each a lemma with a continuation, ported one by one, each loop `Total.loop` over the partial invariant and the code map kept: `loop1` (`LInv1`, lanes and bits flattened into one measure `1600 - (64 lane + z) - 1`), `loop2` (`LInv2`), `mid`, `loop3` (`LInv3`), `fin`; `total` chains them. The partial's lemmas (`loop1_mem`, `loop2_mem`, `loop3_mem`, `mid_mem`, `slot3`, `result_elems`, `memset_frame`, `memset_cols`, `load_g`, `pi_load`, `rho_load`, `idx_eq`, `cols_addr`, `xval`, the masks) are imported, not restated.
- **Computed addresses**: a load at an address the code computes by `mulhu`, masks or a table read is stepped to a stop just before it (instructions 84, 143, and 44 for the slice), the partial's normalizing lemma rewrites the register file there, and the window's arithmetic is then linear (`cols_toNat`, `hw0`, `g0`/`g8`).
- **Tables**: `KECCAK_PI`'s word and `KECCAK_RHO`'s `u32` at lane `l + 1` are in a window and aligned by `table_win` (a part of word `k` of a table in `env.data`, from `Windows.data_ok`); the magic word by `FromElemT.data0`. Their values are the partial's (`pi_load` from `InData.words`, `rho_load` from `RhoAt`).
- **Callee Pres closed at the real calls**: `MemsetBytesT.MemsetSpecT`'s (`MemsetPreT`: both `memset`s are of the frame, in the stack window), `alloc`'s, `ReserveT.ReserveSpecT`'s (`ReservePre ∧ VecT` of the header at `top - 72`), the four `Aborts`.
- **Raised heartbeats**: `loop3` at 1,000,000: its five row cases in one declaration ran out at the default 200,000 (observed, runW4a/scratch/lt14.txt); 1,000,000 measured to pass, nothing between searched (the partial `loop3` sits at 4,000,000).
- **Dead paths**: the bounds check at instruction 41 (`64 π ≥ 1600`) reaches `panic_bounds_check`, whose `Aborts` closes the path through `hstop`; `loop1`'s branch to it is not refuted, it is a legitimate abort the contract allows. `grow_one` is not called by this function.
- **Call site**: 138 (`verify_layer`, step 420): `sret = x23 + 0x30`, the slice the elements of the vector 143 builds at `sp + 0x230` (`SliceT.of_buf` from `FromIterET.PostT`'s `VecT`); recorded in Obligations.
- **`Table/KeccakT.lean`**: callees `VecT.memset` (`MemsetSpecT` at `Idx.Memset`), `RuntimeT.alloc`, `AllocT.reserveE`, `RuntimeT.panicBoundsCheck`, `RuntimeT.assertFailedUsizeUsize`, `RuntimeT.handleError`; open: `hnext`, `hend`, three `DataRef.InData` and `RhoAt` (the partial `Table/Keccak.lean` takes `RhoAt` too; it is a fact about the image's static data as `u32`s, which a later pass could derive from `InData` of the same table).

### Invariants of pass 3
- No existing statement changed: `git diff 93c96cc5f3 --stat` lists six new `.lean` files (three under `Proof/`, three under `Table/`), `README.md` (layout names), `notes/total-status.md` (three rows, three obligation bullets).
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `implemented_by` in the new files (`grep` empty but for the `#print axioms` lines); one `maxHeartbeats` (D15); no em or en dashes (`grep -c` 0 each). `LinearTransposeT` uses `decide +kernel` once (the first `KECCAK_PI` word shifted, a closed word equation), as the partial does.
- Each `Table` theorem and each `total` is pinned by `#guard_msgs in #print axioms` to `[propext, Classical.choice, Quot.sound]`.

### Not done (pass 3)
- **Zeroed-buffer loops 219, 220, 174, 181, 186; `Form` 168, 163, 159, 202 and what they unlock (218, 182, 150, 194); drops 71, 70**: not attempted (budget spent on 102, 53, 36). Next in order: 219 (`counting_sort::<usize, block_members::{closure#0}>`).
- **200 `Flushes::pair`**: still pass 2's obstacle; not retried (no new route).
- The callers' obligations (101, 131 for 102; 42, 66, 74 for 53; 138 for 36) are read from the templates, not proved.

### Where to look hardest (pass 3)
- `PowersT`'s functional postcondition: `st` against `Model.powersM` (`powersM base n = (st base n).1` by `rfl`), and `post_of`'s element reads through the three stores into `sret` (`owned_ne_fresh`).
- `LinearTransposeT.loop1`'s flattened measure: the outer back edge goes from bit 63 of lane `l` to bit 0 of lane `l + 1` (`ih (k - 1)` with `64 (l + 1) + 0 + (k - 1) + 1 = 1600`); and `table_win`'s offset for `KECCAK_RHO` (`4 (l + 1) = 8 ((l + 1) / 2) + 4 ((l + 1) % 2)`).
- `SelectorPointT`'s exit uses `rv_sym.heap false` so its memory matches the partial `exit_fin`; a reviewer can check that `PostT`'s `ClonePostT` goals are closed from the rewritten slot reads, not assumed.
- `LinearTransposeT.SpecT`'s `PreT` adds `SliceT` for the slice: at 138 it comes from 143's `VecT` (Obligations); if 138's proof finds the slice's buffer not 8-aligned, that would be a finding against this `PreT`.

## Golf

Commit 41f60e0f85 on top of 6c359dedac. Proofs only: no `def`, contract or theorem statement changes, and no `PreT`, `PostT`, `OutT` or `SpecT` is touched. Five files, 37 lines added and 63 removed. Skills: `lean4:golf` and `lean4:refactor` were both loaded.

- **G1. `SpecExtendT.keep_of_frame` (new lemma) replaces the identical 9-line `hKeep` proofs in `TryMapT.mid` and `FromIterET.loop`.** Its conclusion is word for word the old `hKeep` type, `∀ a : Word, (a.toNat + 8 ≤ (env.next m).toNat ∨ top.toNat ≤ a.toNat) → M.getMem a = m.getMem a`, so the `rv_symT ... with [hL, hKeep]` calls get the same fact. Its proof is the same case split. The context facts the old `omega` calls used are now explicit: `env.layout`, `hF.1` and `hF.2.1`, and `hlim : stackLimit ≤ top`. At each call site `hlim` follows from `hstk` by `omega`. Adding it to `SpecExtendT` adds no import, because both users already import that module.
- **G2. `TryMapT.saved_ok` and `FromIterET.saved_frame`: the nested `refine Tactic.frame_store (... (Tactic.frame_refl hnx) ?_ ?_) ... <;> closer` is now `repeat (first | ...)` followed by `all_goals closer`.** This is the pattern `PowersT.saved_frame`, `FinishGrowT` and `FinishGrowAT` already use. The lemmas, their order and the side-goal closer (`rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega`) are unchanged, so the proof term has the same shape. `FromIterET` gains `simp only [saved]` first, as `TryMapT` already had. In `TryMapT`, trying `exact Tactic.frame_refl hnx` first timed out at `whnf` on the 13-deep store chain. That build's log is runW4a/golf-build1.log. The `first` alternatives are therefore ordered with `refine` first and the base case last. `FromIterET`'s 9-deep chain built with either order.
- **G3. Hypotheses rewritten in place instead of copied.** The old form was `have := h; rw/simp at this; exact this`. The new forms are `rwa [...] at h`, or `simp only [...] at h; exact h`. This applies to `hVb` and `hVl` in `TryMapT.total` and `FromIterET.total`, to `hlen1` and `hle1` and the `first` arm for `reserve`'s precondition in `SpecExtendT.total`, to `hN01` (which now ends `rwa`), and to the last goal of `ConstraintsT.total`. Each rewrite runs inside the `by` block of a `have`, or as a goal's final tactic, so the change to the hypothesis does not reach other goals. The rewrite lemmas and the closing `exact` are the same. A `simpa only ... using` version was tried for `hVb` and failed: `simpa` checks the result only at reducible transparency, and `BufT` must be unfolded. The kept version therefore ends in `exact`.
- **G4. `PowersT.slots`: the anonymous constructor of 12 identical `slot_toNat (by decide) (by omega) (by decide)` became `and_intros <;> exact slot_toNat (by decide) (by omega) (by decide)`.** It is the same lemma with the same side proofs on every conjunct, and the conjuncts are all of the same form.
- **G5. `PowersT.step_mem`: dropped `have ne : ∀ x y : Word, x.toNat ≠ y.toNat → x ≠ y`.** The proof never refers to it. The only `simp`/`rw` arguments that follow are `gm_ne`, `hdr`, `getMem_setMem_eq` and `cnt_step`, and `omega` ignores universally quantified hypotheses.

Not done: three changes were considered and left out because each would add an import or move a lemma between files for a few lines.
- Proving `FromIterET.vec_ok` from `TryFromFnT.elem_ok` and `SliceT.of_buf`. It would need `FromIterET` to import `TryFromFnT`.
- Proving `PlacementNextT.elem4_ok` from `JumpConstraintsT.word_ok`. `PlacementNextT` does not import `JumpConstraintsT`.
- The pre-existing `PANIC at Lean.Expr.appArg!` that `TryMapT.fin` reports at info level. It was there at 6c359dedac and is not a build error. It is not investigated here.

Check: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build` on the 15 modules the change owns: `Build completed successfully (5370 jobs)`. Rebuilt and newly checked: `PowersT` (49s), `ConstraintsT`, `SpecExtendT` (151s), `TryMapT`, `FromIterET` (213s), `FieldT2`, `LayoutT2` and `BuildT`. Every `#guard_msgs in #print axioms` still passes, pinning `[propext, Classical.choice, Quot.sound]`. The added lines contain no `sorry`, `admit`, `axiom`, `native_decide`, em dash or en dash (`grep -c` gives 0). No `maxHeartbeats` was raised or added.

## Amendments, round 1

Head: 4c7f812bd9 (four commits on 41f60e0f85: e61de7e9a9, 77f94b4737, c2884a80d1, 4c7f812bd9; not pushed). The wave as a whole, superseding the title and the "Head" line at the top, which describe pass 1 only: wave 4a makes ten functions total with `Table` instances: 106, 143, 153 (`Table/BuildT`), 142 (`Table/BuildT`), 183, 148, 145 (`Table/LayoutT2`), 102 (`Table/MultilinearT2`), 53 (`Table/FieldT2`), 36 (`Table/KeccakT`); the rest of the task's list is as in "Not done (pass 3)".

Checks, each the task's command (`cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build ...`):
- `lake build Rv64mc.Proof.Layout.PlacementNextT Rv64mc.Table.LayoutT2` -> `Build completed successfully (5218 jobs).` (PlacementNextT rebuilt in 83 s, LayoutT2 10 s; log runW4a/build_r1a.log).
- `lake build Rv64mc.Proof.Bus.TryMapT Rv64mc.Table.BuildT Rv64mc.Table.MultilinearT2 Rv64mc.Table.FieldT2 Rv64mc.Table.KeccakT` -> `Build completed successfully (5282 jobs).` (TryMapT 201 s, BuildT 38 s, the three tables 48 s each; log runW4a/build_r1b.log). Every `#guard_msgs in #print axioms` in these modules still passes (three standard axioms). The only noise: the pre-existing `Reverse.lean` module-system note and R1's `PANIC` (now at `TryMapT.lean:118`, see R1-1-3).
- The added lines carry no `sorry`, `native_decide`, `axiom`, em or en dash (`grep -c` 0). No `maxHeartbeats` added.

### R1-1-1 (important): fixed
- **Change** (e61de7e9a9): `PlacementNextT.OutT` is now `InRange (regs .x10) 24 b ∨ InRange (regs .x11) 8 b ∨ InRange (regs .x11 + 16#64) 8 b ∨ InRange (m.getMem (regs .x11 + 32#64)) 8 b`: the result, the shunt's cursor (`+ 0`) and count (`+ 16`), the residual. The shunt's `end` at `+ 8` is out of it, so `Env.Frame` keeps it for a caller. The reviewer is right that the old `InRange it 24` covered `end`. The code stores to the shunt only at `x9 + 0x0` and `x9 + 0x10` (`x9 = x11`, template lines 65, 137, 153), so the proof of `total` was not touched and rebuilt as it was; `LayoutT2.placementNext` rebuilt unchanged. The module docstring now says the writes leave `end`.
- **Contradiction with D9**: D9's "Out: the shunt's first 24" and its claim that `PostT` alone is what `build_layout`'s loop needs were wrong: the loop needs `PostT` and `end` kept, which only the narrowed `OutT` gives. D9's claim holds as of e61de7e9a9.
- **For the caller**: `end` is kept when `r` and `sret` also miss `it + 8`, which `IterT` does not force (it puts `sret` at or above `it + 8` and `r` apart from the cursor's word only). At the image's call sites they do: `r = sp + 0x138`, `sret = sp + 0x188` and `sp + 0x1a0`, against `end` at `sp + 0x150` and `sp + 0xe0`; recorded in notes/total-status.md's `build_layout` entry (4c7f812bd9). Narrowing the Pre to force it was not done: it is a fact of the caller's frame, which the caller's proof has as offsets.

### R1-1-2 (nit): fixed here
The title and head line at the top describe pass 1; the wave's whole scope and head are stated in this section's first paragraph (earlier entries are not edited).

### R1-1-3 (nit): fixed here
R1's line: after golf and this round the `PANIC at Lean.Expr.appArg!` is reported at `TryMapT.lean:118:0` (the docstring line of `fin`; it was 116 at 41f60e0f85, 122 before golf); still inside `fin`, still info-level, the build succeeds (runW4a/build_r1b.log line 9).

### R1-1-4 (nit): fixed
77f94b4737: `ClaimT`'s column reads `a + BitVec.ofNat 64 Layouts.ColumnClaim.column`, `PostT`'s second claim is at `regs .x10 + BitVec.ofNat 64 Layouts.ColumnClaim.byteSize`, and `PreT`'s and `SpecT`'s slot size is `2 * Layouts.ColumnClaim.byteSize`, as `ColumnClaimT` writes them. The internal lemmas `fin` and `mid` keep the literal `96` in their hypotheses; the values are definitionally equal (the constants are `abbrev`s), and `total` passes its hypotheses to `mid` unchanged. The proofs did not change; TryMapT and BuildT rebuilt (check above).

### R1-1-5 (nit): fixed
77f94b4737: the predicate is `CloneBufT` (definition, `fin`'s and `mid`'s hypotheses, the module docstring); `CloneT.toNat_add_neg` now resolves only to `Proof.Runtime.CloneT`.

### R1-1-6 (nit): fixed
c2884a80d1: docstrings `**\`selector_point\` at the image** (function 102)`, `**\`powers\` at the image** (function 53)`, `**\`linear_transpose\` at the image** (function 36)`, the indices read from `Gen/Index.lean` (lines 115, 66, 49), in the form `BuildT` and `LayoutT2` use.

### R1-1-7 (nit, optional): deferred
Moving `TryFromFnT.SliceT`/`elem_ok` and `SpecExtendT.keep_of_frame` (with `not_slot`, `dwords_in`, `grow_in`, which `TryMapT` and `FromIterET` also borrow) into a new `Proof/Runtime` module would change the imports and the `open`s of eight of the wave's modules (`TryFromFnT`, `SpecExtendT`, `FromIterET`, `TryMapT`, `PlacementNextT`, `JumpConstraintsT`, `ConstraintsT`, `LinearTransposeT`) and rebuild them with their tables, about 20 minutes of builds on a host a sibling worktree shares, for no change in what is proved. It is the right home; it fits the next wave's golf pass, which will also want `SliceT` (the next vector builders read slices the same way). What it takes: a module `Proof/Runtime/SliceT.lean` with those six lemmas, the eight modules' imports and `open`s retargeted, one build of the 15 owned modules.

### R1-1-8 (nit): fixed here
- D15's "Literal strengthening of the partial contract: `.1` of each" should read as D12's does: `PreT` is the partial `Pre` and more (`InWin`, aligned, `SliceT`), so it is stronger, not implied; `PostT` is the partial `Post` and `VecT`, so the total postcondition implies the partial one by `.1`, and `Out` is the partial's. Only the postcondition (and `Out`) is implied.
- R2's "would silently stop at heads" is wrong: a proof that relied on `through` and stopped at a head would leave an open goal and fail its build, so the effect would be a build failure, not a silent one. What remains of R2: `through` had no effect in D4, cause not confirmed.

## Amendments, round 2

Head: 7e71eb8d57 (one commit on 4c7f812bd9; not pushed).

### R2-1-1 (nit): fixed
- **Change** (7e71eb8d57): `PlacementNextT`'s module docstring now reads "Its writes (`OutT`) leave the slice's `end` alone when `sret`'s 24 bytes and `r`'s word also miss it (`IterT` does not force this; the caller's frame offsets do), which its caller's loop needs to end." Docstring only; no statement or proof changed. The reviewer's alternative (forcing it in `IterT`) was not taken, for the reason given in R1-1-1's "For the caller": it is a fact of the caller's frame (`r = sp + 0x138`, `sret = sp + 0x188` and `sp + 0x1a0` against `end` at `sp + 0x150` and `sp + 0xe0`), recorded in notes/total-status.md's `build_layout` entry.
- **Contradiction**: R1-1-1's "The module docstring now says the writes leave `end`" described an unconditional sentence; that sentence overstated the contract, as the reviewer says. As of 7e71eb8d57 it is conditional, consistent with R1-1-1's "For the caller".
- **Check**: `cd formal/rv64mc && timeout 3600 systemd-run --user --scope -q -p MemoryMax=16G lake build Rv64mc.Proof.Layout.PlacementNextT Rv64mc.Table.LayoutT2` -> `Build completed successfully (5218 jobs).` (PlacementNextT 64 s, LayoutT2 8.6 s; log runW4a/build_r2.log). The added lines carry no `sorry`, `native_decide`, `axiom`, em or en dash (`grep -c` 0).
