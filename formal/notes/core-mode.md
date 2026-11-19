# Modedness at the core IR

Goal (2026-11-18): prove the guest's executability (on the honest hints every instruction finds its inputs written) from per-function facts about the zkDSL core IR and generic theorems about the compilation, replacing the bytecode-level mode walk (`exec-mode.md`), so that a guest edit costs the formal side only the proofs and data of the functions it changes. Success: generated lines for this part down 10x; a one-function edit touches only that function's proof and data; cold build at most 15.7 CPU-h, every module under 7.5 GB; regen under 15 min; `Statement/` unchanged, no new axioms, no raised `maxHeartbeats`.

This note is the design step: the measured census (scripts in `lean_vm/scripts/core-mode/`, Python over the generated data, a measurement and not a proof), the recommended architecture, the generic theorem, the kernel cost and the plan. No proof is changed.

## Recommendation

Split modedness by what each half needs to see. Frame cells (values, plumbing: header, callee frame pointers, jump targets, pooled constants, shared cells, range-check temporaries, hint cells) stay at the ISA, in a data-free bitset walk over `ExecCore`'s segments, with no generated certificate and no hand proof (today's walk, which contains it as its `w` part, passes all 1547 functions). Heap cells, the only part that needs reasoning and the source of every residual, move to the core IR: per function a certificate of **witnesses** (for each heap read, the earlier event of the body, the precondition or the loop run that wrote its cell), checked in one linear pass with no abstract state, so no snapshots; residuals are lemmas on core names (`σ (.n k)`), proved from B1, whose templates already speak core names. The two meet through an order-aware pairing (`Bridge/Align`'s zipper pass extended to heap events) that hands the frame walk an oracle: the pcs whose `DEREF` reads a cell the core certificate proves written. `Mode/Inv*`'s stack invariant is kept and generalized over a per-function frame predicate, so the old walk and the new route discharge `ModeHyps` function by function and coexist until the old one is deleted.

How this differs from the goal's suggestion: values-defined-before-use is not proved at the core. The census shows it holds there for all 1547 functions, but transferring it to `runOp` needs exactly the plumbing the core does not have; at the ISA it costs a few seconds of kernel time per pack and nothing to maintain. And the order-aware extension is of `Align` (an in-order pass already proved sound), not of `Cpl`, whose book is order-free and whose proofs are about the final image.

## 1. Where the volume and the edit cost come from

Generated Lean in `lean_vm/LeanVM` (lines; `sizes`, the census below, and `wc`):

| generator | lines | what | new route |
| --- | --- | --- | --- |
| `mode-cert/gen.py` | 4,133,088 | `Pack/*/ModeD*S*` snapshots 3,845,787; `ModeD*W*` windows 38,976; `ModeD*` 48,928; `Mode{k}` 55,154; `ModeCert` 44,321; `ModeSig` 43,741; `ModeH` 24,364; `ModeL*` 3,863; `Mode/Certs` 27,483 | deleted |
| `res-cert/*` | 10,638 | `Res/` residual certificates (beside 3,533 hand-written) | deleted |
| `bridge-cert/align.py` | 47,698 | `Bridge/Align` 45,982, `Bridge/AlignWin` 1,716 | `AlignWin` deleted, `Align` extended |
| `guest-cert` | 867,713 | `Bundle` 545,965 (code and `Cert.locs`), `Checked*`, `Cplw*`, `Shared*`, `Sig`, `Cells`, `Guest/Checked`, `B2C/{Cplw,Shared}` | stay |
| `guest-core` | 663,142 | `Pack/*/Core*` | stays (read by the new checks) |
| other `bridge-cert` | 187,260 | `AllocChk`, `PairChk`, `JumpCells`, `WitChk`, `PrefixOk`, `ProgAl` (the hint bridge) | stay |

The mode route is 4,145,442 lines, 70% of the 5.96M generated. 98.8% of the `ModeD*` lines belong to 14 functions: `verify_tables` 2,273,740 lines in 501 files, `check_opening_terminal` 546,694, the 11 `open_stacked` specializations 997,051, `main_loop2` 67,426. A snapshot is the walk's whole state at a cut (written cells, heap words `hv`, runs, pointer runs, exponent facts, pending edges); one `verify_tables` snapshot module is 30k lines, 3 MB. By the build records (`.lake/lake-build.tsv` of `/data/exec-spec`, `/data/exec-h2`), the mode route costs about 8 of 15.3 CPU-h cold: windows 3.8, snapshots 3.1.

What stays is offset-coupled but not hand-coupled. `Bundle` holds the code with absolute pcs (a callee's entry is a `SET` of `g^pc`), so an edit that changes a function's length changes the data of every function laid out after it and of their callers, and `Checked`, `Cplw`, `Shared`, `Align` are regenerated with it; nothing hand-written reads them but the generic B2C and bridge proofs. Making that data local too would take a relocatable `Bundle` (code relative to its entry, callees by index through the jump table, one link check), a separate step this design does not need.

Hand-written files that cite bytecode offsets: the residual proofs `EndExecR*.lean` (41 files, 11,554 lines; 14 of them, 4,152 lines, state facts as `M (fp + 398) = …` and pcs) and their definitions `Res/*Defs.lean` (`.fr 17`, `.hp 1 22`, pc `2910`), `Mode/Res{Fam,Ref,Inst}.lean`, `Bridge/{RefTrace,StepOff}.lean`, `EndExecA*.lean` for the bump pointer. They cite offsets because the walk names a value by its frame cell and a residual is a statement about the walk's keys. B1 cites no offset (2 files), it states bodies over core names (`.n k` in 469 files). On the new route a residual is a closed statement about the valuation at core names, stated where the witness check needs it and proved next to the function's B1 module; the bridge from names to cells is once, generic (`Cert.locs`, `FrameHolds`).

## 2. Census over the core IR

`coreir.py` reads `Pack/*/Core*.lean`, the bundles' code and `Cert.locs`; `sizes.py`, `census.py`, `order.py` measure. Parse 13 s, each measure 2 s.

**Size.** The core is not smaller than the bytecode: 563,471 statements (558,448 atoms) against 443,150 instructions, median 1.17 instructions per statement (quartiles 0.97, 1.56; `main_loop2` 189,447 against 114,219, `verify_tables` 5,571 against 5,240). The savings are not in the code a check reads but in the state it carries: the core check needs none.

**(a) Values defined before use.** A forward pass in statement order with the executor's solving rules (an atom with its output and all but one input known solves the last, `assert ==` solving either side, a range check back-solving `y`, frame runs defining their pointer) and intersection at joins: 1547 of 1547 functions pass, no failure. This confirms `exec-mode.md`'s reading of `Fn.renumber`; it is the ISA bitset walk below that the proof needs.

**(b) Heap cells written before read.** The domain: a pointer is a monomial over base values with a power of `g` folded into the offset; written cells come from stores (a `load` whose word is defined), heap hint destinations, frame runs (`frameAddr`), callee guarantees; signatures are inferred callee first (`pre`: cells over parameters read unwritten; `post`: cells over parameters and returned words written on every path); a loop helper's reads and writes over its counter are runs, a read the same iteration's write one step on covers is chained. No rule of `rules_fix.py` is ported. Of 94,961 reads (defining loads, `log2Ceil`'s bit reads, callee preconditions at call sites), 7,639 are covered inside the function (2,276 by a run at a constant index, 797 at a variable one, 1,366 chained), 71,974 are points over parameters (preconditions passed to the caller), and the rest:

| class | reads | functions | families |
| --- | --- | --- | --- |
| loop runs not matched (loop's own precondition, a callee loop's at the call) | 1,839 + 1,833 | 402, 244 | `level_residual`, `opening_queries`, `rs_eq_run`, `aggregate_claims`, `da_levels` |
| pointer loaded from memory (pointer tables) | 4,618 | 158 | `verify_tables` 1,917, the claim lists' monotone paths 1,156, `opening_queries` 519, `block_selector_tab` 306, `keccak_layer` 164, `check_opening_terminal` 132, DA rows 128 |
| index from a hint, a sum or a Keccak word (table index bounds) | 2,633 | 95 | the claim lists 1,156, `decode_query_windows` 542, `rs_eq_run` 504, `column_selector` 286, `grind_check` 87 |
| pointer a callee returned (callee guarantees) | 2,870 | 16 | `open_stacked` 1,821, `verify_keccak` 625, `verify_sub` 354, `ring_switch_weight` 64 |
| own buffer read unwritten | 1,552 | 5 | `verify_tables` 1,519 (filled through a table of pointers) |

By shape (strict: no read outside covered cells and point preconditions; closed: loop runs allowed, every callee closed): no call and no loop 421 functions, 286 strict, 286 closed; calls but no loop 226, 210, 3; calls a loop 366, 122, 159; loop helpers 534, 125, 322. In all 743 strict, 1,280 with loop runs, 770 closed. The families are today's: the walk's residuals are 1,215 `sub`, 91 `lt`, 5 `nz`, 16 `name` in 140 functions (`block_selector_tab` 396, `verify_sub` 316, `child_claim_list_last` 129, `child_claim_list_mono_last` 126, `keccak_layer` 101, `walk_path` 40, `verify_bus_gkr` 46, `shared_selector_tables` 31, `main` 25, `column_selector` 23, `rs_eq_run` 20, `check_opening_terminal` 18, …). The callee-returned and own-buffer classes are gaps of this quick domain (`opening_round` returns a sponge pointer filled two calls down; `verify_tables` fills a buffer through pointers it loads), which `infer.py`'s returned-word guarantees (`Sig.retV`) and pointer runs already close at the ISA; the rules are about heap shapes and port by renaming a frame cell `.fr o` to the value it holds. Expect the ported domain to reach today's closure with about today's residuals.

**Order.** Each core `load` atom (a read or a store) is a `DEREF` of mode `cell` of the code at its certificate cells: 66,128 of 66,128 match. 23,219 of them have no `DEREF` of their own: the compiler shares the cell with an earlier load of the same pointer and offset, so the read happened earlier still, which the earlier load's witness covers. With those, every function's `DEREF`s follow its statement order inside each block (`ite`, `match` and arms start blocks): 0 of 1547 out of order. Hints pair one for one in 970 of 973 functions (`exec-bridge.md`; the three are the advised allocations of `main`, `verify_sub`, `da_verify`, reserved early by `allocAdvice`); allocations are hoisted before the first call and have their own track; branches, table jumps, calls and returns are aligned by `Check` and `Align` already. So the pairing needs no reordering rule beyond shared cells and the advised allocations.

## 3. The generic theorem

New modules `Guest/CoreMode/{Defs,Heap,Frame,Pair,Spec}.lean`. Definitions (all structural, tries keyed by `ℕ`, evaluated by the kernel like `Check`):

```lean
/-- A heap cell over core names: a monomial of values and a power of `g`. -/
structure CCell where
  bases : List (Core.V × ℤ)
  off : ℤ

/-- Why a read's cell is written. -/
inductive Wit
  | ev (p : Bridge.Cur)          -- an earlier write event of the body: a store, a heap hint, a frame run, a call's guarantee
  | pre (k : ℕ)                  -- the function's `k`-th precondition
  | run (r : ℕ) (res : List ℕ)   -- a run (a loop's guarantee or precondition), with its residuals
  | res (k : ℕ)                  -- a residual alone (a pointer table's entry, a table index's bound)

/-- The calling convention: points and runs over parameter indices and returned words. -/
structure HSig where
  pre post : List CCell
  preR postR : List CRun
  term : List (ℕ × ℕ)

/-- A function's heap certificate. -/
structure HCert where
  sig : HSig
  wit : Exec.Trie (List Wit)     -- by read event, in statement order
  res : List CRes                -- closed statements on core names: `lt`, `sub`, `nz`, `ptab`

/-- Core only, one pass, no state: each read's witnesses dominate it (an earlier index of its block
or of an enclosing one, both sides of a join) and write its cell, monomials recomputed from the
defining atoms; each call meets its callee's `pre` and gains its `post`; a loop's tail call meets
its own `preR` (chained or covered) and its `term`. -/
def heapOk (sigOf : String → HSig) (f : Core.Fn) (H : HCert) : Bool

/-- The order-aware pairing: `Align`'s pass with heap events consumed in order (a store or read
`DEREF`, a heap hint, a call), a shared cell's read paired with the earlier `DEREF`; returns the
oracle, the pcs whose `DEREF` reads a cell `H` proves written. -/
def pairOk (f : Core.Fn) (cf : CompiledFunction) (C : Check.Cert) (H : HCert) : Option (Exec.Trie Unit)

/-- The ISA side, no data: a bitset of written frame offsets over `Exec.exec`'s segments, joined by
intersection; XOR, MUL (forward, or back-solved by a divisor `ExecCore` knows nonzero), KECCAK and
JUMP read written cells; a `DEREF` stores when its frame side is written, loads when its pc is in
`O`, links otherwise; callee frame cells `(q, o)` for arguments and returns; header, entry and
return cells as `Sig`'s. -/
def frameOk (F : Exec.Facts) (code : List OffsetInstruction) (sig : Mode.Sig) (O : Exec.Trie Unit) : Bool
```

What they guarantee, per function `j` with certificate `K` (`Mode/Step.lean`'s `Cert`, its frame walk replaced):

```lean
/-- Frame `fp` of function `j` at offset `off`: some core position `π` the pass pairs with `off`,
the frame walk's cells at `off` written, every cell `H` proves written by `π` (read at the valuation
`σ v = M (fp + loc v)`) written, and the residuals at `π` true of `M` at `fp`. -/
def CoreAt (K : Cert) (H : HCert) (M : ℕ → E) (off : ℕ) (s : St) : Prop

theorem frameSpec_core (hh : heapOk sigOf f H = true) (hp : pairOk f cf C H = some O)
    (hf : frameOk F cf.code (H.sig.toSig) O = true) (hc : CheckedFn K f)
    (hres : ∀ fp, FrameOf M j fp → ResAll H M fp) : FrameSpec K (CoreAt K H M)
```

`CheckedFn K f` is the soundness certificate the pack already checks (`Check`'s windows over `K`'s code and `f`), and `FrameOf M j fp` says frame `fp` is an instance of the honest tree (`FrameHolds`, `honest_kid`), so `ResAll`, the residuals at the valuation `σ v = M (fp + loc v)`, is proved once per family from B1.

`FrameSpec K Q` is the interface `Mode/InvRule.lean` needs of one function, stated once for any frame predicate `Q`: at entry `Q` holds from `Sig`'s entry facts; at an offset where `Q` holds, the step's `StepOk` obligations (`OpModed`, each hint's inputs) hold and `Q` holds at the fall-through; at a jump, `Mode/Jump.lean`'s `JumpK` cases hand over: a branch or table jump to `Q` at the target (the pass's joins), a call to the callee's entry facts with `Q` resumable once the callee guarantees `Sig` (`Resume`), a tail call with the header copied (`retStay`), a return with `Sig.post`, the halt. `InvDefs`' stack (`Act`, `Iter`, `Chain`, `Below`, `Susp`, `StackAt`) is unchanged but for `AtOff E F code` becoming `Q j`; then

```lean
theorem inv_rule_of_specs (hQ : ∀ K ∈ guestCerts, FrameSpec K (Q K)) (hsig : SigsIn guestCerts) … :
    InvRule guestProgram img n C M (StackInv Q)
```

and `execute_complete_guest` follows as today. Coexistence: `Q K := if K ∈ coreRoute then CoreAt K (hcert K) M else AtOff …`; `ModeHyps` per function is `FrameSpec K (Q K)`, from `certOk_fn` (the old walk, unchanged) or `frameSpec_core`. Both routes speak `Mode.Sig` at calls: `HSig.toSig` maps a parameter `i` to the callee frame cell `2 + i` (`hp (2 + i) d` facts, runs), and a caller checked by the old walk is regenerated against its callee's new signature.

DEREF direction. The executor decides it from its memory; the frame walk decides it the same way from its bitset (frame side written: store or assertion; else oracle: load; else link), so the step lemma is `Mode/SoundDeref`'s, restricted to frame cells, with the oracle's case using `CoreAt`'s heap fact at the paired read. The core's static view (a `load` whose word is defined is a store) only chooses which events need witnesses; where it disagrees with the bitset, `pairOk` or `frameOk` fails, decidably, with nothing to prove.

Reused: `ExecCore`'s segments, environments and `Facts` (the frame walk runs on them, as `Check` does); `Check`'s `locate` and `loadOk` (a read's `DEREF` at the certificate cells); `Bridge/Align{Defs,Sound,Run,Jump}` (zippers, the order lemma that the head of `cont p` is the path's next event, branch and arm alignment); `Mode/{Jump,Edge}` (`JumpK`, `call_enter`, `ret_regs`, `ret_resume`); `Mode/InvDefs`, `InvStep`, `InvJump`, `InvRule` generalized over `Q`; `Mode/SoundOp`, `SoundDeref`, `SoundHint` for the frame rules; `SoundLoop`'s run lemmas (`loop_step`, `RW.last`, `retStay_sound`) re-keyed to core names; the residual families' mathematics (`EndExecR*`) restated on names. Not reused: `Abs`'s heap domain (`hv`, `h`, runs, pointer runs, `pr`, `xs`), `Win`, `infer.py`'s snapshots, `Cpl`.

Answers to `exec-mode.md`'s alternatives. "Modedness is about the executor's instructions, plumbing included": yes, and that half stays at the ISA, data-free; only heap facts cross, through a pairing the census shows is in order (0 of 1547 after shared cells). "At the ISA a DEREF's direction falls out of the state": kept, the frame walk's bitset is that state. "Extending `Cpl` means redoing `CplWalk` over partial memories": agreed, `Align` is extended instead. "Per-pc annotations are unneeded; recomputation costs what checking would": the measurement says otherwise, recomputation is what writes 3.85M lines of snapshots, since a fixpoint walk must carry and print its state at every cut, while a witness is checked by a lookup with no state. "Heap by B1 alone": not needed, the core tells a store from a read statically; B1 supplies only the residuals' values. "Data-dependent indices defeat a symbolic analysis": still true, those are the residual families, now lemmas on names.

## 4. Kernel cost

Experiments (`decide +kernel` of the def-use pass of section 2 on a function's core, `lake env lean` on a scratch file importing its `Core` module; the import alone is 1.9 s, 2.7 GB): `block_selector__L8` +0.0 s; `verify_tables` (5,571 statements) +2.1 s, +0.6 GB with a `Nat` bit set, +4.7 s with `Exec.Trie`; `main_loop2` (189,447 statements: 35 `match`es of 256 arms) 86 s and 25.7 GB with the bit set, a deterministic timeout at 42 GB with the trie. So a linear core pass costs about 0.4 ms per statement, and `main_loop2` must be checked a `match` at a time (its windows start at a top-level statement, their entry state a short prefix's, recomputed, not printed) with `Check`'s forcing discipline (`seq`), as `Check` and `Align` already do for it.

Projection for the whole guest: the heap witness pass about three def-use passes (563k statements), the frame walk one pass over 443k instructions, the pairing as `Align` today (0.28 CPU-h with `AlignWin`), module overheads for about 150 check modules at 2 to 4 s: in all under 0.5 CPU-h, against about 8 CPU-h for the mode route today. Snapshots disappear: no check carries state across a cut. Cold build about 15.7 - 8 + 0.5, about 8 CPU-h, before the new hand proofs, every check module under 4 GB with `main_loop2` split. Generated data: witnesses (one short entry per read, about 95k entries, about 10k lines), signatures (today's `ModeSig` is 43,741 lines), one theorem per function per pack: about 100k lines against 4.15M, 40x down. Regen of this part: the Python inference over the core runs in seconds (the census, its first version, in 2 s after a 13 s parse), where today's `mode` step walks the whole guest in about 15 minutes.

Edit locality. A function's witness certificate, residual lemmas and B1 module read only its core and its callees' `HSig`; a change of its signature regenerates its callers' certificates, data only. The frame walk and the pairing read the `Bundle`, regenerated for every function laid out after the edit as today, with no hand proof involved.

## 5. Plan and risks

Milestones, each a green gate with its cold-build cost in the commit message:

1. **The interface and the leaves** (about 2,500 lines). `FrameSpec` and `inv_rule_of_specs` (refactor of `Mode/Inv*`, the old walk its first instance, `openGaps` unchanged); `frameOk` and its soundness; `heapOk` for points with no call and no loop; `pairOk` for atoms and hints over `Align`; the checks run on the whole guest; `ModeHyps` per function from either route. Discharges the 286 functions with no call and no loop whose reads are covered or point preconditions (of 421); their callers stay on the old walk against the translated signatures.
2. **Calls, dispatch and returned words** (about 1,200 lines and the Python inference ported from `infer.py`): `HSig` with returned-word guarantees. Moves the 210 strict functions with calls and no loop and the callee-returned class, the 11 `open_stacked` above all, which deletes 1.0M snapshot lines.
3. **Loops** (about 1,000 lines): runs, chained facts, `term`, `retStay` on names: the 1,280 functions whose reads are points or runs.
4. **Residual families on names** (the `EndExecR*` mathematics restated, about 6,000 lines, and `rules_fix.py`'s rules ported): pointer tables and table index bounds (`verify_tables`, `check_opening_terminal`, the claim lists, `block_selector_tab`, `keccak_layer`, `rs_eq_run`, `column_selector`, DA rows), which removes the last 2.8M snapshot lines.
5. **Delete the old route**: `Pack/*/Mode*`, `Mode/{Abs,Sem,Win,Res*,Certs*,Firewall}` and the heap parts of `Mode/Sound*`, `Res/`, `EndExecR*`, `Bridge/AlignWin`, `scripts/mode-cert`, `scripts/res-cert`; `regen-guest.sh`'s `mode` step becomes `core-mode`.

Ordering by cost rather than by shape is also sound: after 1, take `open_stacked` (2), then `verify_tables` and `check_opening_terminal` (3 and 4 for them alone); that reaches the 10x line target with the old walk still checking about 1,500 small functions.

Risks. The residual count after porting the rules is the dominant unknown: the quick domain leaves 4,618 pointer-table and 2,633 table-index reads before any rule, today's walk 1,327 residuals with about 30 rules, and the families coincide; a family the core names cannot state better than offsets would make no gain there. Generalizing `Mode/Inv*` touches proved code (medium). `Align`'s proofs know flow hints only; heap events and shared cells (23,219 reads paired with an earlier `DEREF`) need a rule each (medium). The frame walk must keep what `Abs`'s frame part does today: back-solved divisors nonzero (5 `nz` residuals), the range-check and `assert !=` gadgets, callee frame cells, `__jump_tables`' prologue (low, it is a subset). `main_loop2`'s kernel memory needs windows and forcing (low, done before). The `Bundle`'s absolute pcs keep data regeneration global (accepted; a relocatable `Bundle` is the follow-up if the data must be local too).

## 6. What the core route's data reads (edit locality)

The core route reads none of the mode walk's data: each function's signature is the core route's (`Fn.«k».csig : Mode.Sig`, `Guest/CoreMode/Sig/<pack>`, written by `scripts/core-mode/sigc.py`), which the mode walk's certificates of the functions off the route name too: a routed function keeps its signature as written, its contract, checked against the frame layout and held by the route's checks to its heap signature, so it changes only when its contract does; a function off the route, or one whose frame layout changed, takes the mode walk's inference's (`MODE_CERT_CACHE`). The frame walks' facts come from the code (`scripts/core-mode/compiled.py`: frame signatures by the frame layout, a loop's self cell from its code) and, for a routed function, its oracle and stores from its pairing and its residual divisors from its own walk (`frame_run.own_nz`), so neither `sigc.py` nor `frame_gen.py` reads the mode walk for a routed function; a routed function's frame interface data (`envC`, its callees' signatures by key through `CoreMode.sigTrie`; `funC`, its entry, length, signature and nonzero residuals) sits beside its frame walk. Absolute pcs and the global index `j` appear in the core route's data only through glue: `GlueE/<pack>` (`Fn.«k».entry`, its entry pc, which `csig`, `funC`, the frame walk and its cut states and table calls name: return addresses as `entry + d`, callees as their keys' entries), `GlueP/<pack>` (each function's powers of `g` its code names, code pointers among them), `GlueA`/`GlueC` (its advice and index; its code the program's, and `tie`, the program's tables at its index its data, which `Gen/*/Route` cites, naming the function by its key and its index only as `Fn.«k».idx`) and `GlueG` (the jump table's end, which a heap certificate whose run it is names as `CoreMode.jtHi`). The certificates (`Gen/*/Cert`, `Gen/Certs/Sig*`) list a function's callee signatures in its environment's order, by entry, never in its signature trie's (`sigsOr_of_list`), whose order moves with the entries' bits, and group packs by a fixed count. A one-function edit then rewrites only that function's data and the glue in the core route; the kernel still rechecks every function laid out after the edit (its frame walk reads the bundle's code, whose code pointers are absolute: the relocatable bundle is the follow-up).
