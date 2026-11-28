module

public import LeanVM.Guest.Complete.MainWinGen
public import LeanVM.Guest.B1.Main.AggBody
public import LeanVM.Guest.B1.VsC.VsWins
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Complete.MainCalleesA
import LeanVM.Guest.CoreRef

/-!
# `aggregate_claims`' body in windows

`aggP` (the body before its `ret []`, `agg_shape`) is straight: eleven windows (`wAgg`), runs of atoms
between the guarded loops `aggregate_claims_loop{0,1,2,3}` and the call of `batch_sumcheck__L25`. Its
temporaries read per memory are the inlined grind's six range checks' (`aTL`). The kernel checks
`flatW1 wAgg = aggP`, `winsOkT aTL wAgg` and the evaluation's pattern (`chk_aggP`).

`aVal rd0 o args`: the forward valuation of `aggP` from the arguments, the loads read on `rd0`, the
hints, allocations and the sumcheck's returns from the oracle `o`. `agg_seg`: from the windows'
hypotheses (`WinsHypT`) the body is a window on `over aTL (aVal rd0 o args)`.

`AggWinHyp`: an evaluation memory, an oracle and the node's own words, with the windows' hypotheses
from the cursor `c` and the final condition giving `Post`. `agg_callAtA_of_hyp`: the placed call from it, and
`atEvery_agg_of_hyp` the `AtEvery` form `MainCalleesAt.agg` takes. `AggFieldHyp al k`: what is left of
the field, `AggWinHyp` on every inner node at `main`'s honest arguments, at every position past `mLo`;
`agg_field_of_hyp` gives the field from it.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.B1.Main LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The inlined grind's temporaries: each range check's two, with the value whose word it reads. -/
def aTL : List (V × V) :=
  [(.n 99, .n 96), (.n 100, .n 98), (.n 105, .n 95), (.n 106, .n 104), (.n 114, .n 94), (.n 115, .n 113),
    (.n 123, .n 93), (.n 124, .n 122), (.n 132, .n 92), (.n 133, .n 131), (.n 141, .n 91), (.n 142, .n 140)]

/-- Statements `0 ..< 42`: the buffers `bc_msgs`, `fresh_row`, `carried_row`, `absorb`, the hints, row `0`. -/
noncomputable def aW0 : W1 := .run (atomsOf ((aggP.drop 0).take 42))

/-- Statement `42`: `aggregate_claims_loop0` (`agg_loop0_callAtA`). -/
def aW1 : W1 := .cif (.n 32) "__loop0_aggregate_claims" [.n 33, .n 0, .n 30, .n 2, .n 8, .n 3, .n 9, .n 1]

/-- Statements `43 ..< 476`: the last row's and the nonce's permutations, the grind, `λ`, the squeezes,
`eqtree`, `fresh_val`. -/
noncomputable def aW2 : W1 := .run (atomsOf ((aggP.drop 43).take 433))

/-- Statement `476`: `aggregate_claims_loop1` (`agg_loop1_callAtA`). -/
def aW3 : W1 := .cif (.n 442) "__loop1_aggregate_claims" [.n 443, .n 0, .n 8, .n 445, .n 440]

/-- Statements `477 ..< 488`: `bc_chain` and its record `0`. -/
noncomputable def aW4 : W1 := .run (atomsOf ((aggP.drop 477).take 11))

/-- Statement `488`: `aggregate_claims_loop2` (`agg_loop2_callAtA`). -/
def aW5 : W1 := .cif (.n 453) "__loop2_aggregate_claims" [.n 454, .n 0, .n 449, .n 8, .n 9, .n 155, .n 440, .n 78]

/-- Statements `489 ..< 495`: the last record's claim, `bc_point`. -/
noncomputable def aW6 : W1 := .run (atomsOf ((aggP.drop 489).take 6))

/-- Statement `495`: `batch_sumcheck__L25` (`agg_bs_callCompletesA`). -/
def aW7 : W1 := .call (.call "batch_sumcheck__L25" [.n 230, .n 231, .n 232, .n 233, .n 234, .n 460, .n 457, .n 458, .n 5]
  [.n 461, .n 462, .n 463, .n 464, .n 465, .n 466])

/-- Statements `496 ..< 628`: `bc_point1`, `eq_cols`, `bc_wsum` and its record `0`. -/
noncomputable def aW8 : W1 := .run (atomsOf ((aggP.drop 496).take 132))

/-- Statement `628`: `aggregate_claims_loop3` (`agg_loop3_callAtA`). -/
def aW9 : W1 := .cif (.n 571) "__loop3_aggregate_claims" [.n 572, .n 0, .n 8, .n 9, .n 467, .n 449, .n 568, .n 565, .n 78]

/-- Statements `629 ..< 684`: the final check, the claim written at `defer_stmt`. -/
noncomputable def aW10 : W1 := .run (atomsOf ((aggP.drop 629).take 55))

/-- `aggregate_claims`' windows. -/
noncomputable def wAgg : List W1 := [aW0, aW1, aW2, aW3, aW4, aW5, aW6, aW7, aW8, aW9, aW10]

set_option maxRecDepth 200000 in
theorem wAgg_flat : flatW1 wAgg = aggP := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem wAgg_ok : winsOkT aTL wAgg = true := by decide +kernel

set_option maxRecDepth 200000 in
/-- The values `aggregate_claims`' body defines: `.n 6 ..< 601`, after its six parameters. -/
theorem chk_aggP : chk 6 aggP = some 601 := by decide +kernel

theorem agg_params : (fn% «aggregate_claims»).params = (List.range 6).map V.n := rfl

theorem find_agg : coreProgram.find? "aggregate_claims" = some fn% «aggregate_claims» :=
  coreProgram_find?_at (j := idx% «aggregate_claims») rfl

theorem agg_not_loop : coreProgram.loop "aggregate_claims" = false := by decide +kernel

/-! ## The forward valuation -/

/-- **`aggregate_claims`' forward valuation**: from the arguments `args`, its loads on `rd0`, its oracle
values from `o`. -/
noncomputable def aVal (rd0 : Reader) (o : ℕ → E) (args : List E) : Val := B1.Val.ofArgs (ev rd0 o args aggP)

section
variable {rd0 : Reader} {o : ℕ → E} {args : List E}

theorem aVal_good (hl : args.length = 6) : ∀ s ∈ aggP, GoodS rd0 (storesOf 6 aggP) o (aVal rd0 o args) s := by
  have := (ev_spec rd0 o aggP args (c' := 601) (by rw [hl]; exact chk_aggP)).2.2
  rwa [hl] at this

theorem aVal_param (hl : args.length = 6) {i : ℕ} (hi : i < 6) : aVal rd0 o args (.n i) = args.getD i 0 :=
  ev_params rd0 o (by rw [hl]; exact chk_aggP) (by omega)

end

/-! ## The windows composed -/

/-- **`aggregate_claims`' body before its `ret []` is a window** from its windows' hypotheses. -/
theorem agg_seg {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k fp : ℕ} {rd0 : Reader}
    {o : ℕ → E} {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop} {st : St} {K : St → Prop}
    (hl : args.length = 6) (h : WinsHypT fs al cert k (aVal rd0 o args) o Own R Pre wAgg st K) :
    SegT fs al cert k aTL "aggregate_claims" fp (aVal rd0 o args) Own R Pre aggP st K := by
  have g : ∀ x ∈ atomsW1 wAgg, ∃ S, Good rd0 S o (aVal rd0 o args) x := fun x hx => by
    have hm := mem_atomsW1 hx
    rw [wAgg_flat] at hm
    exact ⟨_, aVal_good hl (.atom x) hm⟩
  have := segA_winsT (T := aTL) (f := "aggregate_claims") (fp := fp) wAgg st K wAgg_ok g h
  rwa [wAgg_flat] at this

/-- `aggregate_claims`' events on `σ0` before its `ret []`. -/
noncomputable def aEs (σ0 : Val) : List Ev := outEvs (walk σ0 aggP)

/-- The state `aggregate_claims`' windows start from: its `HeapBuf`s from the cursor `c`, its callees
from their end, its own words `Wo` held, no data claimed, no callee yet. -/
noncomputable def aSt0 (σ0 : Val) (Wo : Words) (c : ℕ) : St :=
  ⟨c, c + (allocs σ0 (aEs σ0)).sum, fun rd => HoldsWords rd Wo, fun _ => False, []⟩

/-- `aggregate_claims`' final condition on the state after its windows, its valuation `σ0`: on every
memory, every callees' trees valid with their posts give `Post` of the node. -/
def AggK (k : ℕ) (Pre : Reader → Prop) (Post : Reader → Tree → Prop) (σ0 : Val) (st : St) : Prop :=
  ∀ rd, LowDef k rd → Pre rd → st.O rd → ∀ ts,
    Tree.KidsValid coreProgram rd (over aTL σ0 rd) (calls (aEs σ0)) ts →
    KidsPost rd st.Qs (calls (aEs σ0)) ts →
    Post rd (.node "aggregate_claims" (over aTL σ0 rd) (allocs σ0 (aEs σ0)) ts)

/-- **What is left of `aggregate_claims` placed** at frame `fp` and cursor `c`: an evaluation memory
`rd0`, an oracle `o` and its own words `Wo`, its windows' hypotheses on `aVal rd0 o args` from `aSt0`,
ending where the callees' posts give `Post`, within `2^40` of its cursor below `2^60`. -/
def AggWinHyp (al : String → Bool) (k : ℕ) (args : List E) (R : ℕ → Prop) (Pre : Reader → Prop)
    (Post : Reader → Tree → Prop) (fp c : ℕ) : Prop :=
  ∃ (rd0 : Reader) (o : ℕ → E) (Wo : Words),
    WordsInA Wo (fp + 2) (fp + B2C.fs "aggregate_claims") c
      (c + (allocs (aVal rd0 o args) (aEs (aVal rd0 o args))).sum) ∧
    WinsHypT B2C.fs al B2C.cert k (aVal rd0 o args) o
      (ownData B2C.cert fp c "aggregate_claims" (allocs (aVal rd0 o args) (aEs (aVal rd0 o args)))
        (aEs (aVal rd0 o args))) R Pre wAgg (aSt0 (aVal rd0 o args) Wo c)
      (fun st => (c < 2 ^ 60 → st.kc ≤ c + 2 ^ 40) ∧ AggK k Pre Post (aVal rd0 o args) st)

theorem aTL_params : ∀ i < 6, aTL.lookup (.n i) = none := by decide +kernel

/-- **`aggregate_claims` placed, from its windows' hypotheses.** -/
theorem agg_callAtA_of_hyp {al : String → Bool} {k : ℕ} {args : List E} {R : ℕ → Prop} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c : ℕ} (hl : args.length = 6) (hfc : fp + B2C.fs "aggregate_claims" ≤ c)
    (h : AggWinHyp al k args R Pre Post fp c) :
    ∃ e, (c < 2 ^ 60 → e ≤ c + 2 ^ 40) ∧
      CallAtA B2C.fs al B2C.cert k "aggregate_claims" args [] R (fun _ => False) (fun _ => True) Pre Post
        (B2C.fs "aggregate_claims") fp c e := by
  obtain ⟨rd0, o, Wo, hWo, hH⟩ := h
  set σ0 := aVal rd0 o args with hσ0
  obtain ⟨es, st', Qs, hw, hq, hseg, -, hB, hK⟩ := agg_seg (fp := fp) hl hH
  have hes : aEs σ0 = es := congrArg outEvs hw
  have hq' : st'.Qs = Qs := by rw [hq]; rfl
  have ha' : st'.a = c + (allocs σ0 es).sum := hseg.1
  have e0 : (aSt0 σ0 Wo c).kc = c + (allocs σ0 es).sum := by
    show c + (allocs _ (aEs _)).sum = _
    rw [hes]
  unfold AggK at hK
  rw [hes] at hWo hK
  refine ⟨st'.kc, hB, callAtA_segRd agg_not_loop hfc find_agg (agg_shape) σ0 (over aTL σ0) es Wo Qs st'.O st'.D
    hWo (fun _ h => h.elim) ?_ (fun _ _ => trivial) (fun rd _ _ _ => ⟨?_, rfl⟩) ?_⟩
  · rw [hes, ha', e0] at hseg
    exact hseg
  · rw [agg_params]
    refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [over_eq (aTL_params i h1), hσ0, aVal_param hl h1, List.getD_eq_getElem _ _ h2]
  · intro rd hl' hp ho ts hv hk
    rw [← hq'] at hk
    exact hK rd hl' hp ho ts hv hk

/-- **`aggregate_claims` at every position past `lo`**, from its windows' hypotheses there. -/
theorem atEvery_agg_of_hyp {al : String → Bool} {k : ℕ} {args : List E} {R : ℕ → Prop} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {lo : ℕ} (hl : args.length = 6)
    (h : ∀ fp c, lo ≤ fp → fp + B2C.fs "aggregate_claims" ≤ c → AggWinHyp al k args R Pre Post fp c) :
    AtEveryB al k "aggregate_claims" args [] R Pre Post (B2C.fs "aggregate_claims") lo (2 ^ 60) (2 ^ 40) :=
  fun fp c hlo hfc => agg_callAtA_of_hyp hl hfc (h fp c hlo hfc)

/-- `main`'s arguments to `aggregate_claims` (`MainCalleesAt.agg`): the children's count, `child_pi`,
`child_fresh`, `child_carried`, `defer_stmt`, the window tables. -/
noncomputable def aggArgs (al : String → Bool) (m : MainCounts) : List E :=
  [gen ^ m.nc, mPtr m 5 0, mPtr m 6 0, mPtr m 7 0, mPtr m 9 0, ptrAt (mGS al m + winTabAt)]

/-- **What is left of `MainCalleesAt.agg`**: on every inner node `MainCalleesA.callees` covers and every
coverage table, `aggregate_claims`' windows' hypotheses at `main`'s arguments, at every frame past
`mLo` and cursor past its frame. -/
def AggFieldHyp (al : String → Bool) (k : ℕ) : Prop :=
  ∀ (s : NodeStatement) (w : NodeWitness) (cover : List E), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w → w.children ≠ [] →
    cover.length = (mainCounts s w).sx + (mainCounts s w).ss →
    ∀ fp c, mLo al (mainCounts s w) ≤ fp → fp + B2C.fs "aggregate_claims" ≤ c →
      AggWinHyp al k (aggArgs al (mainCounts s w)) (mainR al (mainCounts s w)) (MainPreA al s w cover)
        (PopsPost (Prover.batchPushes w.batchingHints)) fp c

/-- **The field `agg` of `MainCalleesAt`**, from `AggFieldHyp`. -/
theorem agg_field_of_hyp {al : String → Bool} {k : ℕ} (H : AggFieldHyp al k) {s : NodeStatement}
    {w : NodeWitness} {cover : List E} (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hcv : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) (hne : w.children ≠ []) :
    AtEveryB al k "aggregate_claims"
      [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
        mPtr (mainCounts s w) 9 0, ptrAt (mGS al (mainCounts s w) + winTabAt)] []
      (mainR al (mainCounts s w)) (MainPreA al s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
      (B2C.fs "aggregate_claims") (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40) :=
  atEvery_agg_of_hyp rfl fun fp c hlo hfc => H s w cover hr hd hok hne hcv fp c hlo hfc

end
end LeanVM.Guest.Complete.Agg
