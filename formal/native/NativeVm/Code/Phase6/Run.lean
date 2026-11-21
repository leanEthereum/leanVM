module

public import NativeVm.Code.Phase6.First
public import NativeVm.Code.Phase6.Tail
public import NativeVm.Code.Phase6.Out

/-!
# Phase 6 assembled

`runC`, after the scratch's setup: `KECCAK`'s evaluations copied in, the segment and lane
challenges, the committed outputs' claim, the first claim, the layers, the tail, then the results
written (`wkoC`, `wclC`). `run_refines`: it refines `verifyKeccak` (as `headM`), ending with
`KeccakOutAt` and the column claims appended, every word outside phase 6's regions kept.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wdisp Env wd_inj)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

theorem kept_all {s : QState} (h : Kept env rs6 s0 s) : Kept env rsAll s0 s :=
  h.mono fun r hr ↦ by simp only [rs6, List.mem_cons, List.not_mem_nil, or_false] at hr; simp [rsAll, hr]

/-- A word of a region is no word of a region apart from it. -/
theorem not_in_apart (hin : Inputs env inp s0.mem) {q r : Region} (hq : q ∈ regions)
    (hr : r ∈ regions) (hap : q.Apart r) {k : Nat} (hk : k < q.size) :
    ¬ r.In env.work (wd env.work (q.off + k)) := by
  rintro ⟨j, hj, e⟩
  have hl := workWords_lt hin
  have h1 := stop_le_of_mem hq inp.bytecode.size
  have h2 := stop_le_of_mem hr inp.bytecode.size
  unfold Region.stop at h1 h2
  have := (wd_inj (by omega) (by omega)).mp e
  unfold Region.Apart Region.stop at hap
  omega

theorem same_of_frame (hin : Inputs env inp s0.mem) {q r : Region} (hq : q ∈ regions)
    (hr : r ∈ regions) (hap : q.Apart r) {m m' : UInt64 → Option UInt64}
    (h : ∀ a, ¬ r.In env.work a → m' a = m a) : Same m m' (q.at env.work) q.size := fun k hk ↦ by
  rw [Region.at, wd_wd]
  exact h _ (not_in_apart hin hq hr hap hk)

theorem claimsR_size' : claimsR.size = claimsWords := rfl
theorem keccakR_size' : keccakR.size = keccakWords := rfl

/-- **The results written**: `q_keccak`'s point and slices, then the committed outputs' claim. -/
theorem end_spec (hin : Inputs env inp s0.mem) {pb : Nat} {inst : Array EW} {claim : KeccakClaimW}
    {r : Array ColumnClaimW × Array EW × Array EW} {acc : Array ColumnClaimW}
    (h : St env s0 g t s) (hp : TPost g pb inst claim r)
    (hcl : ClaimsAt s.mem (claimsR.at env.work) acc) (hacc : acc.size < claimCap) :
    WP (blk [blk wkoC, blk (wclC eSegPt eComm)]) s (fun s' ↦ CodeRel env t s' ∧
      KeccakOutAt s'.mem (keccakR.at env.work) r.2.1 r.2.2 ∧
      ClaimsAt s'.mem (claimsR.at env.work) (acc ++ r.1) ∧ Kept env rsAll s0 s') fun _ ↦ False := by
  obtain ⟨low, slot1, slot2, word, hw⟩ := hp
  have hr := hw.eq
  refine WP.blk_cons (WP.mono (wko_spec hin (low := low) (pt := claim.point) (slot := slot2)
    (slices := r.2.2) (pb := pb) h.toA hw.lowSize hw.lowG hw.ptSize hw.ptN hw.pt hw.pbW hw.pbLe
    hw.slot2Size hw.slot2G hw.slSize hw.slG) (fun s1 ⟨h1, ko1, f1⟩ ↦ ?_) (fun _ h ↦ h))
  have hcl1 : ClaimsAt s1.mem (claimsR.at env.work) acc :=
    hcl.congr (by
      have := same_of_frame hin (q := claimsR) (r := keccakR) (by simp [regions])
        (by simp [regions]) (by decide) f1
      rwa [claimsR_size'] at this)
  refine WP.blk_cons (WP.mono (wcl_spec hin (so := eSegPt) (vo := eComm) (by p6_omega)
    (by p6_omega) (inst := inst) (slot := slot1) (word := word) h1 hcl1 hacc hw.instSize hw.instN
    hw.instG hw.slot1Size hw.slot1G hw.wordG) (fun s2 ⟨h2, cl2, f2⟩ ↦ WP.blk_nil ?_) (fun _ h ↦ h))
  refine ⟨h2.1, ?_, ?_, h2.2.1.1⟩
  · have ko2 := ko1.congr (by
      have := same_of_frame hin (q := keccakR) (r := claimsR) (by simp [regions])
        (by simp [regions]) (by decide) f2
      rwa [keccakR_size'] at this)
    rw [hr] at ko2 ⊢
    exact ko2
  · rw [hr]
    exact cl2

/-! ## The run -/

theorem keccakPhase_eq (layout : LayoutW) (ev : Array (Array EW × Array EW)) :
    Model.keccakPhase layout ev = verifyKeccak (layout.tableLogHeights.getD opKeccak 0)
      (ev.getD opKeccak (#[], #[])).1
      ((Array.range 25).map fun lane ↦ (ev.getD opKeccak (#[], #[])).2.getD (keccakOut + lane) 0) := by
  unfold Model.keccakPhase
  cases ev.getD opKeccak (#[], #[])
  rfl

/-- Phase 6 after the scratch's setup. -/
def runC : List Stmt := [blk copyC, smpN eSegPt 1, smpN eLanePt 5, rdEl eComm, blk firstC, layersC,
  blk tailC, blk wkoC, blk (wclC eSegPt eComm)]

/-- The claims survive a run that writes only the scratch. -/
theorem claims_kept (hin : Inputs env inp s0.mem) {acc : Array ColumnClaimW}
    (hcl : ClaimsAt s0.mem (claimsR.at env.work) acc) (hk : Kept env rs6 s0 s) :
    ClaimsAt s.mem (claimsR.at env.work) acc :=
  hcl.congr (by
    have := hk.same hin (fun r hr ↦ stop_le_of_mem (by
        simp only [rs6, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        simp [regions]) _) (q := claimsR) (by simp [regions])
      (fun r hr ↦ by simp only [rs6, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; decide)
    rwa [claimsR_size'] at this)

variable (env inp s0)

/-- **Phase 6 after the setup** against `keccakPhase`. -/
theorem run_refines (hin : Inputs env inp s0.mem) {layout : LayoutW} {rate : Nat}
    {ev : Array (Array EW × Array EW)} {acc : Array ColumnClaimW}
    (hlay : LayoutAt s0.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hev : EvalsAt s0.mem (evalsR.at env.work) ev)
    (hcl : ClaimsAt s0.mem (claimsR.at env.work) acc) (hacc : acc.size < claimCap)
    (g0 : Nat → EW) (hcn : Cn g0) :
    Refines (St env s0 g0) (blk runC) (Model.keccakPhase layout ev)
      (fun r t s ↦ CodeRel env t s ∧ (KeccakOutAt s.mem (keccakR.at env.work) r.2.1 r.2.2 ∧
        ClaimsAt s.mem (claimsR.at env.work) (acc ++ r.1) ∧ r.1.size ≤ keccakClaimCount) ∧
        Kept env rsAll s0 s) (Kept env rs6 s0) := by
  rw [keccakPhase_eq, verifyKeccak_eq]
  set inst := (ev.getD opKeccak (#[], #[])).1 with hinst
  set output := (Array.range 25).map fun lane ↦ (ev.getD opKeccak (#[], #[])).2.getD (keccakOut + lane) 0
    with houtput
  set logSteps := layout.tableLogHeights.getD opKeccak 0 with hlog
  unfold headM runC
  obtain ⟨g1, p1, k1, hisz, hiN, hiG, hout, hls, hpbW⟩ := pure_copy hin hlay hev g0
  have hisz' : inst.size ≤ 30 := hisz
  have cn1 : Cn g1 := hcn.congr fun i h1 h2 ↦ k1 i (by unfold CopyW; p6_omega)
  refine Pure6.then p1 ?_
  refine Refines.blk_cons (smpN_refines env inp s0 hin (o := eSegPt) (n := 1) (by p6_omega)
    (by norm_num) g1) fun seg ↦ Refines.intro fun hseg ↦ ?_
  have k2 : ∀ i, ¬ (eSegPt ≤ i ∧ i < eSegPt + 1) → wrA g1 eSegPt seg i = g1 i := fun i hi ↦
    wrA_out (by rw [hseg]; omega)
  refine Refines.blk_cons (smpN_refines env inp s0 hin (o := eLanePt) (n := 5) (by p6_omega)
    (by norm_num) (wrA g1 eSegPt seg)) fun lp ↦ Refines.intro fun hlp ↦ ?_
  set g3 := wrA (wrA g1 eSegPt seg) eLanePt lp with hg3
  have k3 : ∀ i, ¬ (eLanePt ≤ i ∧ i < eLanePt + 5) → g3 i = wrA g1 eSegPt seg i := fun i hi ↦
    wrA_out (by rw [hlp]; omega)
  refine Refines.blk_cons (rdEl_refines env inp s0 hin (o := eComm) (by p6_omega) g3)
    fun committed ↦ ?_
  set g4 := Function.update g3 eComm committed with hg4
  have k14 : ∀ i, i ≠ eComm → ¬ (eLanePt ≤ i ∧ i < eLanePt + 5) → ¬ (eSegPt ≤ i ∧ i < eSegPt + 1) →
      g4 i = g1 i := fun i h1 h2 h3 ↦ by
    rw [hg4, Function.update_of_ne h1, k3 i h2, k2 i h3]
  have cn4 : Cn g4 := cn1.congr fun i h1 h2 ↦ k14 i (by p6_omega) (by p6_omega) (by p6_omega)
  obtain ⟨g5, p5, c5, wf5, sn5, sw5, k5⟩ := pure_first hin (g := g4) cn4 (inst := inst)
    (output := output) (segment := seg) (lanePoint := lp) (committed := committed)
    (pb := logSteps - 4) hisz
    ((k14 _ (by p6_ne) (by p6_omega) (by p6_omega)).trans hiN)
    (fun i hi ↦ (k14 _ (by p6_omega) (by p6_omega) (by p6_omega)).trans (hiG i hi))
    (by simp [houtput])
    (fun l hl ↦ by
      rw [k14 _ (by p6_omega) (by p6_omega) (by p6_omega), hout l hl, houtput,
        getD_map_range _ _ _ hl])
    hseg
    (by rw [hg4, Function.update_of_ne (by p6_ne), k3 _ (by p6_omega)]
        exact wrA_in (o := eSegPt) (i := 0) (by omega))
    hlp
    (fun i hi ↦ by
      rw [hg4, Function.update_of_ne (by p6_omega)]
      exact wrA_in (o := eLanePt) (by omega))
    (Function.update_self ..)
    ((k14 _ (by p6_ne) (by p6_omega) (by p6_omega)).trans hpbW) (by omega)
  set first := keccakFirstClaim inst seg lp output committed with hfirst
  have k15 : ∀ i, ¬ FirstW i → i ≠ eComm → ¬ (eLanePt ≤ i ∧ i < eLanePt + 5) →
      ¬ (eSegPt ≤ i ∧ i < eSegPt + 1) → g5 i = g1 i := fun i h0 h1 h2 h3 ↦
    (k5 i h0).trans (k14 i h1 h2 h3)
  have cn5 : Cn g5 := cn1.congr fun i h1 h2 ↦
    k15 i (by unfold FirstW LW; p6_omega) (by p6_omega) (by p6_omega) (by p6_omega)
  refine Pure6.then p5 ?_
  refine Refines.blk_cons (layers_refines env inp s0 hin (logSteps := logSteps) g5 c5 cn5
    ((k15 _ (by unfold FirstW LW; p6_omega) (by p6_ne) (by p6_omega) (by p6_omega)).trans hpbW)
    (by omega) sn5) fun claim ↦ Refines.exSt fun g6 hl ↦ ?_
  have k56 : ∀ i, ¬ LW i → i ≠ eStep → g6 i = g5 i := hl.fr
  have hpre : TPre g6 (logSteps - 4) inst first claim committed := {
    cl := hl.claim
    muSize := hl.muSize.resolve_left (by decide)
    pbW := (k56 _ (by unfold LW; p6_omega) (by p6_ne)).trans
      ((k15 _ (by unfold FirstW LW; p6_omega) (by p6_ne) (by p6_omega) (by p6_omega)).trans hpbW)
    pbLe := by omega
    segN := by rw [k56 _ (by unfold LW; p6_omega) (by p6_ne), sn5, hl.ptSize]
    seg1 := fun k hk ↦ (k56 _ (by unfold LW; p6_omega) (by p6_omega)).trans (sw5 k hk)
    wf := fun j hj ↦ (k56 _ (by unfold LW; p6_omega) (by p6_omega)).trans (wf5 j hj)
    comm := by
      rw [k56 _ (by unfold LW; p6_omega) (by p6_ne), k5 _ (by unfold FirstW LW; p6_omega), hg4,
        Function.update_self]
    instSize := hisz
    instN := (k56 _ (by unfold LW; p6_omega) (by p6_ne)).trans
      ((k15 _ (by unfold FirstW LW; p6_omega) (by p6_ne) (by p6_omega) (by p6_omega)).trans hiN)
    instG := fun i hi ↦ (k56 _ (by have := hisz'; unfold LW; p6_omega) (by have := hisz'; p6_omega)).trans
      ((k15 _ (by have := hisz'; unfold FirstW LW; p6_omega) (by have := hisz'; p6_omega)
        (by have := hisz'; p6_omega) (by have := hisz'; p6_omega)).trans (hiG i hi)) }
  refine Refines.then_blk (tail_refines env inp s0 hin g6 hpre) fun r t s ⟨g7, h7, hp7⟩ ↦
    WP.mono (end_spec hin h7 hp7 (claims_kept hin hcl h7.2.1.1) hacc)
      (fun s' ⟨q1, q2, q3, q4⟩ ↦ ⟨q1, ⟨q2, q3, ?_⟩, q4⟩) (fun _ h ↦ h)
  obtain ⟨_, _, _, _, hw⟩ := hp7
  rw [hw.eq]
  exact Nat.le_refl _

end NativeVm.Code.P6
