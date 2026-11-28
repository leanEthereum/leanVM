/-
  LeanVM.Guest.B1.VsC.KLPlacedM

  **`keccak_layer` completes placed**: the node.
-/

module

public import LeanVM.Guest.B1.VsC.KLPlaced
public import LeanVM.Guest.B1.VsC.RstA
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# `keccak_layer`, placed: the node

`layer_placed`, as `KLPlaced` describes it.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

theorem sq_eq (D : LayerData) (first : ℕ) :
    layerSq (D.s0 first) D.product D.nonce = (D.sv first, ⟨D.capS first, []⟩) := by
  refine Prod.ext rfl (fs_eta ?_)
  unfold layerSq Fs.grindSqueeze
  split <;> simp [Fs.squeeze]

/-- A claim's record with its pointers is a claim's record. -/
theorem claimRec_of_at {rd : Reader} {first : Bool} {rec cpt clp clc cfl : E} {c : KeccakClaim} {y : ℕ}
    (h : VsC.ClaimRecAt rd first rec cpt clp clc cfl c y) : ClaimRec rd first rec c y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, lanes, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ⟨cpt, h6, h7⟩, clp, lanes, h8, h9, h10, ?_⟩
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte] at h11 ⊢
    obtain ⟨loc, a1, a2, a3, a4, a5, a6⟩ := h11
    exact ⟨clc, cfl, loc, a1, a2, a3, a4, a5, a6⟩
  · simpa using h11

/-- The claim's record's first words, as the weight section reads them. -/
theorem cw_of_at {rd : Reader} {first : ℕ} {rec cpt clp clc cfl : E} {c : KeccakClaim} {y : ℕ}
    (h : VsC.ClaimRecAt rd (first = 1) rec cpt clp clc cfl c y) :
    ∃ cw : List E, ReadsAt rd rec cw ∧ (if first = 1 then 4 else 5) ≤ cw.length ∧
      cw.getD 3 0 = clp := by
  obtain ⟨-, -, h3, h4, -, h6, -, lanes, h8, -, -, h11⟩ := h
  by_cases hf : first = 1
  · refine ⟨[c.value, sumE c.mu, cpt, clp], fun k hk ↦ ?_, by simp [hf], rfl⟩
    match k, hk with
    | 0, _ => exact h3
    | 1, _ => exact h4
    | 2, _ => exact h6
    | 3, _ => exact h8
  · simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte] at h11
    obtain ⟨loc, a1, -⟩ := h11
    refine ⟨[c.value, sumE c.mu, cpt, clp, clc], fun k hk ↦ ?_, by simp [hf], rfl⟩
    match k, hk with
    | 0, _ => exact h3
    | 1, _ => exact h4
    | 2, _ => exact h6
    | 3, _ => exact h8
    | 4, _ => exact a1

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The two dispatched callees' end, from the cursor `cur0`. -/
def layerEnd (fs : String → ℕ) (al : String → Bool) (D : LayerData) (cur0 : ℕ) : ℕ :=
  allocBase (al (remNames.getD (D.y % krStep) ""))
    (allocBase (al (stepNames.getD (D.y / krStep) "")) cur0 + fs (stepNames.getD (D.y / krStep) "")) +
    fs (remNames.getD (D.y % krStep) "")

set_option maxHeartbeats 1000000 in
/-- **The layer's two callees complete one after the other**, from the cursor `cur0`. -/
theorem layer_kids {k : ℕ} {first : ℕ} (D : LayerData) {cur cpt tb : E}
    {σ0 : Val} {R' : ℕ → Prop} {Pre : Reader → Prop} {Wo : Words} {cb cur0 : ℕ}
    (hy32 : D.y < 32) (hpm : D.packMsgs.length = D.y)
    (hA1 : (lA1 (preOff first)).map σ0 = D.capS first ++
      [cur * gen ^ 48, polyEval D.product (D.sv first), cpt, VsC.ptrAtV cb, tb])
    (hR1 : (lR1 (preOff first)).map σ0 = D.r1 first cur)
    (hA2 : (lA2 (preOff first)).map σ0 = D.r1 first cur ++
      [cpt * gen ^ D.n1, VsC.ptrAtV cb * gen ^ D.n1, tb])
    (hR2 : (lR2 (preOff first)).map σ0 = D.r2 first cur)
    (hK1 : VsC.KrRegion cpt (cur * gen ^ 48) (VsC.ptrAtV cb) (krStep * (D.y / krStep)) R')
    (hK2 : VsC.KrRegion (cpt * gen ^ D.n1) (cur * gen ^ 48 * gen ^ (2 * D.n1))
      (VsC.ptrAtV cb * gen ^ D.n1) (D.y % krStep) R')
    (hP1 : ∀ rd, Pre rd → HoldsWords rd Wo → VsC.KrPre cpt (cur * gen ^ 48) (VsC.ptrAtV cb)
      (polyEval D.product (D.sv first)) (D.capS first) (D.c.point.take D.n1) (D.packMsgs.take D.n1) rd)
    (hP2 : ∀ rd, Pre rd → HoldsWords rd Wo → VsC.KrPre (cpt * gen ^ D.n1)
      (cur * gen ^ 48 * gen ^ (2 * D.n1)) (VsC.ptrAtV cb * gen ^ D.n1) (D.run1 first).1.1
      (D.run1 first).2.cap (D.c.point.drop D.n1) (D.packMsgs.drop D.n1) rd) :
    KidsAtF fs al cert k σ0 R' Pre (fun rd => HoldsWords rd Wo) (fun _ => False) [VsC.PostQuiet, VsC.PostQuiet]
      [⟨stepNames.getD (D.y / krStep) "", lA1 (preOff first), lR1 (preOff first), true⟩,
        ⟨remNames.getD (D.y % krStep) "", lA2 (preOff first), lR2 (preOff first), true⟩] cur0
      (layerEnd fs al D cur0) (fun rd => (HoldsWords rd Wo ∧ True) ∧ True) (fun _ => False) := by
  have hj1 : D.y / krStep < 2 := by unfold krStep; omega
  have hj2 : D.y % krStep < 16 := by unfold krStep; omega
  have hn1 : D.n1 ≤ D.y := LayerData.n1_le
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ := five_of_length' (LayerData.capS_ok (D := D) (first := first))
  obtain ⟨hrs, hrl⟩ := LayerData.run1_state (D := D) (first := first)
  obtain ⟨d0, d1, d2, d3, d4, hd⟩ := five_of_length' hrl
  have e1 := stepNames_lr hj1
  have e2 := remNames_lr hj2
  set g1 := stepNames.getD (D.y / krStep) "" with hg1
  set g2 := remNames.getD (D.y % krStep) "" with hg2
  have L1 := VsC.layer_rounds_placed (fs := fs) (al := al) (cert := cert) (k := k)
    (krStep * (D.y / krStep)) (by unfold krStep; omega)
    (f0 := c0) (f1 := c1) (f2 := c2) (f3 := c3) (f4 := c4) (cur := cur * gen ^ 48)
    (v := polyEval D.product (D.sv first)) (pp := cpt) (pt := VsC.ptrAtV cb) (tabs := tb)
    (rs := D.c.point.take D.n1) (ms := D.packMsgs.take D.n1)
    (by rw [List.length_take]; exact Nat.min_eq_left hn1)
    (by rw [List.length_take, hpm]; exact Nat.min_eq_left hn1) hK1
    (allocBase (al g1) cur0) (allocBase (al g1) cur0 + fs g1)
  have L2 := VsC.layer_rounds_placed (fs := fs) (al := al) (cert := cert) (k := k)
    (D.y % krStep) (by unfold krStep; omega)
    (f0 := d0) (f1 := d1) (f2 := d2) (f3 := d3) (f4 := d4) (cur := cur * gen ^ 48 * gen ^ (2 * D.n1))
    (v := (D.run1 first).1.1) (pp := cpt * gen ^ D.n1) (pt := VsC.ptrAtV cb * gen ^ D.n1) (tabs := tb)
    (rs := D.c.point.drop D.n1) (ms := D.packMsgs.drop D.n1)
    (by rw [List.length_drop]; unfold LayerData.n1 LayerData.y krStep; omega)
    (by rw [List.length_drop, hpm]; unfold LayerData.n1 krStep; omega) hK2
    (allocBase (al g2) (allocBase (al g1) cur0 + fs g1))
    (allocBase (al g2) (allocBase (al g1) cur0 + fs g1) + fs g2)
  rw [← e1] at L1
  rw [← e2] at L2
  have hr1W : VsC.lrRetsW (D.c.point.take D.n1) (D.packMsgs.take D.n1) (polyEval D.product (D.sv first))
      (cur * gen ^ 48) [c0, c1, c2, c3, c4] (krStep * (D.y / krStep)) = D.r1 first cur := by
    simp only [LayerData.r1, LayerData.run1, VsC.lrRetsW, hc]; rfl
  have hr2W : VsC.lrRetsW (D.c.point.drop D.n1) (D.packMsgs.drop D.n1) (D.run1 first).1.1
      (cur * gen ^ 48 * gen ^ (2 * D.n1)) [d0, d1, d2, d3, d4] (D.y % krStep) = D.r2 first cur := by
    have : D.run2 first = packRunF (D.c.point.drop D.n1) (D.packMsgs.drop D.n1) (D.run1 first).1.1
        ⟨[d0, d1, d2, d3, d4], []⟩ := by
      rw [LayerData.run2, hrs, hd]
    simp only [LayerData.r2, this, VsC.lrRetsW]
  rw [hr1W] at L1
  rw [hr2W] at L2
  simp only [KidsAtF, ↓reduceIte, List.headD_cons, List.tail_cons]
  refine ⟨fs g1, allocBase (al g1) cur0 + fs g1, R', fun _ => False, fun _ => True, fun i hi => Or.inl hi,
    ?_, fs g2, allocBase (al g2) (allocBase (al g1) cur0 + fs g1) + fs g2, R', fun _ => False,
    fun _ => True, fun i hi => Or.inl hi, ?_, rfl, fun rd h => h, fun i h => h.elim⟩
  · rw [hA1, hR1, hc]
    exact L1.mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
      (fun rd h => by have := hP1 rd h.1 h.2; rwa [hc] at this) (fun _ _ _ h => h)
  · rw [hA2, hR2]
    have hr1 : D.r1 first cur = [d0, d1, d2, d3, d4] ++ [cur * gen ^ 48 * gen ^ (2 * D.n1),
        (D.run1 first).1.1] := by rw [LayerData.r1, hd]
    rw [hr1]
    simp only [List.cons_append, List.nil_append]
    exact L2.mono (fun _ h => h) (fun _ h => h) (fun _ h => h)
      (fun rd h => by have := hP2 rd h.1 h.2.1; rwa [hd] at this) (fun _ _ _ h => h)

end
end LeanVM.Guest.B1.VerifySub.KL
