/-
  LeanVM.Guest.B1.Tables.VtCAir

  `verify_tables`' completeness: a table's constraint window, forward (`VtAirComplete`).
-/

module

public import LeanVM.Guest.B1.Tables.VtCAirI
public import LeanVM.Guest.B1.Tables.VerifyTablesCIface

/-!
# A table's constraint window, forward (G:1759-1770)

Each window (`vtcAir0` .. `vtcAir5`) is arithmetic but for its obligations: loads of `fp_w`, the
weight's `g^n / g^τ` (`τ`'s power nonzero) and its two loads `cprod[n - τ]`, `peq[τ]`, and the
next table's `g^τ` read from `dims`. `vtc_air_gen` completes a window of that shape (its
obligations classified by `vtcAirOk`, by kernel evaluation); `vt_air_complete`: `VtAirComplete`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- A constraint window's obligation: a load of `fp_w`, the power of `τ` nonzero, the weight's two
loads at `c` and `c + 2`, and (with `nxt`) the next table's `g^τ` from `dims` at `doff`. -/
def vtcAirOk (tv c doff : ℕ) (nxt : Bool) (o : IOb) : Bool :=
  (List.range 16).any (fun i => iobEqb o (.ob (.ld (.n 11) i))) || iobEqb o (.ob (.nz (.n tv))) ||
    iobEqb o (.ob (.ld (.n c) 0)) || iobEqb o (.ob (.ld (.n (c + 2)) 0)) ||
    (nxt && iobEqb o (.ob (.ld (.n 7) doff)))

/-- A window's definitions used: the weight's `g^(n - τ)`, its two pointers, the next `g^τ`. -/
def vtcAirEq (tv c : ℕ) : List FEq :=
  [.sv (.n (c - 1)) (.n 4554) (.n tv), .def (.mul (.n c) (.n 4639) (.n (c - 1))),
    .def (.mul (.n (c + 2)) (.n 4655) (.n tv))]

set_option maxHeartbeats 1000000 in
/-- **A constraint window completes**, on loads of `fp_w`, the weight's two cells and the next
`g^τ` that exist. -/
theorem vtc_air_gen {its : List FItem} {lo hi tv c doff tn : ℕ} {nxt : Bool}
    (hok : fOkI lo hi [] its = true) (hobs : (iObs lo [] its).all (vtcAirOk tv c doff nxt) = true)
    (heqs : (vtcAirEq tv c).all (fun e => (fEqs lo [] its).any (feqEqb e)) = true)
    (hnx : nxt = true → (fEqs lo [] its).any (feqEqb (.ld (.n tn) (.n 7) doff)) = true)
    (hlt : 4655 < lo ∧ tv < lo) {rd : Reader} {σ : Val} {fpw dims pC pP : E} {n τ : ℕ}
    (h11 : σ (.n 11) = fpw) (h7 : σ (.n 7) = dims) (h4639 : σ (.n 4639) = pC) (h4655 : σ (.n 4655) = pP)
    (h4554 : σ (.n 4554) = gen ^ n) (htv : σ (.n tv) = gen ^ τ) (hτn : τ ≤ n)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hC : ∃ v, LoadHolds rd pC (n - τ) v)
    (hP : ∃ v, LoadHolds rd pP τ v) (hD : nxt = true → ∃ v, LoadHolds rd dims doff v) :
    Completes (coreProgram.Rel rd) rd lo hi (its.flatMap FItem.stmts) σ (fun σ' =>
      nxt = true → ∀ v, LoadHolds rd dims doff v → σ' (.n tn) = v) := by
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (fun _ => 0) its hok σ
  generalize hσf : fRunI rd lo (fun _ => 0) [] σ its = σf at Cm
  have hf : ∀ u, fRunI rd lo (fun _ => 0) [] σ its u = σf u := fun u => by rw [hσf]
  have E := fRunI_eqs rd (fun _ => 0) σf its [] σ hok hf
  have FR : ∀ k < lo, σf (.n k) = σ (.n k) := fun k hk =>
    fRunI_eq_of_def rd _ hok hf (by simp [fDef, vNum, hk])
  have hB := heqs
  simp only [vtcAirEq, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hB
  have d1 : σf (.n (c - 1)) = σf (.n 4554) * (σf (.n tv))⁻¹ := E _ (mem_of_any feqEqb_sound hB.1)
  have d2 : σf (.n c) = σf (.n 4639) * σf (.n (c - 1)) := E _ (mem_of_any feqEqb_sound hB.2.1)
  have d3 : σf (.n (c + 2)) = σf (.n 4655) * σf (.n tv) := E _ (mem_of_any feqEqb_sound hB.2.2)
  have etv : σf (.n tv) = gen ^ τ := by rw [FR tv hlt.2, htv]
  have ex : σf (.n (c - 1)) = gen ^ (n - τ) := by
    rw [d1, FR 4554 (by omega), h4554, etv]; exact gen_pow_div hτn
  have ec : σf (.n c) = pC * gen ^ (n - τ) := by rw [d2, FR 4639 (by omega), h4639, ex]
  have ep : σf (.n (c + 2)) = pP * gen ^ τ := by rw [d3, FR 4655 (by omega), h4655, etv]
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · intro o ho
    have h := List.all_eq_true.mp hobs o ho
    simp only [vtcAirOk, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, List.mem_range] at h
    rcases h with (((⟨i, hi, he⟩ | he) | he) | he) | ⟨hn, he⟩ <;> obtain rfl := iobEqb_sound he
    · simp only [IOb.Holds, Ob.Holds]
      rw [FR 11 (by omega), h11]
      obtain ⟨w, hw⟩ := hfpw i hi
      exact ⟨hw.1, isSome_of_loadHolds hw⟩
    · simp only [IOb.Holds, Ob.Holds]; rw [etv]; exact gen_pow_ne_zero _
    · simp only [IOb.Holds, Ob.Holds]
      rw [ec]
      obtain ⟨w, hw⟩ := hC
      have := loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact hw)
      exact ⟨this.1, isSome_of_loadHolds this⟩
    · simp only [IOb.Holds, Ob.Holds]
      rw [ep]
      obtain ⟨w, hw⟩ := hP
      have := loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact hw)
      exact ⟨this.1, isSome_of_loadHolds this⟩
    · simp only [IOb.Holds, Ob.Holds]
      rw [FR 7 (by omega), h7]
      obtain ⟨w, hw⟩ := hD hn
      exact ⟨hw.1, isSome_of_loadHolds hw⟩
  · intro σ' h hn v hv
    rw [h]
    have : σf (.n tn) = memAt rd (σf (.n 7)) doff := E _ (mem_of_any feqEqb_sound (hnx hn))
    rw [this, FR 7 (by omega), h7, memAt_of_loadHolds hv]

/-! ## The six windows -/

set_option maxRecDepth 100000 in
theorem vtcAir0_ok : fOkI 4901 5149 [] vtcAir0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir0_obs : (iObs 4901 [] vtcAir0).all (vtcAirOk 4660 5142 2 true) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir0_eqs : (vtcAirEq 4660 5142).all (fun e => (fEqs 4901 [] vtcAir0).any (feqEqb e)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir0_nx : (fEqs 4901 [] vtcAir0).any (feqEqb (.ld (.n 5148) (.n 7) 2)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir1_ok : fOkI 5389 5678 [] vtcAir1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir1_obs : (iObs 5389 [] vtcAir1).all (vtcAirOk 5148 5670 3 true) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir1_eqs : (vtcAirEq 5148 5670).all (fun e => (fEqs 5389 [] vtcAir1).any (feqEqb e)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir1_nx : (fEqs 5389 [] vtcAir1).any (feqEqb (.ld (.n 5677) (.n 7) 3)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir2_ok : fOkI 5806 5955 [] vtcAir2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir2_obs : (iObs 5806 [] vtcAir2).all (vtcAirOk 5677 5947 4 true) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir2_eqs : (vtcAirEq 5677 5947).all (fun e => (fEqs 5806 [] vtcAir2).any (feqEqb e)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir2_nx : (fEqs 5806 [] vtcAir2).any (feqEqb (.ld (.n 5954) (.n 7) 4)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir3_ok : fOkI 6195 6478 [] vtcAir3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir3_obs : (iObs 6195 [] vtcAir3).all (vtcAirOk 5954 6470 5 true) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir3_eqs : (vtcAirEq 5954 6470).all (fun e => (fEqs 6195 [] vtcAir3).any (feqEqb e)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir3_nx : (fEqs 6195 [] vtcAir3).any (feqEqb (.ld (.n 6477) (.n 7) 5)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir4_ok : fOkI 6702 6980 [] vtcAir4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir4_obs : (iObs 6702 [] vtcAir4).all (vtcAirOk 6477 6972 6 true) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir4_eqs : (vtcAirEq 6477 6972).all (fun e => (fEqs 6702 [] vtcAir4).any (feqEqb e)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir4_nx : (fEqs 6702 [] vtcAir4).any (feqEqb (.ld (.n 6979) (.n 7) 6)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir5_ok : fOkI 7572 8140 [] vtcAir5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir5_obs : (iObs 7572 [] vtcAir5).all (vtcAirOk 6979 8133 0 false) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtcAir5_eqs : (vtcAirEq 6979 8133).all (fun e => (fEqs 7572 [] vtcAir5).any (feqEqb e)) = true := by
  decide +kernel

/-- **A table's constraint window completes** (G:1759-1770). -/
theorem vt_air_complete : VtAirComplete := by
  intro t ht rd σ fpw dims pC pP n τ h11 h7 h4639 h4655 h4554 htv hτn hfpw hC hP hD
  interval_cases t
  · rw [show (vtPre.drop (airA.getD 0 0)).take (airB.getD 0 0 - airA.getD 0 0) = (vtPre.drop 4615).take 248
      from rfl, ← vtcAir0_eq]
    exact (vtc_air_gen vtcAir0_ok vtcAir0_obs vtcAir0_eqs (fun _ => vtcAir0_nx) (by omega) h11 h7 h4639 h4655 h4554 htv hτn hfpw hC hP
      (fun _ => hD (by omega))).mono le_rfl le_rfl fun σ' h _ => h rfl
  · rw [show (vtPre.drop (airA.getD 1 0)).take (airB.getD 1 0 - airA.getD 1 0) = (vtPre.drop 5103).take 289
      from rfl, ← vtcAir1_eq]
    exact (vtc_air_gen vtcAir1_ok vtcAir1_obs vtcAir1_eqs (fun _ => vtcAir1_nx) (by omega) h11 h7 h4639 h4655 h4554 htv hτn hfpw hC hP
      (fun _ => hD (by omega))).mono le_rfl le_rfl fun σ' h _ => h rfl
  · rw [show (vtPre.drop (airA.getD 2 0)).take (airB.getD 2 0 - airA.getD 2 0) = (vtPre.drop 5520).take 149
      from rfl, ← vtcAir2_eq]
    exact (vtc_air_gen vtcAir2_ok vtcAir2_obs vtcAir2_eqs (fun _ => vtcAir2_nx) (by omega) h11 h7 h4639 h4655 h4554 htv hτn hfpw hC hP
      (fun _ => hD (by omega))).mono le_rfl le_rfl fun σ' h _ => h rfl
  · rw [show (vtPre.drop (airA.getD 3 0)).take (airB.getD 3 0 - airA.getD 3 0) = (vtPre.drop 5909).take 283
      from rfl, ← vtcAir3_eq]
    exact (vtc_air_gen vtcAir3_ok vtcAir3_obs vtcAir3_eqs (fun _ => vtcAir3_nx) (by omega) h11 h7 h4639 h4655 h4554 htv hτn hfpw hC hP
      (fun _ => hD (by omega))).mono le_rfl le_rfl fun σ' h _ => h rfl
  · rw [show (vtPre.drop (airA.getD 4 0)).take (airB.getD 4 0 - airA.getD 4 0) = (vtPre.drop 6416).take 278
      from rfl, ← vtcAir4_eq]
    exact (vtc_air_gen vtcAir4_ok vtcAir4_obs vtcAir4_eqs (fun _ => vtcAir4_nx) (by omega) h11 h7 h4639 h4655 h4554 htv hτn hfpw hC hP
      (fun _ => hD (by omega))).mono le_rfl le_rfl fun σ' h _ => h rfl
  · rw [show (vtPre.drop (airA.getD 5 0)).take (airB.getD 5 0 - airA.getD 5 0) = (vtPre.drop 7286).take 568
      from rfl, ← vtcAir5_eq]
    exact (vtc_air_gen (tn := 0) vtcAir5_ok vtcAir5_obs vtcAir5_eqs (fun h => absurd h (by decide)) (by omega) h11 h7 h4639 h4655
      h4554 htv hτn hfpw hC hP (fun h => absurd h (by decide))).mono le_rfl le_rfl fun σ' _ h => absurd h (by omega)

end
end LeanVM.Guest.B1.VerifySub
