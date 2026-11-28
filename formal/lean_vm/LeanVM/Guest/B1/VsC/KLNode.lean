/-
  LeanVM.Guest.B1.VsC.KLNode

  `keccak_layer`'s node placed: the valuation before the memory, the callees' arguments, regions
  and preconditions.
-/

module

public import LeanVM.Guest.B1.VsC.KLPlacedM
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# `keccak_layer`'s node, before the memory

`layerσ0`: the empty memory's valuation with the words the dispatches read from memory patched to
their honest values (the capacity after `s`, the product at `s`, the claim's point pointer and its
shift). `layer_σ0_calls`: the dispatches' arguments and returns on it. `layer_kregions`,
`layer_kpres`: the callees' regions and preconditions.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The valuation before the memory.** -/
noncomputable def layerσ0 (D : LayerData) (first : ℕ) (cpt : E) (σr : Val) : Val := fun v ↦
  if v.idx = preOff first + 780 then polyEval D.product (D.sv first)
  else if v.idx = preOff first + 781 then cpt
  else if v.idx = preOff first + 796 then cpt * gen ^ D.n1
  else if preOff first + 539 ≤ v.idx ∧ v.idx < preOff first + 544 then
    (D.capS first).getD (v.idx - (preOff first + 539)) 0
  else σr v

section
variable {D : LayerData} {first : ℕ} {cpt cur : E} {σr : Val}

theorem σ0_other {i : ℕ} (h1 : i ≠ preOff first + 780) (h2 : i ≠ preOff first + 781)
    (h3 : i ≠ preOff first + 796) (h4 : ¬ (preOff first + 539 ≤ i ∧ i < preOff first + 544)) :
    layerσ0 D first cpt σr (.n i) = σr (.n i) := by
  unfold layerσ0; simp only [h1, h2, h3, h4, ↓reduceIte]

theorem σ0_cap {j : ℕ} (hj : j < 5) :
    layerσ0 D first cpt σr (.n (preOff first + 539 + j)) = (D.capS first).getD j 0 := by
  unfold layerσ0
  simp only [show ¬ (preOff first + 539 + j = preOff first + 780) by omega,
    show ¬ (preOff first + 539 + j = preOff first + 781) by omega,
    show ¬ (preOff first + 539 + j = preOff first + 796) by omega,
    show preOff first + 539 ≤ preOff first + 539 + j ∧ preOff first + 539 + j < preOff first + 544 by omega,
    and_self, ↓reduceIte, Nat.add_sub_cancel_left]

theorem list7 {f : ℕ → E} {l : List E} (hl : l.length = 7) (h : ∀ k < 7, f k = l.getD k 0) :
    (List.range 7).map f = l := by
  apply List.ext_getElem (by simp [hl])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [h k (by simpa using h1), List.getD_eq_getElem _ _ h2]

theorem r1_length : (D.r1 first cur).length = 7 := by
  simp [LayerData.r1, (LayerData.run1_state (D := D) (first := first)).2]

theorem r2_length : (D.r2 first cur).length = 7 := by
  simp [LayerData.r2, (LayerData.run2_state (D := D) (first := first)).2]

/-- **The dispatches' words before the memory.** -/
theorem layer_σ0_calls {tb : E} {cb : ℕ}
    (s784 : σr (.n (preOff first + 784)) = cur * gen ^ 48)
    (s785 : ∀ k < 7, σr (.n (preOff first + 785 + k)) = (D.r1 first cur).getD k 0)
    (s782 : σr (.n (preOff first + 782)) = VsC.ptrAtV cb)
    (s797 : σr (.n (preOff first + 797)) = VsC.ptrAtV cb * gen ^ D.n1)
    (s798 : ∀ k < 7, σr (.n (preOff first + 798 + k)) = (D.r2 first cur).getD k 0)
    (s14 : σr (.n (valf% «keccak_layer» "tabs")) = tb) :
    (lA1 (preOff first)).map (layerσ0 D first cpt σr) = D.capS first ++
      [cur * gen ^ 48, polyEval D.product (D.sv first), cpt, VsC.ptrAtV cb, tb] ∧
    (lR1 (preOff first)).map (layerσ0 D first cpt σr) = D.r1 first cur ∧
    (lA2 (preOff first)).map (layerσ0 D first cpt σr) = D.r1 first cur ++
      [cpt * gen ^ D.n1, VsC.ptrAtV cb * gen ^ D.n1, tb] ∧
    (lR2 (preOff first)).map (layerσ0 D first cpt σr) = D.r2 first cur := by
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ := five_of_length' (LayerData.capS_ok (D := D) (first := first))
  have hR1 : (lR1 (preOff first)).map (layerσ0 D first cpt σr) = D.r1 first cur := by
    unfold lR1; rw [List.map_map]
    exact list7 r1_length fun k hk ↦ by
      simp only [Function.comp]; rw [σ0_other (by omega) (by omega) (by omega) (by omega), s785 k hk]
  have hR2 : (lR2 (preOff first)).map (layerσ0 D first cpt σr) = D.r2 first cur := by
    unfold lR2; rw [List.map_map]
    exact list7 r2_length fun k hk ↦ by
      simp only [Function.comp]; rw [σ0_other (by omega) (by omega) (by omega) (by omega), s798 k hk]
  have e0 := σ0_cap (D := D) (cpt := cpt) (σr := σr) (first := first) (j := 0) (by norm_num)
  have e1 := σ0_cap (D := D) (cpt := cpt) (σr := σr) (first := first) (j := 1) (by norm_num)
  have e2 := σ0_cap (D := D) (cpt := cpt) (σr := σr) (first := first) (j := 2) (by norm_num)
  have e3 := σ0_cap (D := D) (cpt := cpt) (σr := σr) (first := first) (j := 3) (by norm_num)
  have e4 := σ0_cap (D := D) (cpt := cpt) (σr := σr) (first := first) (j := 4) (by norm_num)
  rw [hc] at e0 e1 e2 e3 e4
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4
  have f780 : layerσ0 D first cpt σr (.n (preOff first + 780)) = polyEval D.product (D.sv first) := by
    unfold layerσ0; simp
  have f781 : layerσ0 D first cpt σr (.n (preOff first + 781)) = cpt := by
    unfold layerσ0; simp
  have f796 : layerσ0 D first cpt σr (.n (preOff first + 796)) = cpt * gen ^ D.n1 := by
    unfold layerσ0; simp
  refine ⟨?_, hR1, ?_, hR2⟩
  · simp only [lA1, cap5, List.map_cons, List.map_nil, hc, List.cons_append, List.nil_append]
    rw [e0, e1, e2, e3, e4, f780, f781, σ0_other (by omega) (by omega) (by omega) (by omega), s784,
      σ0_other (by omega) (by omega) (by omega) (by omega), s782,
      σ0_other (by omega) (by omega) (by omega) (by omega), s14]
  · simp only [lA2, List.map_append, List.map_cons, List.map_nil]
    rw [hR1, f796, σ0_other (by omega) (by omega) (by omega) (by omega), s797,
      σ0_other (by omega) (by omega) (by omega) (by omega), s14]

end

end
end LeanVM.Guest.B1.VerifySub.KL
