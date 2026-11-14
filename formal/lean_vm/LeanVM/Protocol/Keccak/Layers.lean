/-
  LeanVM.Protocol.Keccak.Layers

  The twelve layers of `verifyKeccak` on a candidate's committed states: from a claim on the
  segments' outputs to one on their committed inputs.
-/

module

public import LeanVM.Protocol.Keccak.Start

/-!
# The layers

`keccakLayers logSteps (List.range 12)` (`crates/verifier/src/keccak.rs`) runs
`verifyKeccakLayer` at steps `0, …, 11`. On a candidate's column `qk q`, the states at depth `d` are
`statesAt … d` (`12 - d` rounds into each segment), and depth `d` is the round of depth `d + 1`
(`claimTrue_round`), so `layerSpec` chains (`layersSpec`): from doom of the claim at depth `d` to
doom of the claim at depth `12`, on the committed inputs.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front
open scoped ENNReal

@[expose] public section

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

open Classical in
/-- **The layers from depth `d`**: lead `T` (`0` when a layer is left, as it starts with a
read); each layer's groups as in `layerSpec`. -/
noncomputable def layersSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ)
    (h46 : (2 : ℝ≥0∞)⁻¹ ^ grindingBits (productBits - 1) * ((L₀ : ℝ≥0∞) * errE 46) ≤ εmax)
    (h3 : (L₀ : ℝ≥0∞) * errE 3 ≤ εmax) (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    (n d : ℕ) → d + n = 12 → (claim : KeccakClaim) → ClaimShape P claim →
      Spec (keccakLayers (P + 4) (List.range' d n) claim)
        (Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) d) P claim ∧ R q))
        (fun c h ↦ ClaimShape P c ∧
          Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P c ∧ R q) h) εmax T T
  | 0, d, hd, claim, hs =>
    (Spec.ret (Post := fun c h ↦ ClaimShape P c ∧
        Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P c ∧ R q) h) claim).mono
      (fun _ h' ↦ ⟨hs, by rw [show d = 12 by omega] at h'; exact h'⟩) (fun _ _ h' ↦ h')
      le_rfl le_rfl le_rfl
  | n + 1, d, hd, claim, hs =>
    ((layerSpec (T := T) hst hcard R (fun q ↦ statesAt (P + 4) (qk q) (d + 1)) d P claim hs h46
      h3 hβ).mono (fun _ h' ↦ Doomed.mono h' fun q ⟨hc, hR⟩ ↦
        ⟨(claimTrue_round (P + 4) (qk q) (by omega) P claim).2 hc, hR⟩)
      (fun _ _ h' ↦ h') le_rfl zero_le le_rfl).bind' fun c ↦
    if hc : ClaimShape P c then
      (layersSpec hst hcard R qk P h46 h3 hβ n (d + 1) (by omega) c hc).mono
        (fun _ h' ↦ h'.2) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h' ↦ hc h'.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

end
end LeanVM.Protocol.KeccakGkr
