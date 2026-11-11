module

public import Qrom.Sphincs.Hidden

@[expose] public section

/-!
# From the presampled game to the hidden game

Any event of the result and the final log has, in the presampled game, at most the square of its
weight's square root in the hidden game plus `n √(4 · 2^-128 tr ρ)`, for a program making at most
`n` calls (`Qrom.Sphincs.hiding_step`).
-/

open OracleComp OracleSpec FORS Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

open Classical in
theorem hiding_step {A : QReg} {α : Type} (x : QComp Spec A (QReg.of Unit) α) (n : ℕ)
    (hx : x.IsTotalQueryBound n) (ρ : SubState A)
    (ev : Data → (Input → HashOutput) → (Σ u, QuantumComp₂.Leaf (QReg.of Unit) α u) → Log → Bool) :
    OvGame.avgSide presGame .instruments x ρ ev ^ (2⁻¹ : ℝ) ≤
      OvGame.avgSide hidGame .instruments x ρ ev ^ (2⁻¹ : ℝ) +
        n * (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) :=
  OvGame.hiding_side_le presGame hidGame rev Prot (fun _ ↦ rfl) (fun d s x hx ↦ hidGame_ov d s x hx)
    (fun _ ↦ rfl) (fun d d' s H ↦ rev_self d d' s H) (fun d j s ↦ rev_mono d j s)
    (fun d d' s H ↦ hidGame_local d d' s H) (fun d d' j s H ↦ hidGame_localTr d d' j s H)
    (fun _ _ ↦ rfl) (by positivity) (fun d s x ↦ card_prot_le d s x) .instruments n x hx ρ ev

end Qrom.Sphincs
