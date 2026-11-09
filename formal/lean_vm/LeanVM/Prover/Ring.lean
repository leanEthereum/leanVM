/-
  LeanVM.Prover.Ring

  The executable ring switching makes the specification's moves and returns the data of its
  claim.
-/

module

public import Statement.Prover.Whir
public import LeanVM.Prover.Corr
public import LeanVM.Protocol.EndToEnd.Complete.Ring

/-!
# Ring switching

`corr_ringFast`: `ringFast point slices` makes the moves of the specification's
`hRing point slices` (six challenges, nothing sent), and the specification's result is the
target with the weight `ringWeight point · (ringCoefficients challenges)` of the executable's
result; the claim description of the result (`RingOut.claim`) denotes the specification's ring
claim on the stack (`denote_ringOut_claim`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-- Receiving `n` challenges gives `n` challenges. -/
theorem corr_sampleN : ∀ n : ℕ,
    Corr (fun a b ↦ a = b ∧ a.length = n) (Script.sampleN n) (Script.sampleN n)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    simp only [Script.sampleN, Script.sampleE, Script.bind_eq, Script.pure_eq]
    intro c
    simp only [Script.bind]
    refine Corr.bind (fun a b h ↦ ?_) _ _ (corr_sampleN n)
    obtain ⟨rfl, hl⟩ := h
    exact ⟨rfl, by simp [hl]⟩

/-- **The executable ring switching makes the specification's moves**, and the specification's
result is the target with the weight of the executable's point and coefficients. -/
theorem corr_ringFast (point slices : List E) :
    Corr (fun a b ↦ b = (a.target, fun rPrime ↦ ringWeight a.point rPrime
        (ringCoefficients a.challenges)) ∧ a.point = point ∧ a.challenges.length = 6)
      (ringFast point slices) (hRing point slices) := by
  simp only [ringFast, hRing, Script.bind_eq, Script.pure_eq]
  refine Corr.bind (fun a b h ↦ ?_) _ _ (corr_sampleN _)
  obtain ⟨rfl, hl⟩ := h
  exact ⟨rfl, rfl, hl⟩

end
end LeanVM.Prover
