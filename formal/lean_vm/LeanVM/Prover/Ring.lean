/-
  LeanVM.Prover.Ring

  The executable ring switching makes the specification's moves and returns the data of its
  claim.
-/

module

public import Statement.Prover.Whir
public import LeanVM.Prover.Corr
public import LeanVM.Protocol.EndToEnd.Complete.Ring
public import LeanVM.Protocol.RingVerifier

/-!
# Ring switching

`corr_ringFast`: `ringFast point slices` makes the moves of the specification's
`hRing point slices` (a grind and sixteen challenges, nothing sent), and the specification's
result is the target with the weight `ringWeight point · (ringCoefficients f g)` of the
executable's result.
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

attribute [local irreducible] Corr in
/-- **The executable ring switching makes the specification's moves**, and the specification's
result is the target with the weight of the executable's point and challenges. -/
theorem corr_ringFast (point slices : List E) :
    Corr (fun a b ↦ b = (a.target, fun rPrime ↦ ringWeight a.point rPrime
        (Protocol.Ring.ringCoefficients a.f a.g)) ∧ a.point = point ∧ a.f.length = 8 ∧
        a.g.length = 8)
      (ringFast point slices) (hRing point slices) := by
  simp only [ringFast, hRing, Script.bind_eq, Script.pure_eq, show ringMapWidth = 8 from rfl]
  refine Corr.bind_same _ fun _ ↦ ?_
  refine Corr.bind (fun a b h ↦ ?_) _ _ (corr_sampleN _)
  obtain ⟨rfl, hl⟩ := h
  refine Corr.ret_ret ⟨?_, rfl, by simp [hl], by simp [hl]⟩
  rw [Protocol.Ring.verifier_ringTarget]

end
end LeanVM.Prover
