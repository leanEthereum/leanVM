/-
  LeanVM.Guest.B1.Whir.LamPows

  A level's batching inverse: `μ = 1/λ` stored for the residual chain.
-/

module

public import LeanVM.Guest.B1.Whir.Loops

/-!
# `level_mus`

`osMu lvl lam k` stores `level_mus[lvl] = μ` with `μ·λ = 1` (`osMu_sound`): the residual chain
runs `h ← (h + eq)·μ`. (`λ^n`, the level's scalar's factor, is `level_queries`' return.)
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **The batching challenge's inverse**: `μ` stored at `level_mus[lvl]` with `μ·λ = 1` (so
`λ ≠ 0` and `μ = λ⁻¹`). -/
theorem osMu_sound {lvl lam k : ℕ} (h : AllOk C rd σ (osMu lvl lam k).1) :
    σ (.n lam) ≠ 0 ∧ LoadHolds rd (σ (.n osMus)) lvl (σ (.n lam))⁻¹ := by
  simp only [osMu, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
  obtain ⟨hc, hm, hl⟩ := h
  rw [hc] at hm
  have hne : σ (.n lam) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hm; exact one_ne_zero (word_one ▸ hm)
  refine ⟨hne, ?_⟩
  have hinv : σ (.n (k + 1)) = (σ (.n lam))⁻¹ := by
    rw [word_one] at hm
    exact eq_inv_of_mul_eq_one_left hm.symm
  rw [← hinv]; exact hl

theorem osMu_next (lvl lam k : ℕ) : (osMu lvl lam k).2 = k + 2 := rfl

end
end LeanVM.Guest.B1.Whir
