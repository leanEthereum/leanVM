/-
  LeanVM.Guest.B1.Whir.LamPows

  A level's batching powers: `λ^n` for `opening_queries` and the level's scalar, and `μ = 1/λ`
  stored for the residual chain.
-/

module

public import LeanVM.Guest.B1.Whir.Loops

/-!
# `lam_pow` and `level_mus` (G:1585-1586)

`osLamPow lvl lam n k` computes `λ^n` by square and multiply (`osPowSteps`) and stores
`level_mus[lvl] = μ` with `μ·λ = 1` (`osLamPow_sound`): the residual chain runs
`h ← (h + eq)·μ` and the level's scalar carries `λ^n`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **The batching power and its inverse**: `λ^n` at the returned value, `μ` stored at
`level_mus[lvl]` with `μ·λ = 1` (so `λ ≠ 0` and `μ = λ⁻¹`). -/
theorem osLamPow_sound {lvl lam n k : ℕ} (hd : digitsVal (osPowDigits n) 1 = n)
    (h : AllOk C rd σ (osLamPow lvl lam n k).1) :
    σ (.n (osLamPow lvl lam n k).2.1) = σ (.n lam) ^ n ∧ σ (.n lam) ≠ 0 ∧
      LoadHolds rd (σ (.n osMus)) lvl (σ (.n lam))⁻¹ := by
  simp only [osLamPow, allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at h
  obtain ⟨hp, hc, hm, hl⟩ := h
  have hv := osPowSteps_val (C := C) (rd := rd) lam (osPowDigits n) lam k 1 (by rw [pow_one]) hp
  rw [hd] at hv
  rw [hc] at hm
  have hne : σ (.n lam) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hm; exact one_ne_zero (word_one ▸ hm)
  refine ⟨hv, hne, ?_⟩
  have hinv : σ (.n (k + osPowLen n + 1)) = (σ (.n lam))⁻¹ := by
    rw [word_one] at hm
    exact eq_inv_of_mul_eq_one_left hm.symm
  rw [← hinv]; exact hl

theorem osLamPow_next (lvl lam n k : ℕ) : (osLamPow lvl lam n k).2.2 = k + osPowLen n + 2 := rfl

end
end LeanVM.Guest.B1.Whir
