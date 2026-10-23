/-
  LeanVM.Protocol.Whir.Sound.Tail

  The final level's tail rounds and terminal check: the residual `f_final` violates the running
  claim, each tail round keeps it violated except at two challenges, and the terminal check
  rejects a violated claim.
-/

module

public import LeanVM.Protocol.Whir.Sound.LevelMidSpec

/-!
# The tail rounds

On the final level the prover sends the residual table `f_final` (`2^κ` entries), so no list is
involved: after the query group the verifier holds a claim about `f_final` itself, and the tail
(`LeanVM.Protocol.Verifier.tailRounds`, `python-verifier/verifier.py:1067-1073` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) is a plain sumcheck on it.

* `tailMsg τ res n`: the residual folded by the tail challenges `τ` so far, as a message on `n`
  lane bits (the remaining variables) and no message bits.
* `TailInv`: the residual has `2^(|τ| + n)` entries, the running weight is multiaffine, the round
  polynomial sums to the target, and the folded residual violates the running claim.
* `tailSpec`: each tail round escapes with probability at most `eTail = 2/|E|`
  (`card_sumcheck_bad_le`), and the rounds return `TailDone`: the fully folded residual,
  `multilinear_eval(f_final, τ)`, times the running weight at `τ` differs from the final target.
* `tailDone_ne`: the terminal check `weight · multilinear_eval(residual, tail) = target` fails under
  `TailDone`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Prog Finset

@[expose] public section

/-- The residual table as an integer-indexed oracle. -/
def resO (res : List E) : ℕ → Unit → E := fun j _ ↦ res.getD j 0

/-- The residual folded by the tail challenges `τ`, on the `n` remaining variables. -/
def tailMsg (τ res : List E) (n : ℕ) : (Fin n → Bool) → (Fin 0 → Bool) → E :=
  fun u _ ↦ foldsN τ (resO res) (bitsToNat u) ()

variable (ℓ₀ : ℕ) (w : List E → E) (s : WhirState) (res : List E)

/-- **The tail invariant**: the folded residual violates the running claim. -/
def TailInv (τ : List E) (n : ℕ) (target : E) (quad : List E) : Prop :=
  res.length = 2 ^ (τ.length + n) ∧ IsMultiaffine (τ.length + n) (runW w ℓ₀ s) ∧
    QuadOK quad target ∧ claimSum (fun r ↦ runW w ℓ₀ s (τ ++ r)) (tailMsg τ res n) ≠ target

/-- After a tail challenge `c`. -/
def TailMid (τ : List E) (n : ℕ) (c : E) (quad : List E) : Prop :=
  res.length = 2 ^ (τ.length + 1 + n) ∧ IsMultiaffine (τ.length + 1 + n) (runW w ℓ₀ s) ∧
    claimSum (fun r ↦ runW w ℓ₀ s ((τ ++ [c]) ++ r)) (tailMsg (τ ++ [c]) res n) ≠ polyEval quad c

/-- At the end of the tail. -/
def TailDone (τ : List E) (t : E) : Prop :=
  res.length = 2 ^ τ.length ∧ claimSum (fun r ↦ runW w ℓ₀ s (τ ++ r)) (tailMsg τ res 0) ≠ t

variable {ℓ₀ w s res}

theorem foldRows_tailMsg (τ : List E) (n : ℕ) (c : E) :
    foldRows c (tailMsg τ res (n + 1)) = tailMsg (τ ++ [c]) res n := by
  funext u x
  simp [foldRows, tailMsg, bitsToNat_cons, foldsN, List.foldl_append, foldN, add_comm]

open Classical in
/-- A tail round escapes at at most two challenges. -/
theorem card_tailBad_le (τ : List E) (n : ℕ) (target : E) (quad : List E)
    (h : TailInv ℓ₀ w s res τ (n + 1) target quad) :
    (univ.filter fun c ↦ ¬ TailMid ℓ₀ w s res τ n c quad).card ≤ 2 := by
  obtain ⟨hlen, hma, ⟨c₀, c₁, c₂, rfl, hσ⟩, hviol⟩ := h
  have hΦ : IsMultiaffine (n + 1 + 0) fun r ↦ runW w ℓ₀ s (τ ++ r) := hma.append τ rfl
  have hc := card_sumcheck_bad_le _ hΦ (tailMsg τ res (n + 1)) target c₀ c₁ c₂ hσ hviol
  refine (Finset.card_le_card fun c hc' ↦ ?_).trans hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, TailMid, not_and, not_not] at hc' ⊢
  have := hc' (by rw [hlen]; congr 1; omega) (by
    rw [show τ.length + 1 + n = τ.length + (n + 1) by omega]; exact hma)
  rw [← this, foldRows_tailMsg]
  simp

variable (ℓ₀ w s res)

/-- **The tail rounds' specification.** -/
noncomputable def tailSpec {εmax : ENNReal} (hεT : eTail ≤ εmax) :
    (n : ℕ) → (τ : List E) → (target : E) → (quad : List E) →
      Spec (tailRounds n target quad) (fun _ ↦ TailInv ℓ₀ w s res τ n target quad)
        (fun x _ ↦ TailDone ℓ₀ w s res (τ ++ x.1) x.2) εmax eTail 0
  | 0, τ, target, quad => (Spec.ret ([], target)).mono
      (fun _ h ↦ ⟨by simpa using h.1, by simpa using h.2.2.2⟩) (fun _ _ h ↦ h) le_rfl zero_le
      le_rfl
  | n + 1, τ, target, quad =>
    ((Spec.sampleE (Pre := fun _ ↦ TailInv ℓ₀ w s res τ (n + 1) target quad)
        (Post := fun c _ ↦ TailMid ℓ₀ w s res τ n c quad) (εmax := εmax) (T := 0) eTail
        fun _ hp ↦ by
          rw [eTail, ENNReal.div_eq_inv_mul]
          gcongr
          exact_mod_cast card_tailBad_le τ n target quad hp).bind' fun c ↦
      Spec.ite (c := n = 0)
        (fun hn ↦ (Spec.ret ([c], polyEval quad c)).mono (fun _ h ↦ by
          subst hn
          exact ⟨by simpa using h.1, by simpa using h.2.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
        (fun _ ↦ (roundPolyInv (fun _ ↦ TailMid ℓ₀ w s res τ n c quad) (polyEval quad c)
            (T := eTail) hεT).bind' fun quad' ↦
          ((tailSpec hεT n (τ ++ [c]) (polyEval quad c) quad').mono
            (fun _ h ↦ ⟨by simpa using h.2.1, by simpa using h.2.2.1, h.1, by
              simpa using h.2.2.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun x ↦
            (Spec.ret (c :: x.1, x.2)).mono (fun _ h ↦ by simpa using h) (fun _ _ h ↦ h) le_rfl
              le_rfl le_rfl)).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

/-- **The terminal check fails** at the end of the tail. -/
theorem tailDone_ne {τ : List E} {t : E} (h : TailDone ℓ₀ w s res τ t) :
    ¬ runW w ℓ₀ s τ * multilinearEval res τ = t := by
  obtain ⟨hlen, hviol⟩ := h
  rw [claimSum_zero] at hviol
  rw [multilinearEval_eq_foldsN res τ hlen]
  intro heq
  apply hviol
  rw [Fintype.sum_unique]
  simp only [bitsL_zero, List.append_nil, tailMsg]
  have hb : bitsToNat (Fin.elim0 : Fin 0 → Bool) = 0 := by simp [bitsToNat]
  rw [hb]
  exact heq

end
end LeanVM.Protocol.Whir.Sound
