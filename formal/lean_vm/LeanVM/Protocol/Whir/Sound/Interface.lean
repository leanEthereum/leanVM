/-
  LeanVM.Protocol.Whir.Sound.Interface

  The batching challenge `λ` of a WHIR level against the program's glued claim: after positions
  that catch every member of the next list, at most `(t + 1)·L'` values of `λ` let a member
  satisfy the claim the verifier glues (`t` values on the final level, for the residual).
-/

module

public import LeanVM.Protocol.Whir.Sound.Folds
public import LeanVM.Protocol.Whir.Sound.Group

/-!
# The glued claim of a level

The verifier glues a level's claims into the running sumcheck (`glue`,
`python-verifier/verifier.py:1058-1062` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`):
the running claim keeps `λ⁰`, the out-of-domain claim `(eq_eval(z, ·), y)` gets `λ`, and the batch
of consistency claims `(_induced_weight(κ, qs, powers(λ, t), ·), _enforced_sum)` gets `λ²`; on the
final level only the batch, with `λ`. With the inner products of `LeanVM.Protocol.Whir.Sound.
Weights` (`sum_inducedWeight_mul`: the batch weight pairs with a message to `Σ_q λ^q Enc(G)[x_q]`)
the glued claim of a member is a polynomial in `λ` of degree `t + 1` whose coefficients are the
discrepancies of the separate claims.

* `card_lambda_bad_le`: under `QueryGood`, at most `(t + 1)·listMax'` values of `λ` break
  `Viol` for the glued claim.
* `card_lambda_bad_le_final`: under `QueryGoodFinal`, at most `t` values of `λ` let the residual
  satisfy the glued claim.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## Linearity and bookkeeping -/

theorem claimSum_add {m κ : ℕ} (Φ Ψ : List E → E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    claimSum (fun r ↦ Φ r + Ψ r) g = claimSum Φ g + claimSum Ψ g := by
  simp only [claimSum, add_mul, Finset.sum_add_distrib]

theorem claimSum_const_mul {m κ : ℕ} (c : E) (Φ : List E → E)
    (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    claimSum (fun r ↦ c * Φ r) g = c * claimSum Φ g := by
  simp only [claimSum, Finset.mul_sum, mul_assoc]

theorem claimSum_glue2 {m κ : ℕ} (Φ Ψ₁ Ψ₂ : List E → E) (a b : E)
    (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    claimSum (fun r ↦ Φ r + a * Ψ₁ r + b * Ψ₂ r) g =
      claimSum Φ g + a * claimSum Ψ₁ g + b * claimSum Ψ₂ g := by
  simp only [claimSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

/-- The program's rows of an opening are the lanes of its leaves. -/
theorem rows_eq (i : ℕ) (words : List (List K)) :
    (if i = 0 then words.map (fun row ↦ row.reverse.map ofK) else words.map extRow) =
      words.map (lanesOf i) := by
  by_cases h : i = 0 <;> simp [lanesOf, h]

theorem wordOf_append (cs : List (ℕ × ℕ × Word)) (x : ℕ × ℕ × Word) {i : ℕ}
    (h : i < cs.length) : wordOf (cs ++ [x]) i = wordOf cs i := by
  simp [wordOf, List.getElem?_append_left h]

theorem laneO_append (cs : List (ℕ × ℕ × Word)) (x : ℕ × ℕ × Word) {i : ℕ} (h : i < cs.length)
    (n : ℕ) : laneO i (cs ++ [x]) n = laneO i cs n := by
  funext j v
  simp [laneO, wordOf_append cs x h]

theorem rowsOf_zero {ι : Type*} (O : ℕ → ι → E) : rowsOf 0 O = fun _ ↦ O 0 := by
  funext u
  simp [rowsOf, bitsToNat]

/-! ## The batching challenge -/

/-- The inner product of the batch weight with a member's message: `Σ_k λ^k Enc(G)[x_k]`. -/
theorem claimSum_inducedWeight (P : LevelCode) {ℓ' κ' : ℕ} (hκ : P.κ = ℓ' + κ')
    (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n) (lam : E)
    (g : (Fin ℓ' → Bool) → (Fin κ' → Bool) → E) :
    claimSum (fun r ↦ Verifier.inducedWeight P.κ qs (powers lam qs.length) r) g =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R (joinMsg hκ g) qs[k] := by
  rw [← sum_joinMsg hκ, sum_inducedWeight_mul P.R (by have := P.h64; omega) qs _
    (length_powers lam qs.length) hqs, sum_zip_powers]

open Classical in
/-- **The batching step of a level with a next commitment.** -/
theorem card_lambda_bad_le (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n)
    (hgood : QueryGood P P' hκ Q' C Φ σ z y qs) :
    (univ.filter fun lam : E ↦ ¬ Viol P' Q'
        (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])).card ≤
      (qs.length + 1) * P'.listMax := by
  set L := iList P'.code P'.thr Q'
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans
    ((card_filter_exists_le L (fun V lam ↦
        claimSum Φ (decode P' V) + lam * oodVal z (decode P' V) + lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R (joinMsg hκ (decode P' V)) qs[k] =
        σ + lam * y + lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])
      (N := qs.length + 1) fun V hV ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Viol, not_forall, not_not,
      exists_prop] at hlam ⊢
    obtain ⟨V, hV, heq⟩ := hlam
    refine ⟨V, hV, ?_⟩
    rw [claimSum_glue2, claimSum_inducedWeight P hκ qs hqs lam] at heq
    rw [oodVal]
    simpa only [one_mul] using heq
  · refine card_glue_bad_le _ σ _ y _ _ ?_
    rcases hgood V hV with h | h | ⟨q, hq, hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
      exact Or.inr (Or.inr ⟨⟨k, hk⟩, hne⟩)
  · rw [mul_comm]
    exact Nat.mul_le_mul_left _ (P'.card_iList_le Q')

/-- The residual of the final level as a message (entry `⟨x⟩` of the table). -/
def resMsg {κ : ℕ} (res : List E) : (Fin κ → Bool) → E := fun x ↦ res.getD (bitsToNat x) 0

open Classical in
/-- **The batching step of the final level**: the residual alone, at most `t` values. -/
theorem card_lambda_bad_le_final (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n)
    (hgood : QueryGoodFinal P C Φ σ G qs) :
    (univ.filter fun lam : E ↦
        ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
          (bitsL x)) * G x =
          σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]).card ≤
      qs.length := by
  have hsum : ∀ lam, ∑ x, (Φ (bitsL x) + 1 * lam *
      Verifier.inducedWeight P.κ qs (powers lam qs.length)
      (bitsL x)) * G x = ∑ x, Φ (bitsL x) * G x +
        lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R G qs[k] := by
    intro lam
    rw [← sum_zip_powers, ← sum_inducedWeight_mul P.R (by have := P.h64; omega) qs _
      (length_powers lam qs.length) hqs G, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  simp only [hsum]
  simp only [one_mul]
  refine card_glue_bad_le_final _ σ _ _ ?_
  rcases hgood with h | ⟨q, hq, hne⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    exact Or.inr ⟨⟨k, hk⟩, hne⟩

end
end LeanVM.Protocol.Whir.Sound
