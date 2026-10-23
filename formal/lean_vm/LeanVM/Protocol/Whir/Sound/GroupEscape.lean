/-
  LeanVM.Protocol.Whir.Sound.GroupEscape

  The escape expectations of a WHIR level's joint groups, in the form `Spec.ofNoMove` consumes:
  the out-of-domain point (`sampleN κ`) and the query group (positions, `λ`, openings), on a
  level with a next commitment and on the final level.
-/

module

public import LeanVM.Protocol.Whir.Sound.Defs

/-!
# Escapes of the joint groups

* `escRet_sampleN_le`: the out-of-domain point escapes the separation of the next list with
  probability at most `eOod P' κ = C(L', 2)·κ/|E|` (`card_oodSep_bad_le`; the `κ` samples are a
  uniform vector, `retExp_sampleN`).
* `escRet_queryFrag_le`: the query group escapes the glued claim's doom with probability at most
  `eQuery P P' t = ((A − 1)/n)^t + (t + 1)·L'/|E|`: the positions avoid the agreement set of the
  one consistent candidate except with probability `((A − 1)/n)^t` (`exists_agreeSet`,
  `retExp_queryFrag_le`), and then `λ` escapes at at most `(t + 1)·L'` values
  (`card_lambda_bad_le`).
* `escRet_queryFrag_le_final`: the final level's `((A − 1)/n)^t + t/|E|`.

The groups' posts are functions of the values and of the commitments, which a group does not
change (`retExp_commits`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Prog Finset

@[expose] public section

/-- The average of an indicator is the fraction of its support. -/
theorem avg_ite_le (p : E → Prop) [DecidablePred p] :
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, (if p c then 0 else 1 : ENNReal) =
      (Fintype.card E : ENNReal)⁻¹ * ((univ.filter fun c ↦ ¬ p c).card : ENNReal) := by
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases h : p c <;> simp [h]

open Classical in
/-- **The out-of-domain group.** -/
theorem escRet_sampleN_le (P' : LevelCode) {κ ℓ' : ℕ} (hκ : κ = ℓ' + P'.κ) (hκ1 : 1 ≤ κ)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (J : List E → List (ℕ × ℕ × Word) → Prop)
    (h₀ : List Ev) (hJ : ∀ z : List E, z.length = κ → OodSep P' Q' z → J z (commits h₀)) :
    escRet (fun z h ↦ J z (commits h)) h₀ [] (sampleN κ) ≤ eOod P' κ := by
  unfold escRet
  rw [retExp_commits (fun z cs ↦ if J z cs then 0 else 1), List.append_nil, retExp_sampleN]
  set N := (univ.filter fun v : Vector E κ ↦ ¬ OodSep P' Q' v.toList).card
  have hsum : ∑ f : Fin κ → E, (if J (List.ofFn f) (commits h₀) then 0 else 1 : ENNReal) ≤ N := by
    calc ∑ f : Fin κ → E, (if J (List.ofFn f) (commits h₀) then 0 else 1 : ENNReal)
        ≤ ∑ f : Fin κ → E, (if OodSep P' Q' (List.ofFn f) then 0 else 1 : ENNReal) := by
          gcongr with f
          by_cases hs : OodSep P' Q' (List.ofFn f)
          · simp [hs, hJ _ (List.length_ofFn) hs]
          · split_ifs <;> simp
      _ = ((univ.filter fun f : Fin κ → E ↦ ¬ OodSep P' Q' (List.ofFn f)).card : ENNReal) := by
          rw [Finset.card_filter, Nat.cast_sum]
          exact Finset.sum_congr rfl fun f _ ↦ by
            by_cases h : OodSep P' Q' (List.ofFn f) <;> simp [h]
      _ = N := by
          have hcard : (univ.filter fun f : Fin κ → E ↦ ¬ OodSep P' Q' (List.ofFn f)).card = N := by
            refine Finset.card_bij' (fun f _ ↦ Vector.ofFn f) (fun v _ ↦ fun j : Fin κ ↦ v[j.val])
              ?_ ?_ ?_ ?_
            · intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
              rwa [Vector.toList_ofFn]
            · intro v hv
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
              rwa [← Vector.toList_ofFn, Vector.ofFn_getElem]
            · intro f _; funext j; simp
            · intro v _; exact Vector.ofFn_getElem
          rw [hcard]
  have hN : (N : ENNReal) ≤ ((P'.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) : ℕ) :
      ENNReal) := by exact_mod_cast card_oodSep_bad_le P' hκ Q'
  calc (Fintype.card E : ENNReal)⁻¹ ^ κ * ∑ f : Fin κ → E, _
      ≤ (Fintype.card E : ENNReal)⁻¹ ^ κ *
        ((P'.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) : ℕ) : ENNReal) := by
        gcongr; exact hsum.trans hN
    _ = eOod P' κ := by
        obtain ⟨k, rfl⟩ : ∃ k, κ = k + 1 := ⟨κ - 1, by omega⟩
        rw [eOod, ENNReal.div_eq_inv_mul, Nat.add_sub_cancel]
        push_cast
        rw [pow_succ, mul_comm ((Fintype.card E : ENNReal)⁻¹ ^ k), mul_assoc]
        have h1 : (Fintype.card E : ENNReal)⁻¹ ^ k * (Fintype.card E : ENNReal) ^ k = 1 := by
          rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
        calc (Fintype.card E : ENNReal)⁻¹ * ((Fintype.card E : ENNReal)⁻¹ ^ k *
              ((P'.listMax.choose 2 : ENNReal) * ((k + 1 : ENNReal) * (Fintype.card E) ^ k)))
            = (Fintype.card E : ENNReal)⁻¹ * ((P'.listMax.choose 2 : ENNReal) * (k + 1)) *
              ((Fintype.card E : ENNReal)⁻¹ ^ k * (Fintype.card E : ENNReal) ^ k) := by ring
          _ = _ := by rw [h1, mul_one]

/-- The count of the positions in the agreement set. -/
theorem card_filter_mem {n : ℕ} (A : Finset (Fin n)) :
    (univ.filter fun j : Fin n ↦ ∀ h : (j : ℕ) < n, (⟨j, h⟩ : Fin n) ∈ A).card = A.card := by
  congr 1
  ext j
  simp

/-- `((|A|)/n)^t ≤ ((thr − 1)/n)^t` for `|A| + 1 ≤ thr`. -/
theorem pow_frac_le (P : LevelCode) (A : Finset (Fin P.n)) (hA : A.card + 1 ≤ P.thr) (t : ℕ) :
    ((A.card : ENNReal) / 2 ^ (P.κ + P.R)) ^ t ≤ (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t := by
  have hn : ((P.n : ℕ) : ENNReal) = 2 ^ (P.κ + P.R) := by simp [LevelCode.n]
  rw [hn]
  gcongr
  exact_mod_cast (show A.card ≤ P.thr - 1 by omega)

open Classical in
/-- **The query group of a level with a next commitment.** -/
theorem escRet_queryFrag_le (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (t i : ℕ)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[i]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag (P.κ + P.R) t i) ≤ eQuery P P' t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet P P' hκ Q' C Φ σ z y hviol hsep
  have hd1 : 1 ≤ P.κ + P.R := by have := P.hκ; omega
  have hd2 : P.κ + P.R ≤ 192 := by have := P.h64; omega
  refine (retExp_queryFrag_le (P.κ + P.R) t i hd1 hd2 h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A)
    ((((t + 1) * P'.listMax : ℕ) : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGood P P' hκ Q' C Φ σ z y qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le P P' hκ Q' C Φ σ z y qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦ ¬ Viol P' Q'
          (fun r ↦ Φ r + 1 * lam * eqEval z r +
            1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
          (σ + 1 * lam * y + 1 * lam * lam *
            ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact fun hv ↦ hlam (hJ qs lam hr hlen hv)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQuery]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

open Classical in
/-- **The query group of the final level.** -/
theorem escRet_queryFrag_le_final (P : LevelCode) (t i : ℕ)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[i]? = some (P.κ + P.R, wd, W))
    (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
          (bitsL x)) * G x ≠
        σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k] →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag (P.κ + P.R) t i) ≤
      eQueryFinal P t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_final P C Φ σ hviol G
  have hd1 : 1 ≤ P.κ + P.R := by have := P.hκ; omega
  have hd2 : P.κ + P.R ≤ 192 := by have := P.h64; omega
  refine (retExp_queryFrag_le (P.κ + P.R) t i hd1 hd2 h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) ((t : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGoodFinal P C Φ σ G qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le_final P C Φ σ G qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦
          ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
            (bitsL x)) * G x =
          σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        by_contra hne
        exact hlam (hJ qs lam hr hlen hne)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQueryFinal]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

end
end LeanVM.Protocol.Whir.Sound
