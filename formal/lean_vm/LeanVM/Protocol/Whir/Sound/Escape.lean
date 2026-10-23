/-
  LeanVM.Protocol.Whir.Sound.Escape

  The escape counts of a WHIR level interface: the out-of-domain point separates the next
  oracle's list except at `C(L, 2)·κ·|E|^(κ−1)` points; the query positions then catch the one
  candidate consistent with the out-of-domain answer unless they all land in an agreement set of
  fewer than `A` columns; and the level's batching challenge `λ` keeps every list member violating
  the glued claim except at `(t + 1)·L` values (`t` on the final level, no list).
-/

module

public import LeanVM.Protocol.Whir.Sound.Lanes
public import LeanVM.Protocol.ToArkLib.Whir.Ood
public import LeanVM.Protocol.ToArkLib.Whir.Counting

/-!
# Escapes at the level interface

Annex B of the leanVM specification (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "OOD
challenge", "Query message" and "Batching challenge", for the deployed order of messages
(`verify_whir`, `python-verifier/verifier.py:1026-1062`): commitment of the next oracle `O'`, the
out-of-domain point `z` and answer `y` with its intro polynomial, the proof of work, the query
positions, `λ`, the openings, the query intro polynomial. The level's claims are glued with
powers of `λ`: the running claim with `λ⁰`, the out-of-domain claim with `λ`, the `t` consistency
claims with `λ^(2+q)`. On the final level the residual `f` is sent instead of `O'`, and the
consistency claims get `λ^(1+q)`.

* `OodSep P' Q z`: the members of the list of the next oracle `Q` have pairwise distinct
  out-of-domain values at `z`, i.e. distinct `claimSum (eqEval z)` of their decoded messages.
  `card_oodSep_bad_le`: at most `C(listMax', 2)·κ·|E|^(κ−1)` points `z` break it
  (`card_ood_collision_image_le`).
* `QueryGood`: after positions `qs`, every member `V` of the next list violates the running claim,
  or the out-of-domain claim, or the consistency claim at some queried column. `exists_agreeSet`:
  under the doom before the positions, there is a set `A` of at most `thr − 1` columns such that
  positions breaking `QueryGood` all lie in `A`: the one candidate `V*` with the right
  out-of-domain value (`OodSep`) either is close to the folded word, then it violates the running
  claim by the doom, or agrees with it on fewer than `thr` columns.
* `card_lambda_bad_le`: under `QueryGood`, at most `(t + 1)·listMax'` values `λ` let a member
  satisfy the glued claim: its discrepancy is a nonzero polynomial of degree `t + 1` in `λ`.
* The final level: `exists_agreeSet_final`, `card_lambda_bad_le_final` (degree `t`, the residual
  alone).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset CompPoly
  CMlPolynomialEval

@[expose] public section

/-! ## Out-of-domain separation -/

/-- The out-of-domain value of a decoded member: its claim against `eq_eval(z, ·)`. -/
def oodVal {m κ : ℕ} (z : List E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) : E :=
  claimSum (eqEval z) g

/-- The members of the list of `Q` have pairwise distinct out-of-domain values at `z`. -/
def OodSep (P : LevelCode) {m : ℕ} (Q : (Fin m → Bool) → Fin P.n → E) (z : List E) : Prop :=
  ∀ V ∈ iList P.code P.thr Q, ∀ V' ∈ iList P.code P.thr Q, V ≠ V' →
    oodVal z (decode P V) ≠ oodVal z (decode P V')

/-- The out-of-domain claim against a vector point reads the extension of the table. -/
theorem sum_eqEval_vec {κ : ℕ} (v : Vector E κ) (G : (Fin κ → Bool) → E) :
    ∑ p, eqEval v.toList (bitsL p) * G p = evalMle (tableOf G) v := by
  rw [evalMle_eq_sum, ← Equiv.sum_comp (bitsEquiv κ)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have ht : (tableOf G)[bitsEquiv κ p] = G p := by
    simp [tableOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  have hl : (lagrangeBasis v)[bitsEquiv κ p] = eqEval v.toList (bitsL p) := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (bitsEquiv κ p).isLt,
      eqEval_bitsL v.toList (by simp)]
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    rw [bitsEquiv_val, testBit_bitsToNat]
    simp [List.getD_eq_getElem?_getD]
  rw [ht, hl, mul_comm]

/-- Decoding is injective on interleaved codewords. -/
theorem decode_injOn (P : LevelCode) {ρ : Type*} {V V' : ρ → Fin P.n → E}
    (hV : IsInterleavedCodeword P.code V) (hV' : IsInterleavedCodeword P.code V')
    (h : decode P V = decode P V') : V = V' := by
  funext u
  rw [← enc_decode P hV u, ← enc_decode P hV' u, h]

/-- The table of a message is injective in the message. -/
theorem tableOf_injective {κ : ℕ} : Function.Injective (tableOf (n := κ)) := by
  intro G G' h
  funext p
  have := congrArg (fun t : CMlPolynomialEval E κ ↦ t[bitsEquiv κ p]) h
  simpa [tableOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply] using this

/-- Joining is injective in the split message. -/
theorem joinMsg_injective {n m κ' : ℕ} (hn : n = m + κ') :
    Function.Injective (fun g : (Fin m → Bool) → (Fin κ' → Bool) → E ↦ joinMsg hn g) := by
  subst hn
  intro g g' h
  funext u x
  have := congrFun h (Fin.append u x)
  simpa [joinMsg] using this

open Classical in
/-- **Out-of-domain separation** (Annex B, `lem:ood`): at most `C(listMax, 2)·κ·|E|^(κ−1)` points
`z` leave two members of the list of `Q` with equal out-of-domain values. -/
theorem card_oodSep_bad_le (P : LevelCode) {m κ : ℕ} (hκ : κ = m + P.κ)
    (Q : (Fin m → Bool) → Fin P.n → E) :
    (univ.filter fun v : Vector E κ ↦ ¬ OodSep P Q v.toList).card ≤
      P.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) := by
  set L := iList P.code P.thr Q
  let dec : ((Fin m → Bool) → Fin P.n → E) → CMlPolynomialEval E κ :=
    fun V ↦ tableOf (joinMsg hκ (decode P V))
  have hval : ∀ V (v : Vector E κ), oodVal v.toList (decode P V) = evalMle (dec V) v := by
    intro V v
    rw [oodVal, ← sum_joinMsg hκ, sum_eqEval_vec]
  have hinj : Set.InjOn dec L := by
    intro V hV V' hV' h
    exact decode_injOn P ((mem_iList _ _ _ _).mp hV).1 ((mem_iList _ _ _ _).mp hV').1
      (joinMsg_injective hκ (tableOf_injective h))
  refine (Finset.card_le_card fun v hv ↦ ?_).trans
    ((card_ood_collision_image_le L dec hinj).trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (P.card_iList_le Q))))
  have hv' := (Finset.mem_filter.mp hv).2
  simp only [OodSep, not_forall, not_not, exists_prop] at hv'
  obtain ⟨V, hV, V', hV', hne, heq⟩ := hv'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, V, hV, V', hV', hne, by
    rw [← hval, ← hval, heq]⟩

/-! ## Batching sums -/

/-- The batched sum with `powers λ`: `Σ_q λ^q f(q)`. -/
theorem sum_zip_powersFrom (lam acc : E) (qs : List ℕ) (f : ℕ → E) :
    (((powersFrom acc lam qs.length).zip qs).map fun wq ↦ wq.1 * f wq.2).sum =
      ∑ k : Fin qs.length, acc * lam ^ (k : ℕ) * f qs[k] := by
  induction qs generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.length_cons, powersFrom, List.zip_cons_cons, List.map_cons, List.sum_cons, ih,
      Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun k _ ↦ ?_)
    simp only [pow_succ]
    ring_nf
    rfl

theorem sum_zip_powers (lam : E) (qs : List ℕ) (f : ℕ → E) :
    (((powers lam qs.length).zip qs).map fun wq ↦ wq.1 * f wq.2).sum =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) * f qs[k] := by
  rw [powers, sum_zip_powersFrom]
  simp

/-- `powers λ t` has `t` entries. -/
theorem length_powers (lam : E) (t : ℕ) : (powers lam t).length = t := by
  rw [powers]
  suffices h : ∀ acc, (powersFrom acc lam t).length = t from h 1
  induction t with
  | zero => intro; rfl
  | succ t ih => intro acc; simp [powersFrom, ih]

/-! ## Query positions -/

/-- An entry of a word at an integer position (`0` outside). -/
def wordAt {n : ℕ} (C : Fin n → E) (q : ℕ) : E := if h : q < n then C ⟨q, h⟩ else 0

/-- After positions `qs`, every member of the list of `Q'` violates the running claim `(Φ, σ)`,
the out-of-domain claim `(eq_eval(z, ·), y)`, or the consistency claim at a queried column of the
folded word `C`. -/
def QueryGood (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) ≠ σ ∨ oodVal z (decode P' V) ≠ y ∨
    ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (decode P' V)) q ≠ wordAt C q

/-- A message whose encoding agrees with the folded word on `thr` columns is caught by the
running claim. -/
theorem viol_of_close (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E)
    (hclose : P.thr ≤ (univ.filter fun x ↦ enc P.κ P.R G x = C x).card) :
    ∑ x, Φ (bitsL x) * G x ≠ σ := by
  have hmem : (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∈ iList P.code P.thr fun _ ↦ C := by
    rw [mem_iList]
    refine ⟨fun _ ↦ ?_, _, hclose, fun _ x hx ↦ ((Finset.mem_filter.mp hx).2).symm⟩
    show _ ∈ ReedSolomon.code (domain P.κ P.R P.h64) (2 ^ P.κ)
    rw [← range_enc P.h64]; exact LinearMap.mem_range_self _ _
  have := hviol _ hmem
  rwa [decode_enc P (fun _ ↦ G), claimSum_zero] at this

/-- **The query step.** Under the doom before the positions (every member of the list of the
folded word `C` violates `(Φ, σ)`, and the out-of-domain values separate the list of `Q'`), the
positions breaking `QueryGood` all lie in a set of at most `thr − 1` columns. -/
theorem exists_agreeSet (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGood P P' hκ Q' C Φ σ z y qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ ∧
      oodVal z (decode P' V) = y
  · obtain ⟨V₀, hV₀, hclaim, hood⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact viol_of_close P C Φ σ hviol G (Nat.lt_succ_iff.mp (not_le.mp hlt))
        (by rw [sum_joinMsg]; exact hclaim)
    · intro hlt
      simp only [QueryGood, not_forall, not_or, not_not, exists_prop, not_exists, not_and] at hqs
      obtain ⟨V, hV, hc, ho, hall⟩ := hqs
      have hVV : V = V₀ := by
        by_contra hne
        exact hsep V hV V₀ hV₀ hne (ho.trans hood.symm)
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV
    by_contra h
    simp only [not_or, not_not] at h
    exact hex ⟨V, hV, h.1, h.2.1⟩

/-! ## The batching challenge -/

/-- **The batching step.** If a member violates one of the running, out-of-domain and `t`
consistency claims, the glued claim with powers `1, λ, λ^2, …, λ^(t+1)` holds at at most `t + 1`
values `λ`. -/
theorem card_glue_bad_le {t : ℕ} (a σ b y : E) (e c : Fin t → E)
    (h : a ≠ σ ∨ b ≠ y ∨ ∃ k, e k ≠ c k) :
    (univ.filter fun lam : E ↦ a + lam * b + lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k =
        σ + lam * y + lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k).card ≤ t + 1 := by
  let d : Fin (t + 2) → E := Fin.cons (a - σ) (Fin.cons (b - y) fun k ↦ e k - c k)
  have hd : ∃ k, d k ≠ 0 := by
    rcases h with h | h | ⟨k, hk⟩
    · exact ⟨0, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨1, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨k.succ.succ, by simpa [d, sub_eq_zero] using hk⟩
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans (card_powerBatch_eq_zero_le d hd)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
  have hs : ∑ k : Fin t, (e k - c k) * lam ^ ((k : ℕ) + 1 + 1) =
      lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k -
        lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [d, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, hs]
  linear_combination hlam

/-- **The final batching step.** If the residual violates the running claim or a consistency
claim, the glued claim with powers `1, λ, …, λ^t` holds at at most `t` values `λ`. -/
theorem card_glue_bad_le_final {t : ℕ} (a σ : E) (e c : Fin t → E)
    (h : a ≠ σ ∨ ∃ k, e k ≠ c k) :
    (univ.filter fun lam : E ↦ a + lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k =
        σ + lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k).card ≤ t := by
  let d : Fin (t + 1) → E := Fin.cons (a - σ) fun k ↦ e k - c k
  have hd : ∃ k, d k ≠ 0 := by
    rcases h with h | ⟨k, hk⟩
    · exact ⟨0, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨k.succ, by simpa [d, sub_eq_zero] using hk⟩
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans (card_powerBatch_eq_zero_le d hd)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
  have hs : ∑ k : Fin t, (e k - c k) * lam ^ ((k : ℕ) + 1) =
      lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k - lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [d, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, hs]
  linear_combination hlam

/-! ## The final level's query step -/

/-- After positions `qs` on the final level, the residual `G` violates the running claim or the
consistency claim at a queried column. -/
def QueryGoodFinal (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (qs : List ℕ) : Prop :=
  ∑ x, Φ (bitsL x) * G x ≠ σ ∨ ∃ q ∈ qs, encAt P.κ P.R G q ≠ wordAt C q

/-- **The final query step.** Positions breaking `QueryGoodFinal` lie in a set of at most
`thr − 1` columns. -/
theorem exists_agreeSet_final (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodFinal P C Φ σ G qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hc : ∑ x, Φ (bitsL x) * G x = σ
  · refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact viol_of_close P C Φ σ hviol G (Nat.lt_succ_iff.mp (not_le.mp hlt)) hc
    · simp only [QueryGoodFinal, not_or, not_not, not_exists, not_and] at hqs
      intro hlt
      have h := hqs.2 q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd (Or.inl hc) hqs⟩

end
end LeanVM.Protocol.Whir.Sound
