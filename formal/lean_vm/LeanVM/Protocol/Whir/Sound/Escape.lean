/-
  LeanVM.Protocol.Whir.Sound.Escape

  The escape counts of a WHIR level interface: the out-of-domain point separates the next
  oracle's list except at `C(L, 2)·κ|E|^(κ−1)` points; the query positions then catch the one
  message consistent with the out-of-domain answer unless they all land in an agreement set of
  fewer than `A` columns; and the level's batching challenge `λ` keeps every member violating the
  glued claim except at `(t + 1)·L` values.
-/

module

public import LeanVM.Protocol.Whir.Sound.Lanes
public import LeanVM.Protocol.ToArkLib.Whir.Ood
public import LeanVM.Protocol.ToArkLib.Whir.Counting

/-!
# Escapes at the level interface

Annex B (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "The
level interface", "OOD points", "Query message", "Batching challenge", for the deployed order of
messages (`verify_whir`, `crates/verifier/src/whir.rs:291-327`): the next oracle `Q'` and the
folded lane's high part, a grind, the out-of-domain point `z` and answer `y`, a grind, the queries
and `λ`, the openings. The level's claims are glued with powers of `λ`: the running claim with
`λ⁰`, the out-of-domain claim with `λ`, the `t` consistency claims with `λ^(2+q)`.

The next level's members are tuples `U` of `ℓ'` lanes of degree at most the next level's
`d' = 2^κ' − 1 + ℓ'`; `msgT κ' U` is their messages (the low parts, all the claims weigh) and
`joinMsg` the message on the current level's `κ = ℓ' + κ'` variables. Members with the same
messages make the same claims.

* `OodSep P' Q' z`: members of the list of `Q'` with distinct messages differ at `z`;
  `card_oodSep_bad_le`: at most `C(L, 2) κ |E|^(κ−1)` points break it, `L` the list's size (a
  bound on its distinct messages).
* `QDoom`: after the positions `qs`, every member violates the running claim, the out-of-domain
  claim, or the consistency claim at a queried column, `c' q` being the value the verifier
  derives from the opened row (`P(x_q)` corrected by the high part).
* `exists_agreeSet`: positions breaking `QDoom` all lie in a set of at most `A − 1` columns: the
  agreement set of the one message `g*` consistent with the answer, through the polynomial
  `P* = P_(g*) + Ŵ_κ H` of degree at most `2^κ − 1 + ℓ` (`H` the high part).
* `card_lambda_bad_le`: from `QDoom`, at most `(t + 1)·|list|` values `λ` let a member satisfy
  the glued claim.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset Polynomial CompPoly
  CMlPolynomialEval

@[expose] public section

/-! ## Messages of tuples -/

/-- The messages of a tuple's lanes. -/
noncomputable def msgT {m : ℕ} (κ : ℕ) (U : (Fin m → Bool) → E[X]) :
    (Fin m → Bool) → (Fin κ → Bool) → E :=
  fun u ↦ lowMsg κ (U u)

/-- A polynomial of degree below `2^κ` is the message polynomial of its low part. -/
theorem msgPoly_lowMsg_of_deg {κ : ℕ} (hκ : κ ≤ 64) {P : E[X]} (hP : P.natDegree ≤ 2 ^ κ - 1) :
    msgPoly κ (lowMsg κ P) = P := by
  rw [msgPoly_lowMsg hκ, (modByMonic_eq_self_iff (vanE_monic κ)).mpr]
  rw [degree_eq_natDegree (vanE_monic κ).ne_zero, natDegree_vanE]
  refine degree_le_natDegree.trans_lt ?_
  have := Nat.one_le_two_pow (n := κ)
  exact_mod_cast (show P.natDegree < 2 ^ κ by omega)

/-! ## Out-of-domain separation -/

/-- The out-of-domain value of a message: its claim against `eq_eval(z, ·)`. -/
def oodVal {m κ : ℕ} (z : List E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) : E :=
  claimSum (eqEval z) g

/-- Members of the list of `Q'` with distinct messages differ at `z`. -/
def OodSep (P' : LevelCode) {m : ℕ} (Q : (Fin m → Bool) → Fin P'.n → E) (z : List E) : Prop :=
  ∀ U ∈ tlist P'.dom Q (P'.thr 0) P'.deg, ∀ U' ∈ tlist P'.dom Q (P'.thr 0) P'.deg,
    msgT P'.κ U ≠ msgT P'.κ U' → oodVal z (msgT P'.κ U) ≠ oodVal z (msgT P'.κ U')

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
/-- **Out-of-domain separation of the next list** (Annex B, `lem:ood`): at most
`C(|list|, 2) κ |E|^(κ−1)` points break `OodSep`, two members with distinct messages agreeing
there. -/
theorem card_oodSep_bad_le (P' : LevelCode) {m κ : ℕ} (hκ : κ = m + P'.κ)
    (Q : (Fin m → Bool) → Fin P'.n → E) :
    (univ.filter fun f : Fin κ → E ↦ ¬ OodSep P' Q (List.ofFn f)).card ≤
      (tlist P'.dom Q (P'.thr 0) P'.deg).card.choose 2 * (κ * Fintype.card E ^ (κ - 1)) := by
  set L := tlist P'.dom Q (P'.thr 0) P'.deg
  set M := L.image (msgT P'.κ)
  let dec : ((Fin m → Bool) → (Fin P'.κ → Bool) → E) → CMlPolynomialEval E κ :=
    fun g ↦ tableOf (joinMsg hκ g)
  have hval : ∀ U (f : Fin κ → E), oodVal (List.ofFn f) (msgT P'.κ U) =
      evalMle (dec (msgT P'.κ U)) (Vector.ofFn f) := by
    intro U f
    rw [oodVal, ← sum_joinMsg hκ, ← sum_eqEval_vec, Vector.toList_ofFn]
  have hinj : Set.InjOn dec M := fun g _ g' _ h ↦ joinMsg_injective hκ (tableOf_injective h)
  refine (card_le_card_of_injOn Vector.ofFn (fun f hf ↦ ?_) fun f _ f' _ h ↦ ?_).trans
    ((card_ood_collision_image_le M dec hinj).trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 card_image_le)))
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, OodSep, not_forall,
      exists_prop, not_not] at hf ⊢
    obtain ⟨U, hU, U', hU', hne, heq⟩ := hf
    exact ⟨_, mem_image_of_mem _ hU, _, mem_image_of_mem _ hU', hne,
      by rw [← hval, ← hval, heq]⟩
  · funext k
    have := congrArg (fun v : Vector E κ ↦ v[k]) h
    simpa using this

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

/-! ## The query step -/

/-- The normalized subspace polynomial `Ŵ_κ` over `E`. -/
noncomputable def hatE (κ : ℕ) : E[X] := (normVanishing κ).map (algebraMap K E)

theorem hatE_eq (κ : ℕ) :
    hatE κ = vanE κ * C (ofK (vanishingAt κ (basisVec κ))⁻¹) := by
  rw [hatE, normVanishing, Polynomial.map_mul, Polynomial.map_C, vanE, mul_comm]
  rfl

theorem eval_hatE (κ : ℕ) (x : K) : (hatE κ).eval (ofK x) = ofK (normVanishingAt κ x) := by
  rw [hatE, eval_map, show ofK x = algebraMap K E x from rfl, eval₂_hom, eval_normVanishing]
  rfl

theorem natDegree_hatE_mul_le {κ : ℕ} (hκ : κ < 64) (H : E[X]) :
    (hatE κ * H).natDegree ≤ 2 ^ κ + H.natDegree := by
  refine natDegree_mul_le.trans (Nat.add_le_add_right ?_ _)
  rw [hatE, natDegree_map, natDegree_normVanishing hκ]

/-- The low part of `P_g + Ŵ_κ H` is `g`. -/
theorem lowMsg_msgPoly_add_hat {κ : ℕ} (hκ : κ ≤ 64) (g : (Fin κ → Bool) → E) (H : E[X]) :
    lowMsg κ (msgPoly κ g + hatE κ * H) = g := by
  rw [hatE_eq, mul_assoc]
  exact lowMsg_msgPoly_add hκ g _

/-- **The doom after the query positions**: every member of the list of the next oracle `Q'`
violates the running claim `(Φ, σ)`, the out-of-domain claim `(eq(z, ·), y)`, or the consistency
claim at a queried column, whose value the verifier derives is `c' q`. -/
def QDoom (P P' : LevelCode) (hκ : P.κ = P'.ℓ + P'.κ) (Q' : (Fin P'.ℓ → Bool) → Fin P'.n → E)
    (Φ : List E → E) (σ : E) (z : List E) (y : E) (c' : ℕ → E) (qs : List ℕ) : Prop :=
  ∀ U ∈ tlist P'.dom Q' (P'.thr 0) P'.deg,
    ∑ x, Φ (bitsL x) * joinMsg hκ (msgT P'.κ U) x ≠ σ ∨ oodVal z (msgT P'.κ U) ≠ y ∨
      ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (msgT P'.κ U)) q ≠ c' q

/-- **The query step** (Annex B, proof of `thm:rbr`, "Query message"). Let every tuple of degree
at most `2^κ − 1 + ℓ` close to the folded word `C` violate the running claim, the out-of-domain
point separate the next list, and `c' q` be `C` at `x_q` corrected by the high part `Ŵ_κ H`
(`deg H < ℓ`). The positions that break `QDoom` all lie in a set of at most `A − 1` columns. -/
theorem exists_agreeSet (P P' : LevelCode) (hκ : P.κ = P'.ℓ + P'.κ) (hA : 1 ≤ P.A)
    (Q' : (Fin P'.ℓ → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (H : E[X]) (hH : H.natDegree + 1 ≤ P.ℓ) (c' : ℕ → E)
    (hc' : ∀ q (h : q < P.n), c' q = C ⟨q, h⟩ + (hatE P.κ * H).eval (P.dom ⟨q, h⟩))
    (hviol : TViol P.κ P.dom (fun _ : Fin 0 → Bool ↦ C) Φ σ (P.thr P.ℓ) P.deg)
    (hsep : OodSep P' Q' z) :
    ∃ S : Finset (Fin P.n), S.card + 1 ≤ P.A ∧ ∀ qs : List ℕ,
      ¬ QDoom P P' hκ Q' Φ σ z y c' qs → ∀ q ∈ qs, ∀ h : q < P.n,
        (⟨q, h⟩ : Fin P.n) ∈ S := by
  classical
  have h64 := P.κ_lt
  set L := tlist P'.dom Q' (P'.thr 0) P'.deg
  by_cases hex : ∃ U ∈ L, oodVal z (msgT P'.κ U) = y
  · obtain ⟨U₀, hU₀, ho⟩ := hex
    set g := joinMsg hκ (msgT P'.κ U₀)
    set Pst := msgPoly P.κ g + hatE P.κ * H
    -- The one message consistent with the answer, as a single polynomial.
    have huniq : ∀ U ∈ L, oodVal z (msgT P'.κ U) = y → msgT P'.κ U = msgT P'.κ U₀ := by
      intro U hU h₁
      by_contra hne
      exact hsep U hU U₀ hU₀ hne (h₁.trans ho.symm)
    have hdeg : DegLE P.deg (fun _ : Fin 0 → Bool ↦ Pst) := fun _ ↦ by
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · have := natDegree_msgPoly_lt (show P.κ ≤ 64 by omega) g
        have h1 := Nat.one_le_two_pow (n := P.κ)
        have : (msgPoly P.κ g).natDegree < 2 ^ P.κ := by
          by_cases h0 : msgPoly P.κ g = 0
          · rw [h0, natDegree_zero]; omega
          · exact (natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast this)
        simp only [LevelCode.deg]; omega
      · have := natDegree_hatE_mul_le h64 H
        have h1 := Nat.one_le_two_pow (n := P.κ)
        simp only [LevelCode.deg]; omega
    have hclaim : tclaim P.κ Φ (fun _ : Fin 0 → Bool ↦ Pst) = ∑ x, Φ (bitsL x) * g x := by
      rw [tclaim, claimSum_zero, lowMsg_msgPoly_add_hat (by omega)]
    set S := agreeT P.dom (fun _ : Fin 0 → Bool ↦ Pst) (fun _ ↦ C)
    by_cases hS : P.A ≤ S.card
    · -- `P*` is close, so it violates the running claim, and so does every member: no escape.
      have hv := hviol _ hdeg (by simpa [LevelCode.thr] using hS)
      rw [hclaim] at hv
      refine ⟨∅, by simpa using hA, fun qs hqs ↦ absurd ?_ hqs⟩
      intro U hU
      by_cases h₁ : oodVal z (msgT P'.κ U) = y
      · rw [huniq U hU h₁]; exact Or.inl hv
      · exact Or.inr (Or.inl h₁)
    · refine ⟨S, by omega, fun qs hqs q hq hlt ↦ ?_⟩
      simp only [QDoom, not_forall, not_or, not_not, exists_prop, not_exists, not_and] at hqs
      obtain ⟨U, hU, -, h₁, hall⟩ := hqs
      have he := hall q hq
      rw [huniq U hU h₁] at he
      rw [encAt, dite_eq_left_of_eq_true (eq_true hlt), hc' q hlt,
        enc_eq_evalOnPoints (show P.κ + P.R ≤ 64 from P.h64)] at he
      rw [mem_agreeT]
      intro _
      change (msgPoly P.κ g).eval (P.dom ⟨q, hlt⟩) = _ at he
      simp only [Pst, Polynomial.eval_add]
      rw [he]
      linear_combination (CharTwo.two_eq_zero (R := E)) *
        (eval (P.dom ⟨q, hlt⟩) (hatE P.κ * H))
  · refine ⟨∅, by simpa using hA, fun qs hqs ↦ absurd ?_ hqs⟩
    intro U hU
    by_contra h
    simp only [not_or, not_not] at h
    exact hex ⟨U, hU, h.2.1⟩

/-! ## The batching challenge -/

/-- The glued claim's weight against a member: the running weight, `λ` times the out-of-domain
weight and `λ²` times the consistency weight. -/
def gluedW (Φ : List E → E) (z : List E) (mu : ℕ) (qs : List ℕ) (lam : E) (x : List E) : E :=
  Φ x + lam * eqEval z x + lam * lam * Verifier.inducedWeight mu qs (powers lam qs.length) x

/-- The glued claim's value. -/
def gluedV (σ y : E) (qs : List ℕ) (c' : ℕ → E) (lam : E) : E :=
  σ + lam * y + lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * c' qs[k]

open Classical in
/-- **The batching step** (Annex B, proof of `thm:rbr`, "Batching challenge"): from `QDoom`, at
most `(t + 1)·|list|` values `λ` let a member of the next list satisfy the glued claim. -/
theorem card_lambda_bad_le (P P' : LevelCode) (hκ : P.κ = P'.ℓ + P'.κ)
    (Q' : (Fin P'.ℓ → Bool) → Fin P'.n → E) (Φ : List E → E) (σ : E) (z : List E)
    (y : E) (c' : ℕ → E) (qs : List ℕ) (hq : ∀ q ∈ qs, q < P.n)
    (hQ : QDoom P P' hκ Q' Φ σ z y c' qs) :
    (univ.filter fun lam : E ↦ ∃ U ∈ tlist P'.dom Q' (P'.thr 0) P'.deg,
        ∑ x, gluedW Φ z P.κ qs lam (bitsL x) * joinMsg hκ (msgT P'.κ U) x =
          gluedV σ y qs c' lam).card ≤
      (tlist P'.dom Q' (P'.thr 0) P'.deg).card * (qs.length + 1) := by
  set L := tlist P'.dom Q' (P'.thr 0) P'.deg
  refine card_filter_exists_le L _ fun U hU ↦ ?_
  set g := joinMsg hκ (msgT P'.κ U)
  have h64 : P.κ ≤ 64 := by have := P.h64; omega
  have hood : oodVal z (msgT P'.κ U) = ∑ x, eqEval z (bitsL x) * g x := by
    rw [oodVal, ← sum_joinMsg hκ]
  -- The discrepancy's coefficients: residual, the out-of-domain claim, the queries.
  let e : Fin qs.length → E := fun k ↦ encAt P.κ P.R g qs[k] - c' qs[k]
  let d : Fin (qs.length + 2) → E :=
    Fin.cons (∑ x, Φ (bitsL x) * g x - σ) (Fin.cons (oodVal z (msgT P'.κ U) - y) e)
  have hd : ∃ k, d k ≠ 0 := by
    rcases hQ U hU with h | h | ⟨q, hqm, hne⟩
    · exact ⟨0, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨1, by simpa [d, sub_eq_zero] using h⟩
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hqm
      exact ⟨(⟨k, hk⟩ : Fin qs.length).succ.succ, by
        simp only [d, Fin.cons_succ, e, ne_eq, sub_eq_zero]; exact hne⟩
  refine (card_le_card fun lam hlam ↦ ?_).trans
    ((card_powerBatch_eq_zero_le d hd).trans (by simp))
  simp only [mem_filter, mem_univ, true_and] at hlam ⊢
  have hind : ∑ x, Verifier.inducedWeight P.κ qs (powers lam qs.length) (bitsL x) * g x =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R g qs[k] := by
    rw [sum_inducedWeight_mul P.R h64 qs _ (length_powers lam _) hq, sum_zip_powers]
  have hsplit : ∑ x, gluedW Φ z P.κ qs lam (bitsL x) * g x =
      ∑ x, Φ (bitsL x) * g x + lam * oodVal z (msgT P'.κ U) +
        lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R g qs[k] := by
    rw [hood, ← hind]
    simp only [gluedW, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hsplit, gluedV] at hlam
  have hs : ∑ k : Fin qs.length, e k * lam ^ ((k : ℕ) + 1 + 1) =
      lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R g qs[k] -
        lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * c' qs[k] := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by simp only [e]; ring
  simp only [d, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, hs]
  linear_combination hlam

end
end LeanVM.Protocol.Whir.Sound
