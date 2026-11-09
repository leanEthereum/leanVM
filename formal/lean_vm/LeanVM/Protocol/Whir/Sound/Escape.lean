/-
  LeanVM.Protocol.Whir.Sound.Escape

  The escape counts of a WHIR level interface: the two out-of-domain points separate the next
  oracle's list except on `L²·(κ|E|^(κ−1))²` pairs; the query positions then catch the one member
  consistent with the out-of-domain answers unless they all land in an agreement set of fewer than
  `A` columns; and the level's batching challenge `λ` keeps every member violating the glued claim
  except at `(t + 2)·L` values.
-/

module

public import LeanVM.Protocol.Whir.Sound.Lanes
public import LeanVM.Protocol.ToArkLib.Whir.Ood
public import LeanVM.Protocol.ToArkLib.Whir.Counting

/-!
# Escapes at the level interface

Annex B (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "The
level interface", "OOD points", "Query message", "Batching challenge", for the deployed order of
messages (`verify_whir`, `crates/verifier/src/whir.rs:304-341`): the next oracle `Q'` and the
folded lane's high part, the two out-of-domain points `z₁, z₂` and answers `y₁, y₂`, the queries,
`λ`, the openings. The level's claims are glued with powers of `λ`: the running claim with `λ⁰`,
the out-of-domain claims with `λ`, `λ²`, the `t` consistency claims with `λ^(3+q)`.

The next level's members are tuples `U` of `ℓ'` lanes of degree below `2^κ'`; `msgT κ' U` is
their messages and `joinMsg` the message on the current level's `κ = ℓ' + κ'` variables.

* `OodSep2 P' Q' z₁ z₂`: distinct members of the list of `Q'` differ at `z₁` or at `z₂`;
  `card_oodSep2_bad_le`: at most `L² (κ |E|^(κ−1))²` pairs of points break it.
* `QDoom`: after the positions `qs`, every member violates the running claim, an out-of-domain
  claim, or the consistency claim at a queried column, `c' q` being the value the verifier
  derives from the opened row (`P(x_q)` corrected by the high part).
* `exists_agreeSet`: positions breaking `QDoom` all lie in a set of at most `A − 1` columns: the
  agreement set of the one member `U*` consistent with both answers, through the polynomial
  `P* = P_(g*) + Ŵ_κ H` of degree at most `2^κ − 1 + ℓ` (`H` the high part).
* `card_lambda_bad_le`: from `QDoom`, at most `(t + 2)·|list|` values `λ` let a member satisfy
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

/-- Tuples of degree below `2^κ` are determined by their messages. -/
theorem msgT_inj {m κ : ℕ} (hκ : κ ≤ 64) {U U' : (Fin m → Bool) → E[X]}
    (hU : DegLE (2 ^ κ - 1) U) (hU' : DegLE (2 ^ κ - 1) U') (h : msgT κ U = msgT κ U') :
    U = U' :=
  funext fun u ↦ by
    rw [← msgPoly_lowMsg_of_deg hκ (hU u), ← msgPoly_lowMsg_of_deg hκ (hU' u)]
    exact congrArg (msgPoly κ) (congrFun h u)

/-! ## Out-of-domain separation -/

/-- The out-of-domain value of a message: its claim against `eq_eval(z, ·)`. -/
def oodVal {m κ : ℕ} (z : List E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) : E :=
  claimSum (eqEval z) g

/-- Distinct members of the list of `Q'` differ at `z₁` or at `z₂`. -/
def OodSep2 (P' : LevelCode) {m : ℕ} (Q : (Fin m → Bool) → Fin P'.n → E) (z₁ z₂ : List E) :
    Prop :=
  ∀ U ∈ tlist P'.dom Q (P'.thr 0) (P'.deg 0), ∀ U' ∈ tlist P'.dom Q (P'.thr 0) (P'.deg 0),
    U ≠ U' → oodVal z₁ (msgT P'.κ U) ≠ oodVal z₁ (msgT P'.κ U') ∨
      oodVal z₂ (msgT P'.κ U) ≠ oodVal z₂ (msgT P'.κ U')

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
/-- Points as functions: the Schwartz-Zippel count of `card_evalMle_eq_le`. -/
theorem card_evalMle_eq_fn_le {κ : ℕ} {g g' : CMlPolynomialEval E κ} (hne : g ≠ g') :
    (univ.filter fun f : Fin κ → E ↦ evalMle g (Vector.ofFn f) = evalMle g' (Vector.ofFn f)).card ≤
      κ * Fintype.card E ^ (κ - 1) := by
  refine le_trans ?_ (card_evalMle_eq_le hne)
  refine card_le_card_of_injOn Vector.ofFn (fun f hf ↦ ?_) fun f _ f' _ h ↦ ?_
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
    exact hf
  · funext k
    have := congrArg (fun v : Vector E κ ↦ v[k]) h
    simpa using this

open Classical in
/-- **Out-of-domain separation at two points** (Annex B, `lem:ood`): at most
`|L|² (κ |E|^(κ−1))²` pairs of points leave two members of `L` with equal extensions at both. -/
theorem card_ood2_collision_le {X : Type*} {κ : ℕ} (L : Finset X)
    (dec : X → CMlPolynomialEval E κ) (hinj : Set.InjOn dec L) :
    (univ.filter fun zz : (Fin κ → E) × (Fin κ → E) ↦ ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧
        evalMle (dec U) (Vector.ofFn zz.1) = evalMle (dec U') (Vector.ofFn zz.1) ∧
        evalMle (dec U) (Vector.ofFn zz.2) = evalMle (dec U') (Vector.ofFn zz.2)).card ≤
      L.card ^ 2 * (κ * Fintype.card E ^ (κ - 1)) ^ 2 := by
  let S : X × X → Finset (Fin κ → E) := fun p ↦
    univ.filter fun f ↦ evalMle (dec p.1) (Vector.ofFn f) = evalMle (dec p.2) (Vector.ofFn f)
  let B : X × X → Finset ((Fin κ → E) × (Fin κ → E)) := fun p ↦
    if p.1 = p.2 then ∅ else S p ×ˢ S p
  calc _ ≤ ((L ×ˢ L).biUnion B).card := by
        refine card_le_card fun zz hz ↦ ?_
        simp only [mem_filter, mem_univ, true_and] at hz
        obtain ⟨U, hU, U', hU', hne, h1, h2⟩ := hz
        refine mem_biUnion.mpr ⟨(U, U'), mem_product.mpr ⟨hU, hU'⟩, ?_⟩
        simp only [B, hne, ite_false, mem_product, S, mem_filter, mem_univ, true_and]
        exact ⟨h1, h2⟩
    _ ≤ ∑ p ∈ L ×ˢ L, (B p).card := card_biUnion_le
    _ ≤ ∑ _p ∈ L ×ˢ L, (κ * Fintype.card E ^ (κ - 1)) ^ 2 := by
        refine sum_le_sum fun p hp ↦ ?_
        simp only [B]
        split_ifs with h
        · simp
        · rw [card_product, sq]
          have hp' := mem_product.mp hp
          have hS := card_evalMle_eq_fn_le (fun he ↦ h (hinj hp'.1 hp'.2 he))
          exact Nat.mul_le_mul hS hS
    _ = _ := by rw [sum_const, card_product, smul_eq_mul]; ring

open Classical in
/-- **Out-of-domain separation of the next list**: at most `|list|² (κ |E|^(κ−1))²` pairs of
points break `OodSep2`. -/
theorem card_oodSep2_bad_le (P' : LevelCode) {m κ : ℕ} (hκ : κ = m + P'.κ)
    (Q : (Fin m → Bool) → Fin P'.n → E) :
    (univ.filter fun zz : (Fin κ → E) × (Fin κ → E) ↦
        ¬ OodSep2 P' Q (List.ofFn zz.1) (List.ofFn zz.2)).card ≤
      (tlist P'.dom Q (P'.thr 0) (P'.deg 0)).card ^ 2 * (κ * Fintype.card E ^ (κ - 1)) ^ 2 := by
  set L := tlist P'.dom Q (P'.thr 0) (P'.deg 0)
  let dec : ((Fin m → Bool) → E[X]) → CMlPolynomialEval E κ :=
    fun U ↦ tableOf (joinMsg hκ (msgT P'.κ U))
  have hval : ∀ U (f : Fin κ → E), oodVal (List.ofFn f) (msgT P'.κ U) =
      evalMle (dec U) (Vector.ofFn f) := by
    intro U f
    rw [oodVal, ← sum_joinMsg hκ, ← sum_eqEval_vec, Vector.toList_ofFn]
  have hinj : Set.InjOn dec L := by
    intro U hU U' hU' h
    have h64 : P'.κ ≤ 64 := by have := P'.h64; omega
    exact msgT_inj h64 ((mem_tlist _ _ _ _ _).mp hU).1 ((mem_tlist _ _ _ _ _).mp hU').1
      (joinMsg_injective hκ (tableOf_injective h))
  refine (card_le_card fun zz hz ↦ ?_).trans (card_ood2_collision_le L dec hinj)
  simp only [mem_filter, mem_univ, true_and, OodSep2, not_forall, not_or, not_not,
    exists_prop] at hz ⊢
  obtain ⟨U, hU, U', hU', hne, h1, h2⟩ := hz
  exact ⟨U, hU, U', hU', hne, by rw [← hval, ← hval, h1], by rw [← hval, ← hval, h2]⟩

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
violates the running claim `(Φ, σ)`, an out-of-domain claim `(eq(z_s, ·), y_s)`, or the
consistency claim at a queried column, whose value the verifier derives is `c' q`. -/
def QDoom (P P' : LevelCode) (hκ : P.κ = P'.ℓ + P'.κ) (Q' : (Fin P'.ℓ → Bool) → Fin P'.n → E)
    (Φ : List E → E) (σ : E) (z₁ z₂ : List E) (y₁ y₂ : E) (c' : ℕ → E) (qs : List ℕ) : Prop :=
  ∀ U ∈ tlist P'.dom Q' (P'.thr 0) (P'.deg 0),
    ∑ x, Φ (bitsL x) * joinMsg hκ (msgT P'.κ U) x ≠ σ ∨ oodVal z₁ (msgT P'.κ U) ≠ y₁ ∨
      oodVal z₂ (msgT P'.κ U) ≠ y₂ ∨ ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (msgT P'.κ U)) q ≠ c' q

/-- **The query step** (Annex B, proof of `thm:rbr`, "Query message"). Let every tuple of degree
at most `2^κ − 1 + ℓ` close to the folded word `C` violate the running claim, the out-of-domain
points separate the next list, and `c' q` be `C` at `x_q` corrected by the high part `Ŵ_κ H`
(`deg H < ℓ`). The positions that break `QDoom` all lie in a set of at most `A − 1` columns. -/
theorem exists_agreeSet (P P' : LevelCode) (hκ : P.κ = P'.ℓ + P'.κ) (hA : 1 ≤ P.A)
    (Q' : (Fin P'.ℓ → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z₁ z₂ : List E) (y₁ y₂ : E) (H : E[X]) (hH : H.natDegree + 1 ≤ P.ℓ) (c' : ℕ → E)
    (hc' : ∀ q (h : q < P.n), c' q = C ⟨q, h⟩ + (hatE P.κ * H).eval (P.dom ⟨q, h⟩))
    (hviol : TViol P.κ P.dom (fun _ : Fin 0 → Bool ↦ C) Φ σ (P.thr P.ℓ) (P.deg P.ℓ))
    (hsep : OodSep2 P' Q' z₁ z₂) :
    ∃ S : Finset (Fin P.n), S.card + 1 ≤ P.A ∧ ∀ qs : List ℕ,
      ¬ QDoom P P' hκ Q' Φ σ z₁ z₂ y₁ y₂ c' qs → ∀ q ∈ qs, ∀ h : q < P.n,
        (⟨q, h⟩ : Fin P.n) ∈ S := by
  classical
  have h64 := P.κ_lt
  set L := tlist P'.dom Q' (P'.thr 0) (P'.deg 0)
  by_cases hex : ∃ U ∈ L, oodVal z₁ (msgT P'.κ U) = y₁ ∧ oodVal z₂ (msgT P'.κ U) = y₂
  · obtain ⟨U₀, hU₀, ho₁, ho₂⟩ := hex
    set g := joinMsg hκ (msgT P'.κ U₀)
    set Pst := msgPoly P.κ g + hatE P.κ * H
    -- The one member consistent with both answers, as a single polynomial.
    have huniq : ∀ U ∈ L, oodVal z₁ (msgT P'.κ U) = y₁ → oodVal z₂ (msgT P'.κ U) = y₂ → U = U₀ := by
      intro U hU h₁ h₂
      by_contra hne
      rcases hsep U hU U₀ hU₀ hne with h | h
      · exact h (h₁.trans ho₁.symm)
      · exact h (h₂.trans ho₂.symm)
    have hdeg : DegLE (P.deg P.ℓ) (fun _ : Fin 0 → Bool ↦ Pst) := fun _ ↦ by
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
      by_cases h₁ : oodVal z₁ (msgT P'.κ U) = y₁
      · by_cases h₂ : oodVal z₂ (msgT P'.κ U) = y₂
        · rw [huniq U hU h₁ h₂]; exact Or.inl hv
        · exact Or.inr (Or.inr (Or.inl h₂))
      · exact Or.inr (Or.inl h₁)
    · refine ⟨S, by omega, fun qs hqs q hq hlt ↦ ?_⟩
      simp only [QDoom, not_forall, not_or, not_not, exists_prop, not_exists, not_and] at hqs
      obtain ⟨U, hU, -, h₁, h₂, hall⟩ := hqs
      obtain rfl := huniq U hU h₁ h₂
      have he := hall q hq
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
    exact hex ⟨U, hU, h.2.1, h.2.2.1⟩

end
end LeanVM.Protocol.Whir.Sound
