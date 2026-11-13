/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerCore

  The affine combiner on one word over an extension field: exceptional triples, persistence, and
  the bound on the persistent exceptional pairs ([CWYZ26], Lemmas 4.4 and 4.5).
  Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDefs
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine combiners on one word: the persistent pairs

The setting of [CWYZ26], Sections 3 and 4, for one received word over a field `L` with
the domain and the challenges in a subfield `F` (the proof of its Theorem 5.2
packs the lanes of an interleaved word into one word over an extension of `F`;
`AffineCombinerPacking` does so). Fix `dom : ι ↪ F`, `n = |ι|`, and words `f g : ι → L`; write
`pt x` for the point `dom x ∈ L`.

* `IsExcTriple dom f g d A α β P`: `deg P ≤ d`, `P` agrees with `f + (α + β x) g` on at least `A`
  coordinates (`agreeL`), and `P` has no witness `U`, `V` (`deg U ≤ d`, `deg V ≤ d - 1`,
  `P = U + (α + β X) V`, agreement loss at most one): the exceptional triples of [CWYZ26,
  Definition 3.1].
* `PersistentData dom f g d B α β P I H Lp`: `I` is a set of at least `B` agreement coordinates of
  `P`, and the rational function `G = H / Lp`, `deg H ≤ d`, `Lp ≠ 0`, `deg Lp ≤ 1`, is defined on
  `I` and equals `g` there; then `F = P - (α + β X) G` equals `f` on `I` as well. `IsPersistent`
  is its existence: the persistent triples of [CWYZ26, Section 4.1], with `Lp` nonvanishing on
  `I` (the form the proof of Claim 4.8 produces).
* `persSet`, `nonpersSet`: the pairs `(α, β)` with an exceptional triple that is, resp. is not,
  persistent; `excSetL ⊆ persSet ∪ nonpersSet`.

## Main statement

`card_persSet_le` ([CWYZ26, Lemma 4.5], with Lemma 4.4): if `B² > n (d + 1)`,
then `|persSet| ≤ jl n B (d + 1) · max(|F|, C(n, 2))`. The rational pairs `(F, G)` explaining the
persistent triples (`key`) agree pairwise on at most `d + 1` coordinates (`card_inter_le_of_key_ne`),
so the Johnson bound counts at most `jl n B (d + 1)` of them; one pair accounts for at most
`C(n, 2)` exceptional pairs if it is a pair of polynomials of degrees `d` and `d - 1`
(`card_le_choose_of_polyPair`: two agreements outside the pair's own agreement set determine the
line), and for at most `|F|` otherwise (`card_le_of_not_polyPair`: the admissible `(α, β)` form a
proper `F`-affine subspace of `F²`).
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Defs

variable (dom : ι ↪ F) (f g : ι → L)

/-- The domain point `dom x`, in `L`. -/
def pt (x : ι) : L := algebraMap F L (dom x)

omit [Fintype ι] [DecidableEq ι] in
theorem pt_injective : Function.Injective (pt (L := L) dom) :=
  (algebraMap F L).injective.comp dom.injective

/-- The affine combiner `α + β X` over `L`. -/
noncomputable def linL (α β : F) : L[X] := C (algebraMap F L α) + C (algebraMap F L β) * X

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem eval_linL (α β : F) (z : L) :
    (linL (L := L) α β).eval z = algebraMap F L α + algebraMap F L β * z := by
  simp [linL]

omit [Fintype ι] [DecidableEq ι] in
theorem natDegree_linL_le (α β : F) : (linL (L := L) α β).natDegree ≤ 1 := by
  unfold linL
  refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
  exact (natDegree_C_mul_le _ _).trans (by simp)

open Classical in
/-- The coordinates where `P` agrees with `f + (α + β x) g`. -/
noncomputable def agreeL (P : L[X]) (α β : F) : Finset ι :=
  univ.filter fun x ↦ P.eval (pt dom x) = f x + (linL α β).eval (pt dom x) * g x

omit [DecidableEq ι] in
@[simp] theorem mem_agreeL (P : L[X]) (α β : F) (x : ι) :
    x ∈ agreeL dom f g P α β ↔ P.eval (pt dom x) = f x + (linL α β).eval (pt dom x) * g x := by
  classical
  simp [agreeL]

open Classical in
/-- **A witness with agreement loss one** for `P` at `(α, β)`. -/
def IsWitnessL (d : ℕ) (α β : F) (P U V : L[X]) : Prop :=
  U.natDegree ≤ d ∧ V.natDegree ≤ d - 1 ∧ P = U + linL α β * V ∧
    ((agreeL dom f g P α β).filter fun x ↦ U.eval (pt dom x) ≠ f x ∨ V.eval (pt dom x) ≠ g x).card
      ≤ 1

/-- **An exceptional triple** ([CWYZ26, Definition 3.1]). -/
def IsExcTriple (d A : ℕ) (α β : F) (P : L[X]) : Prop :=
  P.natDegree ≤ d ∧ A ≤ (agreeL dom f g P α β).card ∧ ¬ ∃ U V, IsWitnessL dom f g d α β P U V

/-- **Persistence data**: `I` holds at least `B` agreement coordinates of `P`, on which
`G = H / Lp` is defined and equals `g`. -/
def PersistentData (d B : ℕ) (α β : F) (P : L[X]) (I : Finset ι) (H Lp : L[X]) : Prop :=
  I ⊆ agreeL dom f g P α β ∧ B ≤ I.card ∧ H.natDegree ≤ d ∧ Lp ≠ 0 ∧ Lp.natDegree ≤ 1 ∧
    ∀ x ∈ I, Lp.eval (pt dom x) ≠ 0 ∧ H.eval (pt dom x) = g x * Lp.eval (pt dom x)

/-- **A persistent triple** ([CWYZ26, Section 4.1]). -/
def IsPersistent (d B : ℕ) (α β : F) (P : L[X]) : Prop :=
  ∃ I H Lp, PersistentData dom f g d B α β P I H Lp

variable [Fintype F]

open Classical in
/-- The exceptional pairs of one word. -/
noncomputable def excSetL (d A : ℕ) : Finset (F × F) :=
  univ.filter fun p ↦ ∃ P, IsExcTriple dom f g d A p.1 p.2 P

open Classical in
/-- The pairs with a persistent exceptional triple. -/
noncomputable def persSet (d A B : ℕ) : Finset (F × F) :=
  univ.filter fun p ↦ ∃ P, IsExcTriple dom f g d A p.1 p.2 P ∧ IsPersistent dom f g d B p.1 p.2 P

open Classical in
/-- The pairs with a non-persistent exceptional triple. -/
noncomputable def nonpersSet (d A B : ℕ) : Finset (F × F) :=
  univ.filter fun p ↦ ∃ P, IsExcTriple dom f g d A p.1 p.2 P ∧
    ¬ IsPersistent dom f g d B p.1 p.2 P

omit [DecidableEq ι] in
/-- Every exceptional pair has a persistent or a non-persistent exceptional triple. -/
theorem card_excSetL_le (d A B : ℕ) :
    (excSetL dom f g d A).card ≤ (persSet dom f g d A B).card + (nonpersSet dom f g d A B).card := by
  classical
  refine (card_le_card fun p hp ↦ ?_).trans (card_union_le _ _)
  obtain ⟨P, hP⟩ := (mem_filter.mp hp).2
  by_cases h : IsPersistent dom f g d B p.1 p.2 P
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, P, hP, h⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, P, hP, h⟩)

end Defs

/-! ## Root counting at injective points -/

omit [Fintype ι] [DecidableEq ι] in
/-- A nonzero polynomial vanishes at no more of a family of distinct points than its degree. -/
theorem card_le_natDegree_of_eval_eq_zero {e : ι → L} (he : Function.Injective e) {D : L[X]}
    (hD : D ≠ 0) (S : Finset ι) (hS : ∀ x ∈ S, D.eval (e x) = 0) : S.card ≤ D.natDegree := by
  classical
  calc S.card ≤ D.roots.toFinset.card :=
        Finset.card_le_card_of_injOn e (fun x hx ↦ by
          rw [Finset.mem_coe, Multiset.mem_toFinset]
          exact (mem_roots hD).mpr (hS x hx)) he.injOn
    _ ≤ D.roots.card := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := card_roots' D

/-! ## Rational pairs -/

section Key

variable (dom : ι ↪ F) (f g : ι → L)

/-- The rational pair `(P - (α + β X) H / Lp, H / Lp)` of persistence data, in `L(X)`. -/
noncomputable def key (α β : F) (P H Lp : L[X]) : RatFunc L × RatFunc L :=
  (algebraMap L[X] (RatFunc L) P - algebraMap L[X] (RatFunc L) (linL α β) *
      (algebraMap L[X] (RatFunc L) H / algebraMap L[X] (RatFunc L) Lp),
    algebraMap L[X] (RatFunc L) H / algebraMap L[X] (RatFunc L) Lp)

/-- **Distinct rational pairs agree on at most `d + 1` coordinates** ([CWYZ26, Lemma 4.5]): if
`G ≠ G'`, then `H Lp' - H' Lp` vanishes on `I ∩ I'`; otherwise `F ≠ F'`, and
`(P - P') Lp - ((α - α') + (β - β') X) H = (F - F') Lp` does. Both have degree at most `d + 1`. -/
theorem card_inter_le_of_key_ne {d B : ℕ} {α β α' β' : F} {P P' I I' H H' Lp Lp'}
    (hP : P.natDegree ≤ d) (hP' : P'.natDegree ≤ d)
    (h : PersistentData dom f g d B α β P I H Lp) (h' : PersistentData dom f g d B α' β' P' I' H' Lp')
    (hne : key α β P H Lp ≠ key α' β' P' H' Lp') : (I ∩ I').card ≤ d + 1 := by
  obtain ⟨hI, -, hH, hL, hL1, hval⟩ := h
  obtain ⟨hI', -, hH', hL', hL1', hval'⟩ := h'
  have hLa : (algebraMap L[X] (RatFunc L)) Lp ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective L)).mpr hL
  have hLa' : (algebraMap L[X] (RatFunc L)) Lp' ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective L)).mpr hL'
  by_cases hG : (algebraMap L[X] (RatFunc L)) H / (algebraMap L[X] (RatFunc L)) Lp = (algebraMap L[X] (RatFunc L)) H' / (algebraMap L[X] (RatFunc L)) Lp'
  · -- Same `G`: then `F ≠ F'`.
    set D := (P - P') * Lp - (linL α β - linL α' β') * H with hDdef
    have hD : D ≠ 0 := by
      intro hD0
      apply hne
      have h1 : (algebraMap L[X] (RatFunc L)) P * (algebraMap L[X] (RatFunc L)) Lp - (algebraMap L[X] (RatFunc L)) P' * (algebraMap L[X] (RatFunc L)) Lp = ((algebraMap L[X] (RatFunc L)) (linL α β) - (algebraMap L[X] (RatFunc L)) (linL α' β')) * (algebraMap L[X] (RatFunc L)) H := by
        have := congrArg (algebraMap L[X] (RatFunc L)) hD0
        simp only [hDdef, map_sub, map_mul, map_zero] at this
        linear_combination this
      refine Prod.ext ?_ hG
      simp only [key]
      rw [← hG]
      field_simp
      linear_combination h1
    refine (card_le_natDegree_of_eval_eq_zero (pt_injective dom) hD _ fun x hx ↦ ?_).trans ?_
    · obtain ⟨hx, hx'⟩ := mem_inter.mp hx
      have e1 := (mem_agreeL dom f g P α β x).mp (hI hx)
      have e2 := (mem_agreeL dom f g P' α' β' x).mp (hI' hx')
      have e3 := (hval x hx).2
      simp only [hDdef, eval_sub, eval_mul, e1, e2, e3]
      ring
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_mul_le).trans (add_le_add ((natDegree_sub_le _ _).trans (max_le hP hP'))
          hL1)
      · refine (natDegree_mul_le).trans ?_
        have := (natDegree_sub_le (linL (L := L) α β) (linL α' β')).trans
          (max_le (natDegree_linL_le α β) (natDegree_linL_le α' β'))
        omega
  · -- Different `G`.
    set D := H * Lp' - H' * Lp with hDdef
    have hD : D ≠ 0 := by
      intro hD0
      apply hG
      rw [div_eq_div_iff hLa hLa']
      have := congrArg (algebraMap L[X] (RatFunc L)) hD0
      simp only [hDdef, map_sub, map_mul, map_zero] at this
      linear_combination this
    refine (card_le_natDegree_of_eval_eq_zero (pt_injective dom) hD _ fun x hx ↦ ?_).trans ?_
    · obtain ⟨hx, hx'⟩ := mem_inter.mp hx
      simp only [hDdef, eval_sub, eval_mul, (hval x hx).2, (hval' x hx').2]
      ring
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_mul_le).trans (by omega)
      · exact (natDegree_mul_le).trans (by omega)

end Key

/-! ## One rational pair -/

section OnePair

variable (dom : ι ↪ F) (f g : ι → L) {d A : ℕ}

/-- **A polynomial pair** ([CWYZ26, Lemma 4.4], first case): if `deg F₀ ≤ d` and `deg G₀ ≤ d - 1`,
at most `C(n, 2)` pairs `(α, β)` make `F₀ + (α + β X) G₀` exceptional. Such a pair has two
agreement coordinates where `G₀ ≠ g`, and these two determine the line `α + β x`. -/
theorem card_le_choose_of_polyPair (F₀ G₀ : L[X]) (hF : F₀.natDegree ≤ d)
    (hG : G₀.natDegree ≤ d - 1) (Ps : Finset (F × F))
    (hPs : ∀ p ∈ Ps, IsExcTriple dom f g d A p.1 p.2 (F₀ + linL p.1 p.2 * G₀)) :
    Ps.card ≤ (Fintype.card ι).choose 2 := by
  classical
  let bad : F × F → Finset ι := fun p ↦ (agreeL dom f g (F₀ + linL p.1 p.2 * G₀) p.1 p.2).filter
    fun x ↦ F₀.eval (pt dom x) ≠ f x ∨ G₀.eval (pt dom x) ≠ g x
  have hbad : ∀ p ∈ Ps, 2 ≤ (bad p).card := by
    intro p hp
    by_contra hlt
    have hle : (bad p).card ≤ 1 := by omega
    exact (hPs p hp).2.2 ⟨F₀, G₀, hF, hG, rfl, by convert hle⟩
  -- At a coordinate of `bad p`, `G₀ ≠ g` and `(α + β x)(g - G₀) = F₀ - f`.
  have hline : ∀ p, ∀ x ∈ bad p, G₀.eval (pt dom x) ≠ g x ∧
      (linL (L := L) p.1 p.2).eval (pt dom x) * (g x - G₀.eval (pt dom x)) =
        F₀.eval (pt dom x) - f x := by
    intro p x hx
    obtain ⟨hx, hne⟩ := mem_filter.mp hx
    have e := (mem_agreeL dom f g _ p.1 p.2 x).mp hx
    simp only [eval_add, eval_mul] at e
    refine ⟨fun hG' ↦ ?_, by linear_combination -e⟩
    rw [hG'] at e
    exact hne.elim (fun h ↦ h (by linear_combination e)) fun h ↦ h hG'
  have hex : ∀ p ∈ Ps, ∃ s ⊆ bad p, s.card = 2 := fun p hp ↦ exists_subset_card_eq (hbad p hp)
  choose! s hs hs2 using hex
  refine (card_le_card_of_injOn s (fun p hp ↦ ?_) fun p hp p' hp' heq ↦ ?_).trans
    (card_powersetCard 2 (univ : Finset ι)).le |>.trans (by rw [card_univ])
  · exact mem_coe.mpr (mem_powersetCard.mpr ⟨subset_univ _, hs2 p hp⟩)
  · obtain ⟨x, y, hxy, hsxy⟩ := card_eq_two.mp (hs2 p hp)
    have hx : x ∈ s p := by rw [hsxy]; simp
    have hy : y ∈ s p := by rw [hsxy]; simp
    have hx' : x ∈ s p' := heq ▸ hx
    have hy' : y ∈ s p' := heq ▸ hy
    -- The two lines agree at `x` and at `y`.
    have hpt (z : ι) (hz : z ∈ s p) (hz' : z ∈ s p') :
        (linL (L := L) p.1 p.2).eval (pt dom z) = (linL (L := L) p'.1 p'.2).eval (pt dom z) := by
      obtain ⟨hG1, e1⟩ := hline p z (hs p hp hz)
      obtain ⟨-, e2⟩ := hline p' z (hs p' hp' hz')
      have hgz : g z - G₀.eval (pt dom z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hG1)
      exact mul_right_cancel₀ hgz (e1.trans e2.symm)
    have ex := hpt x hx hx'
    have ey := hpt y hy hy'
    simp only [eval_linL] at ex ey
    have hdiff : pt (L := L) dom x - pt dom y ≠ 0 :=
      sub_ne_zero.mpr fun h ↦ hxy (pt_injective dom h)
    have hβ : algebraMap F L p.2 = algebraMap F L p'.2 :=
      mul_right_cancel₀ hdiff (by linear_combination ex - ey)
    have hα : algebraMap F L p.1 = algebraMap F L p'.1 := by
      rw [hβ] at ex; linear_combination ex
    exact Prod.ext ((algebraMap F L).injective hα) ((algebraMap F L).injective hβ)

/-- The polynomials `P'` with `deg P' ≤ d`, times `Lp`, as an `F`-submodule of `L[X]`. -/
noncomputable def timesLp (d : ℕ) (Lp : L[X]) : Submodule F L[X] where
  carrier := {Q | ∃ P', P'.natDegree ≤ d ∧ P' * Lp = Q}
  add_mem' := by
    rintro _ _ ⟨P₁, h₁, rfl⟩ ⟨P₂, h₂, rfl⟩
    exact ⟨P₁ + P₂, (natDegree_add_le _ _).trans (max_le h₁ h₂), by ring⟩
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro c _ ⟨P₁, h₁, rfl⟩
    refine ⟨c • P₁, ?_, by rw [smul_mul_assoc]⟩
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
    exact (natDegree_C_mul_le _ _).trans h₁

/-- `(a, b) ↦ (a + b X) H` as an `F`-linear map. -/
noncomputable def linMul (H : L[X]) : (F × F) →ₗ[F] L[X] where
  toFun p := linL p.1 p.2 * H
  map_add' p p' := by
    simp only [linL, Prod.fst_add, Prod.snd_add, map_add]
    ring
  map_smul' c p := by
    obtain ⟨a, b⟩ := p
    show linL (c * a) (c * b) * H = c • (linL a b * H)
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
    simp only [linL, map_mul]
    ring

/-- **A non-polynomial pair** ([CWYZ26, Lemma 4.4], second case), with the rational pair
`(P₀ - (α₀ + β₀ X) H₀ / Lp₀, H₀ / Lp₀)` written by its numerators. If it is not a pair of
polynomials of degrees `d` and `d - 1`, at most `|F|` pairs `(α, β)` make
`P₀ + (α - α₀ + (β - β₀) X) H₀ / Lp₀` a polynomial of degree at most `d`: they form a proper
`F`-affine subspace of `F²`. -/
theorem card_le_of_not_polyPair [Fintype F] (P₀ H₀ Lp₀ : L[X]) (hL : Lp₀ ≠ 0) (hP₀ : P₀.natDegree ≤ d)
    (α₀ β₀ : F)
    (hnot : ¬ ∃ F₀ G₀ : L[X], F₀.natDegree ≤ d ∧ G₀.natDegree ≤ d - 1 ∧
      F₀ * Lp₀ = P₀ * Lp₀ - linL α₀ β₀ * H₀ ∧ G₀ * Lp₀ = H₀)
    (Ps : Finset (F × F))
    (hPs : ∀ p ∈ Ps, ∃ P' : L[X], P'.natDegree ≤ d ∧
      P' * Lp₀ = P₀ * Lp₀ + (linL p.1 p.2 - linL α₀ β₀) * H₀) :
    Ps.card ≤ Fintype.card F := by
  classical
  set W := (timesLp d Lp₀).comap (linMul (F := F) H₀) with hW
  have hlin (p : F × F) : linMul (F := F) H₀ p = linL p.1 p.2 * H₀ := rfl
  have hWtop : W ≠ ⊤ := by
    intro htop
    have h10 : ((1, 0) : F × F) ∈ W := htop ▸ Submodule.mem_top
    have h01 : ((0, 1) : F × F) ∈ W := htop ▸ Submodule.mem_top
    have h00 : ((α₀, β₀) : F × F) ∈ W := htop ▸ Submodule.mem_top
    obtain ⟨G₀, hG₀, eG⟩ := h10
    obtain ⟨G₁, hG₁, eG₁⟩ := h01
    obtain ⟨Q₀, hQ₀, eQ⟩ := h00
    simp only [hlin, linL, map_one, map_zero, zero_mul, add_zero, one_mul,
      zero_add] at eG eG₁ eQ
    -- `G₁ = X G₀`, so `deg G₀ ≤ d - 1`.
    have hX : G₁ = X * G₀ := mul_right_cancel₀ hL (by rw [eG₁, mul_assoc, eG])
    have hG₀' : G₀.natDegree ≤ d - 1 := by
      rcases eq_or_ne G₀ 0 with h0 | h0
      · simp [h0]
      · rw [hX, natDegree_X_mul h0] at hG₁; omega
    refine hnot ⟨P₀ - Q₀, G₀, (natDegree_sub_le _ _).trans (max_le hP₀ hQ₀), hG₀', ?_, eG⟩
    rw [sub_mul, eQ]
    simp only [linL]
  -- `Ps - (α₀, β₀)` lies in `W`, a proper subspace.
  have hcardW : (univ.filter fun v : F × F ↦ v ∈ W).card ≤ Fintype.card F := by
    have hrank : Module.finrank F W < 2 := by
      have := Submodule.finrank_lt hWtop
      rwa [Module.finrank_prod, Module.finrank_self] at this
    rw [← Fintype.card_subtype, Module.card_eq_pow_finrank (K := F)]
    calc Fintype.card F ^ Module.finrank F W ≤ Fintype.card F ^ 1 :=
          Nat.pow_le_pow_right Fintype.card_pos (by omega)
      _ = Fintype.card F := pow_one _
  refine le_trans (card_le_card_of_injOn (fun p ↦ p - (α₀, β₀)) (fun p hp ↦ ?_)
    fun p _ p' _ h ↦ sub_left_injective h) hcardW
  obtain ⟨P', hP', e⟩ := hPs p hp
  refine mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, P' - P₀, (natDegree_sub_le _ _).trans
    (max_le hP' hP₀), ?_⟩)
  rw [hlin, sub_mul, e]
  simp only [linL, Prod.fst_sub, Prod.snd_sub, map_sub]
  ring

end OnePair

/-! ## The persistent pairs -/

/-- **The persistent exceptional pairs** ([CWYZ26, Lemma 4.5]): if `B² > n (d + 1)`, at most `jl n B (d + 1) · max(|F|, C(n, 2))` pairs `(α, β)` have a persistent
exceptional triple. -/
theorem card_persSet_le [Fintype F] (dom : ι ↪ F) (f g : ι → L) {d A B : ℕ}
    (hgap : Fintype.card ι * (d + 1) < B * B) :
    (persSet dom f g d A B).card ≤
      jl (Fintype.card ι) B (d + 1) * max (Fintype.card F) ((Fintype.card ι).choose 2) := by
  classical
  have hex : ∀ p ∈ persSet dom f g d A B, ∃ P I H Lp, IsExcTriple dom f g d A p.1 p.2 P ∧
      PersistentData dom f g d B p.1 p.2 P I H Lp := by
    intro p hp
    obtain ⟨P, he, I, H, Lp, hpd⟩ := (mem_filter.mp hp).2
    exact ⟨P, I, H, Lp, he, hpd⟩
  choose! P I H Lp hPe hPd using hex
  set S := persSet dom f g d A B
  let κ : F × F → RatFunc L × RatFunc L := fun p ↦ key p.1 p.2 (P p) (H p) (Lp p)
  set K := S.image κ
  -- The rational pairs: at most `jl n B (d + 1)` of them.
  have hK : K.card ≤ jl (Fintype.card ι) B (d + 1) := by
    have hrep : ∀ k ∈ K, ∃ p ∈ S, κ p = k := fun k hk ↦ mem_image.mp hk
    choose! rep hrep1 hrep2 using hrep
    refine card_le_jl K (fun k ↦ I (rep k)) B (d + 1)
      (fun k hk ↦ (hPd _ (hrep1 k hk)).2.1) (fun k hk k' hk' hne ↦ ?_) hgap
    refine card_inter_le_of_key_ne dom f g (hPe _ (hrep1 k hk)).1 (hPe _ (hrep1 k' hk')).1
      (hPd _ (hrep1 k hk)) (hPd _ (hrep1 k' hk')) ?_
    change κ (rep k) ≠ κ (rep k')
    rw [hrep2 k hk, hrep2 k' hk']
    exact hne
  -- Each rational pair: at most `max(|F|, C(n, 2))` pairs `(α, β)`.
  have hfib : ∀ k ∈ K, (S.filter fun p ↦ κ p = k).card ≤
      max (Fintype.card F) ((Fintype.card ι).choose 2) := by
    intro k hk
    obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hk
    obtain ⟨-, -, -, hL₀, -, -⟩ := hPd p₀ hp₀
    have hLa : (algebraMap L[X] (RatFunc L)) (Lp p₀) ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective L)).mpr hL₀
    -- A pair in the fiber satisfies `P Lp₀ = P₀ Lp₀ + (lin - lin₀) H₀`.
    have hfiber : ∀ p ∈ S.filter fun p ↦ κ p = κ p₀,
        P p * Lp p₀ = P p₀ * Lp p₀ + (linL p.1 p.2 - linL p₀.1 p₀.2) * H p₀ := by
      intro p hp
      obtain ⟨-, hκ⟩ := mem_filter.mp hp
      have h1 := congrArg Prod.fst hκ
      have h2 := congrArg Prod.snd hκ
      simp only [κ, key] at h1 h2
      rw [h2] at h1
      apply RatFunc.algebraMap_injective L
      simp only [map_add, map_mul, map_sub]
      field_simp at h1
      linear_combination h1
    by_cases hpoly : ∃ F₀ G₀ : L[X], F₀.natDegree ≤ d ∧ G₀.natDegree ≤ d - 1 ∧
        F₀ * Lp p₀ = P p₀ * Lp p₀ - linL p₀.1 p₀.2 * H p₀ ∧ G₀ * Lp p₀ = H p₀
    · obtain ⟨F₀, G₀, hF₀, hG₀, eF, eG⟩ := hpoly
      refine (card_le_choose_of_polyPair (A := A) dom f g F₀ G₀ hF₀ hG₀ _ fun p hp ↦ ?_).trans
        (le_max_right _ _)
      have hPp : P p = F₀ + linL p.1 p.2 * G₀ := by
        refine mul_right_cancel₀ hL₀ ?_
        rw [hfiber p hp, add_mul, eF, mul_assoc, eG]
        ring
      rw [← hPp]
      exact hPe p (mem_filter.mp hp).1
    · exact (card_le_of_not_polyPair (P p₀) (H p₀) (Lp p₀) hL₀ (hPe p₀ hp₀).1 p₀.1 p₀.2 hpoly _
        fun p hp ↦ ⟨P p, (hPe p (mem_filter.mp hp).1).1, hfiber p hp⟩).trans (le_max_left _ _)
  calc S.card = ∑ k ∈ K, (S.filter fun p ↦ κ p = k).card := card_eq_sum_card_image κ S
    _ ≤ ∑ _k ∈ K, max (Fintype.card F) ((Fintype.card ι).choose 2) := sum_le_sum hfib
    _ = K.card * max (Fintype.card F) ((Fintype.card ι).choose 2) := by
        rw [sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hK

end
end LeanVM.Protocol.Whir.AffineCombiner
