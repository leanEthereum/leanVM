/-
The pole collapse of the affine combiner and of every polynomial combiner, and its consequence
that lists are pole pairs: Proposition 3.5 of the paper.

Everything in this file holds over an arbitrary field, with the signs that characteristic two
hides: the line of `lemmaA` is `α + β β₀ = -C(β₀)`.
-/
import Constructions.Flats

open Polynomial Finset
open scoped Classical

namespace Constructions

theorem ne_pole {α : Type*} {D : Finset α} {β₀ x : α} (hx : x ∈ D) (hβ₀ : β₀ ∉ D) : x ≠ β₀ :=
  fun h => hβ₀ (h ▸ hx)

variable {K : Type*} [Field K]

/-! ### Folds -/

/-- The fold of a pair of words by a polynomial combiner `Cb`: `f₁ + Cb(x) f₀`. -/
def polyFold (f₀ f₁ : K → K) (Cb : K[X]) : K → K := fun x => f₁ x + Cb.eval x * f₀ x

/-- The affine fold `f₁ + (α + β x) f₀` at the challenge `c = (α, β)`. -/
def affFold (f₀ f₁ : K → K) (c : K × K) : K → K := fun x => f₁ x + (c.1 + c.2 * x) * f₀ x

/-- The scalar fold `f₁ + γ f₀`. -/
def scalFold (f₀ f₁ : K → K) (γ : K) : K → K := fun x => f₁ x + γ * f₀ x

theorem affFold_eq_polyFold (f₀ f₁ : K → K) (c : K × K) :
    affFold f₀ f₁ c = polyFold f₀ f₁ (C c.1 + C c.2 * X) := by
  funext x
  simp [affFold, polyFold]

theorem scalFold_eq_polyFold (f₀ f₁ : K → K) (γ : K) :
    scalFold f₀ f₁ γ = polyFold f₀ f₁ (C γ) := by
  funext x
  simp [scalFold, polyFold]

/-- The word `1 / (x - β₀)`. -/
def poleWord (β₀ : K) : K → K := fun x => (x - β₀)⁻¹

/-- The word `w(x) / (x - β₀)`. -/
def poleNum (w : K → K) (β₀ : K) : K → K := fun x => w x * (x - β₀)⁻¹

/-- A word is `(d, T)`-close on `D` if a polynomial of degree at most `d` agrees with it on at
least `T` points of `D`. -/
def Close (D : Finset K) (w : K → K) (d T : ℕ) : Prop :=
  ∃ P : K[X], P.natDegree ≤ d ∧ T ≤ (agree D w P).card

theorem close_of_mem_RSList {D : Finset K} {w : K → K} {d T : ℕ} {P : K[X]}
    (h : P ∈ RSList D w (d + 1) T) : Close D w d T := by
  refine ⟨P, ?_, h.2⟩
  have h1 : P.degree < ((d + 1 : ℕ) : WithBot ℕ) := h.1
  by_cases hP : P = 0
  · simp [hP]
  · have := (natDegree_lt_iff_degree_lt hP).mpr h1
    omega

/-! ### The collapse -/

/-- The pointwise identity: `(α + β x) / (x - β₀) = β + (α + β β₀) / (x - β₀)`. -/
theorem pole_collapse {x β₀ : K} (hx : x ≠ β₀) (α β : K) :
    (α + β * x) / (x - β₀) = β + (α + β * β₀) / (x - β₀) := by
  have h : x - β₀ ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

/-- Division of a combiner by the pole: `Cb(x) / (x - β₀) = q(x) + Cb(β₀) / (x - β₀)` with
`q = Cb /ₘ (X - β₀)`, a polynomial of degree `deg Cb - 1`. -/
theorem combiner_collapse {x β₀ : K} (hx : x ≠ β₀) (Cb : K[X]) :
    Cb.eval x / (x - β₀) = (Cb /ₘ (X - C β₀)).eval x + Cb.eval β₀ / (x - β₀) := by
  have h : x - β₀ ≠ 0 := sub_ne_zero.mpr hx
  have e := congrArg (eval x) (modByMonic_add_div Cb (X - C β₀))
  rw [modByMonic_X_sub_C_eq_C_eval] at e
  simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at e
  rw [← e]
  field_simp
  ring

theorem natDegree_divByMonic_X_sub_C (Cb : K[X]) (β₀ : K) :
    (Cb /ₘ (X - C β₀)).natDegree = Cb.natDegree - 1 := by
  rw [natDegree_divByMonic _ (monic_X_sub_C β₀), natDegree_X_sub_C]

/-- The fold of a pole pair by a polynomial combiner is the scalar fold at `Cb(β₀)` plus a
polynomial of degree `deg Cb - 1`. -/
theorem polyFold_pole {x β₀ : K} (hx : x ≠ β₀) (f₁ : K → K) (Cb : K[X]) :
    polyFold (poleWord β₀) f₁ Cb x =
      (Cb /ₘ (X - C β₀)).eval x + scalFold (poleWord β₀) f₁ (Cb.eval β₀) x := by
  have h := combiner_collapse hx Cb
  simp only [polyFold, scalFold, poleWord, ← div_eq_mul_inv]
  rw [h]
  ring

/-- The affine fold of a pole pair is the scalar fold at `γ = α + β β₀` plus the constant `β`. -/
theorem affFold_pole {x β₀ : K} (hx : x ≠ β₀) (f₁ : K → K) (c : K × K) :
    affFold (poleWord β₀) f₁ c x = c.2 + scalFold (poleWord β₀) f₁ (c.1 + c.2 * β₀) x := by
  have h := pole_collapse hx c.1 c.2
  simp only [affFold, scalFold, poleWord, ← div_eq_mul_inv]
  rw [h]
  ring

theorem agree_add_of_forall {D : Finset K} {w w' : K → K} {Q : K[X]}
    (h : ∀ x ∈ D, w' x = Q.eval x + w x) (P : K[X]) : agree D w' (Q + P) = agree D w P := by
  unfold agree
  refine Finset.filter_congr fun x hx => ?_
  rw [h x hx, eval_add]
  exact add_right_inj _

/-- The collapse for a polynomial combiner: if the scalar fold at `Cb(β₀)` is `(d, T)`-close, so
is the fold by `Cb`, at degree `max d (deg Cb - 1)`. -/
theorem polyFold_pole_close {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) (f₁ : K → K) (Cb : K[X])
    {d T : ℕ} (h : Close D (scalFold (poleWord β₀) f₁ (Cb.eval β₀)) d T) :
    Close D (polyFold (poleWord β₀) f₁ Cb) (max d (Cb.natDegree - 1)) T := by
  obtain ⟨P, hP, hT⟩ := h
  refine ⟨Cb /ₘ (X - C β₀) + P, ?_, ?_⟩
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_divByMonic_X_sub_C]
      exact le_max_right _ _
    · exact hP.trans (le_max_left _ _)
  · rw [agree_add_of_forall (w := scalFold (poleWord β₀) f₁ (Cb.eval β₀))]
    · exact hT
    · intro x hx
      exact polyFold_pole (ne_pole hx hβ₀) f₁ Cb

/-- For a combiner of degree at most `d + 1` the collapse is an equivalence at degree `d`: the
fold by `Cb` is close exactly when the scalar fold at `Cb(β₀)` is. -/
theorem polyFold_pole_close_iff {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) (f₁ : K → K) (Cb : K[X])
    {d T : ℕ} (hC : Cb.natDegree ≤ d + 1) :
    Close D (polyFold (poleWord β₀) f₁ Cb) d T ↔
      Close D (scalFold (poleWord β₀) f₁ (Cb.eval β₀)) d T := by
  constructor
  · rintro ⟨P, hP, hT⟩
    refine ⟨-(Cb /ₘ (X - C β₀)) + P, ?_, ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le ?_ hP)
      rw [natDegree_neg, natDegree_divByMonic_X_sub_C]
      omega
    · rw [agree_add_of_forall (w := polyFold (poleWord β₀) f₁ Cb)]
      · exact hT
      · intro x hx
        rw [polyFold_pole (ne_pole hx hβ₀) f₁ Cb, eval_neg]
        ring
  · intro h
    have := polyFold_pole_close hβ₀ f₁ Cb h
    rwa [max_eq_left (by omega)] at this

/-- **The pole collapse of the affine combiner.** For a pole pair `(1 / (x - β₀), f₁)` with
`β₀` outside the domain, the affine fold at `(α, β)` is close exactly when the scalar fold at
`γ = α + β β₀` is: every bad scalar `γ` is a whole line of bad pairs `(α, β)`. -/
theorem affFold_pole_close_iff {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) (f₁ : K → K) (c : K × K)
    (d T : ℕ) :
    Close D (affFold (poleWord β₀) f₁ c) d T ↔
      Close D (scalFold (poleWord β₀) f₁ (c.1 + c.2 * β₀)) d T := by
  constructor
  · rintro ⟨P, hP, hT⟩
    refine ⟨C (-c.2) + P, ?_, ?_⟩
    · rwa [add_comm, natDegree_add_C]
    · rw [agree_add_of_forall (w := affFold (poleWord β₀) f₁ c)]
      · exact hT
      · intro x hx
        rw [affFold_pole (ne_pole hx hβ₀) f₁ c, eval_C]
        ring
  · rintro ⟨P, hP, hT⟩
    refine ⟨C c.2 + P, ?_, ?_⟩
    · rwa [add_comm, natDegree_add_C]
    · rw [agree_add_of_forall (w := scalFold (poleWord β₀) f₁ (c.1 + c.2 * β₀))]
      · exact hT
      · intro x hx
        rw [affFold_pole (ne_pole hx hβ₀) f₁ c, eval_C]

/-- The bad affine challenges of a pole pair are `|K|` times the bad scalar challenges. -/
theorem card_bad_affFold_pole [Fintype K] {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) (f₁ : K → K)
    (d T : ℕ) :
    (univ.filter (fun c : K × K => Close D (affFold (poleWord β₀) f₁ c) d T)).card =
      Fintype.card K *
        (univ.filter (fun γ : K => Close D (scalFold (poleWord β₀) f₁ γ) d T)).card := by
  rw [mul_comm, ← Finset.card_univ (α := K), ← Finset.card_product]
  refine Finset.card_nbij' (fun c => (c.1 + c.2 * β₀, c.2)) (fun p => (p.1 - p.2 * β₀, p.2))
    ?_ ?_ ?_ ?_
  · intro c hc
    have hc' := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, and_true]
    exact (affFold_pole_close_iff hβ₀ f₁ c d T).mp hc'
  · intro p hp
    have hp' := (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hp)).1).2
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [affFold_pole_close_iff hβ₀ f₁ _ d T]
    simpa using hp'
  · intro c _
    simp
  · intro p _
    simp

/-! ### A list gives lines of bad challenges -/

/-- No polynomial of degree at most `d` agrees with `1 / (x - β₀)` on more than `d + 1` points. -/
theorem card_agree_poleWord_le {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) {G : K[X]} {d : ℕ}
    (hG : G.natDegree ≤ d) : (agree D (poleWord β₀) G).card ≤ d + 1 := by
  set p : K[X] := (X - C β₀) * G - 1 with hp
  have hp0 : p ≠ 0 := by
    intro h
    have := congrArg (eval β₀) h
    simp [hp] at this
  have hdeg : p.natDegree ≤ d + 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
    refine natDegree_mul_le.trans ?_
    rw [natDegree_X_sub_C]
    omega
  have hsub : (agree D (poleWord β₀) G).val ⊆ p.roots := by
    intro x hx
    obtain ⟨hxD, hxe⟩ := Finset.mem_filter.mp hx
    have hne : x - β₀ ≠ 0 := sub_ne_zero.mpr (ne_pole hxD hβ₀)
    rw [mem_roots hp0, IsRoot, hp]
    simp only [eval_sub, eval_mul, eval_X, eval_C, eval_one, hxe, poleWord]
    rw [mul_inv_cancel₀ hne, sub_self]
  exact (card_le_degree_of_subset_roots hsub).trans hdeg

/-- The scalar form of `lemmaA`: if `Ci` has degree at most `d + 1` and agrees with the word `w` on
at least `T` points of `D`, the scalar fold of the pole pair `(1 / (x - β₀), w / (x - β₀))` at
`γ = -Ci(β₀)` agrees with `(Ci - Ci(β₀)) / (X - β₀)`, of degree at most `d`, on those points. -/
theorem scalFold_pole_close_of_list {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) (w : K → K)
    {Ci : K[X]} {d T : ℕ} (hdeg : Ci.natDegree ≤ d + 1) (hT : T ≤ (agree D w Ci).card) :
    Close D (scalFold (poleWord β₀) (poleNum w β₀) (-(Ci.eval β₀))) d T := by
  refine ⟨Ci /ₘ (X - C β₀), ?_, hT.trans (Finset.card_le_card ?_)⟩
  · rw [natDegree_divByMonic_X_sub_C]
    omega
  · intro x hx
    obtain ⟨hxD, hxe⟩ := Finset.mem_filter.mp hx
    have hne : x ≠ β₀ := ne_pole hxD hβ₀
    have h := combiner_collapse hne Ci
    rw [agree, Finset.mem_filter]
    refine ⟨hxD, ?_⟩
    simp only [scalFold, poleWord, poleNum, ← div_eq_mul_inv, ← hxe]
    rw [h]
    ring

/-- **A list member gives a line of bad challenges** (Proposition 3.5 of the paper, one member).
If `Ci` has degree at most `d + 1` and agrees with the word `w` on at least `T` points of `D`, then
for every challenge `(α, β)` on the line `α + β β₀ = -Ci(β₀)` the affine fold of the pole pair
`(1 / (x - β₀), w / (x - β₀))` agrees with a polynomial of degree at most `d` on at least `T`
points. -/
theorem lemmaA {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) (w : K → K) {Ci : K[X]} {d T : ℕ}
    (hdeg : Ci.natDegree ≤ d + 1) (hT : T ≤ (agree D w Ci).card) {c : K × K}
    (hc : c.1 + c.2 * β₀ = -(Ci.eval β₀)) :
    Close D (affFold (poleWord β₀) (poleNum w β₀) c) d T := by
  rw [affFold_pole_close_iff hβ₀, hc]
  exact scalFold_pole_close_of_list hβ₀ w hdeg hT

/-- `lemmaA` with its witness: on the agreement set of `Ci`, the fold is
`P = β + (Ci - Ci(β₀)) / (X - β₀)`. -/
theorem lemmaA_witness {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) (w : K → K) (Ci : K[X]) {c : K × K}
    (hc : c.1 + c.2 * β₀ = -(Ci.eval β₀)) :
    agree D w Ci ⊆ agree D (affFold (poleWord β₀) (poleNum w β₀) c) (C c.2 + Ci /ₘ (X - C β₀)) := by
  intro x hx
  obtain ⟨hxD, hxe⟩ := Finset.mem_filter.mp hx
  have hne : x ≠ β₀ := ne_pole hxD hβ₀
  have h := combiner_collapse hne Ci
  rw [agree, Finset.mem_filter]
  refine ⟨hxD, ?_⟩
  rw [affFold_pole hne, hc, eval_add, eval_C]
  simp only [scalFold, poleWord, poleNum, ← div_eq_mul_inv, ← hxe]
  rw [h]
  ring

/-- `lemmaA`, counted: a family `𝒞` of list members with distinct values at the pole gives
`|𝒞|` lines, that is `|𝒞| · |K|` bad challenges. -/
theorem lemmaA_card [Fintype K] {D : Finset K} {β₀ : K} (hβ₀ : β₀ ∉ D) (w : K → K) {d T : ℕ}
    (𝒞 : Finset K[X]) (h𝒞 : ∀ Ci ∈ 𝒞, Ci.natDegree ≤ d + 1 ∧ T ≤ (agree D w Ci).card)
    (hinj : Set.InjOn (fun Ci : K[X] => Ci.eval β₀) (𝒞 : Set K[X])) :
    𝒞.card * Fintype.card K ≤
      (univ.filter (fun c : K × K =>
        Close D (affFold (poleWord β₀) (poleNum w β₀) c) d T)).card := by
  rw [card_bad_affFold_pole hβ₀, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  have hinj' : Set.InjOn (fun Ci : K[X] => -(Ci.eval β₀)) (𝒞 : Set K[X]) :=
    fun P hP Q hQ hPQ => hinj hP hQ (neg_injective hPQ)
  rw [← Finset.card_image_of_injOn hinj']
  refine Finset.card_le_card fun γ hγ => ?_
  obtain ⟨Ci, hCi, rfl⟩ := Finset.mem_image.mp hγ
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, scalFold_pole_close_of_list hβ₀ w (h𝒞 Ci hCi).1 (h𝒞 Ci hCi).2⟩

/-- A pole that separates a finite family: if `m · C(|𝒞|, 2) + |D| < |K|` and the members of `𝒞`
have degree at most `m`, some `β₀` outside `D` gives them pairwise distinct values. -/
theorem exists_pole_injOn [Fintype K] (D : Finset K) (𝒞 : Finset K[X]) {m : ℕ}
    (h𝒞 : ∀ P ∈ 𝒞, P.natDegree ≤ m) (hK : m * 𝒞.card.choose 2 + D.card < Fintype.card K) :
    ∃ β₀ : K, β₀ ∉ D ∧ Set.InjOn (fun P : K[X] => P.eval β₀) (𝒞 : Set K[X]) := by
  set R : Finset K[X] → Finset K := fun s =>
    univ.filter (fun β => ∃ P ∈ s, ∃ Q ∈ s, P ≠ Q ∧ P.eval β = Q.eval β) with hR
  have hRcard : ∀ s ∈ 𝒞.powersetCard 2, (R s).card ≤ m := by
    intro s hs
    obtain ⟨hs𝒞, hs2⟩ := Finset.mem_powersetCard.mp hs
    obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.mp hs2
    have hA : A ∈ 𝒞 := hs𝒞 (by simp)
    have hB : B ∈ 𝒞 := hs𝒞 (by simp)
    have hne : A - B ≠ 0 := sub_ne_zero.mpr hAB
    have hdeg : (A - B).natDegree ≤ m :=
      (natDegree_sub_le _ _).trans (max_le (h𝒞 A hA) (h𝒞 B hB))
    have hsub : (R {A, B}).val ⊆ (A - B).roots := by
      intro β hβ
      obtain ⟨-, P, hP, Q, hQ, hPQ, he⟩ := Finset.mem_filter.mp hβ
      rw [mem_roots hne, IsRoot, eval_sub]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP hQ
      rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
      · exact absurd rfl hPQ
      · exact sub_eq_zero.mpr he
      · exact sub_eq_zero.mpr he.symm
      · exact absurd rfl hPQ
    exact (card_le_degree_of_subset_roots hsub).trans hdeg
  have hcard : (D ∪ (𝒞.powersetCard 2).biUnion R).card < Fintype.card K := by
    refine lt_of_le_of_lt ((Finset.card_union_le _ _).trans ?_) hK
    rw [add_comm]
    refine Nat.add_le_add_right (Finset.card_biUnion_le.trans ?_) _
    refine (Finset.sum_le_card_nsmul _ _ m hRcard).trans ?_
    rw [Finset.card_powersetCard, smul_eq_mul, mul_comm]
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : K, β₀ ∉ D ∪ (𝒞.powersetCard 2).biUnion R := by
    by_contra hcon
    have : D ∪ (𝒞.powersetCard 2).biUnion R = univ :=
      Finset.eq_univ_iff_forall.mpr fun x => by
        by_contra hx
        exact hcon ⟨x, hx⟩
    rw [this, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  rw [Finset.mem_union, not_or] at hβ₀
  refine ⟨β₀, hβ₀.1, ?_⟩
  intro P hP Q hQ hPQ
  by_contra hne
  apply hβ₀.2
  rw [Finset.mem_biUnion]
  refine ⟨{P, Q}, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair hne⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hP
    · rw [Finset.mem_singleton.mp hx]
      exact hQ
  · rw [hR, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, P, by simp, Q, by simp, hne, hPQ⟩

/-- **Lists give lines of bad challenges** (the last statement of Proposition 3.5 of the paper).
Over a finite field, a word `w` on `D` with a list `𝒞` of polynomials of degree at most `d + 1` at
agreement `T`, and
`(d + 1) · C(|𝒞|, 2) + |D| < |K|`: for some pole `β₀` outside `D`, the pole pair
`(1 / (x - β₀), w / (x - β₀))` has at least `|𝒞| · |K|` challenges `(α, β)` at which its affine
fold agrees with a polynomial of degree at most `d` on at least `T` points, although its first
word agrees with no polynomial of degree at most `d` on more than `d + 1` points
(`card_agree_poleWord_le`). -/
theorem list_gives_bad_challenges [Fintype K] (D : Finset K) (w : K → K) {d T : ℕ}
    (𝒞 : Finset K[X]) (h𝒞 : ∀ Ci ∈ 𝒞, Ci.natDegree ≤ d + 1 ∧ T ≤ (agree D w Ci).card)
    (hK : (d + 1) * 𝒞.card.choose 2 + D.card < Fintype.card K) :
    ∃ β₀ : K, β₀ ∉ D ∧
      𝒞.card * Fintype.card K ≤
        (univ.filter (fun c : K × K =>
          Close D (affFold (poleWord β₀) (poleNum w β₀) c) d T)).card := by
  obtain ⟨β₀, hβ₀, hinj⟩ := exists_pole_injOn D 𝒞 (fun P hP => (h𝒞 P hP).1) hK
  exact ⟨β₀, hβ₀, lemmaA_card hβ₀ w 𝒞 h𝒞 hinj⟩

end Constructions
