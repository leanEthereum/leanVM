/-
Proposition 6.2 of the paper, the projection bound: a list-size bound for words with values in
one finite vector space `W` over a field `K` gives one for words with values in every finite
vector space `V` over `K`, with the loss `1/(1 - L/|W|)`.

The code is given by a generator: the word of a message `m : κ → V` is
`enc G m i = ∑ k, G i k • m k` for a matrix `G : ι → κ → K`. For the Reed-Solomon code,
`G x k = x ^ k` and a message is the coefficient vector of a polynomial (`ReedSolomon.lean`).
Lists are lists of messages, as in the paper (lists of polynomials).

The proof follows the paper: a uniformly random `K`-linear map `l : V → W`, applied to the
coordinates of the messages, commutes with the encoding, and two distinct messages collide with
probability at most `1/|W|`.
-/
import Interleave.Basic

open Finset

namespace Interleave

section Collisions

variable {β γ : Type*} [DecidableEq γ]

/-- A map that identifies few ordered pairs has a large image: `2(|S| - |f(S)|)` is at most the
number of ordered pairs of distinct elements of `S` with the same image. -/
theorem two_mul_card_le_image_add_collisions (f : β → γ) (S : Finset β) :
    2 * S.card ≤ 2 * (S.image f).card + (S.offDiag.filter (fun p => f p.1 = f p.2)).card := by
  have h1 : S.card = ∑ y ∈ S.image f, (S.filter (fun b => f b = y)).card :=
    card_eq_sum_card_image f S
  have h2 : (S.offDiag.filter (fun p => f p.1 = f p.2)).card =
      ∑ y ∈ S.image f, ((S.filter (fun b => f b = y)).offDiag).card := by
    rw [card_eq_sum_card_fiberwise (f := fun p : β × β => f p.1) (t := S.image f)]
    · refine sum_congr rfl fun y _ => ?_
      congr 1
      ext ⟨p, p'⟩
      simp only [mem_filter, mem_offDiag]
      constructor
      · rintro ⟨⟨⟨hp, hp', hne⟩, heq⟩, hy⟩
        exact ⟨⟨hp, hy⟩, ⟨hp', heq.symm.trans hy⟩, hne⟩
      · rintro ⟨⟨hp, hy⟩, ⟨hp', hy'⟩, hne⟩
        exact ⟨⟨⟨hp, hp', hne⟩, hy.trans hy'.symm⟩, hy⟩
    · intro p hp
      exact mem_coe.mpr (mem_image_of_mem f (mem_offDiag.mp (mem_filter.mp (mem_coe.mp hp)).1).1)
  have h3 : (S.image f).card = ∑ _y ∈ S.image f, 1 := by
    rw [sum_const, smul_eq_mul, mul_one]
  rw [h2, h1, h3, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun y hy => ?_
  have hpos : 0 < (S.filter (fun b => f b = y)).card := by
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
    exact card_pos.mpr ⟨b, mem_filter.mpr ⟨hb, rfl⟩⟩
  rw [offDiag_card]
  generalize (S.filter (fun b => f b = y)).card = n at hpos ⊢
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e : (k + 1) * (k + 1) - (k + 1) = k * k + k := by
    have e' : (k + 1) * (k + 1) = k * k + k + (k + 1) := by ring
    omega
  have hk : k ≤ k * k := Nat.le_mul_self k
  rw [e]
  omega

end Collisions

section LinearMaps

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- A nonzero vector is killed by at most one linear map in `|W|`. -/
theorem card_vanish_mul_le [Fintype W] [Fintype (V →ₗ[K] W)] [DecidableEq W] {v : V}
    (hv : v ≠ 0) :
    (univ.filter (fun l : V →ₗ[K] W => l v = 0)).card * Fintype.card W ≤
      Fintype.card (V →ₗ[K] W) := by
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ v ≠ 0 := by
    by_contra h
    exact hv ((Module.forall_dual_apply_eq_zero_iff K v).mp fun φ =>
      by_contra fun hφ => h ⟨φ, hφ⟩)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K V, ψ v = 1 :=
    ⟨(φ v)⁻¹ • φ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]⟩
  rw [← card_univ (α := W), ← card_product, ← card_univ (α := V →ₗ[K] W)]
  refine card_le_card_of_injOn (fun p => p.1 + ψ.smulRight p.2)
    (fun _ _ => mem_coe.mpr (mem_univ _)) ?_
  rintro ⟨l, w⟩ hp ⟨l', w'⟩ hp' h
  have hl : l v = 0 := (mem_filter.mp (mem_product.mp (mem_coe.mp hp)).1).2
  have hl' : l' v = 0 := (mem_filter.mp (mem_product.mp (mem_coe.mp hp')).1).2
  have hw : w = w' := by
    have h' := LinearMap.congr_fun h v
    simpa only [LinearMap.add_apply, LinearMap.smulRight_apply, hl, hl', hψ, one_smul, zero_add]
      using h'
  subst hw
  have hll : l = l' := add_right_cancel h
  rw [hll]

/-- Some linear map `V → W` identifies at most `|S|(|S| - 1)/|W|` ordered pairs of distinct
elements of a finite set `S` of `V`-valued functions. -/
theorem exists_linearMap_collisions [Finite V] [Fintype W] {X : Type*} [DecidableEq (X → V)]
    [DecidableEq (X → W)] (S : Finset (X → V)) :
    ∃ l : V →ₗ[K] W,
      (S.offDiag.filter (fun p => (fun x => l (p.1 x)) = (fun x => l (p.2 x)))).card *
        Fintype.card W ≤ S.card * (S.card - 1) := by
  classical
  have : Finite (V →ₗ[K] W) := Finite.of_injective (fun l => (l : V → W)) DFunLike.coe_injective
  have := Fintype.ofFinite (V →ₗ[K] W)
  have key : ∑ l : V →ₗ[K] W,
      (S.offDiag.filter (fun p => (fun x => l (p.1 x)) = (fun x => l (p.2 x)))).card *
        Fintype.card W ≤ ∑ _l : V →ₗ[K] W, S.card * (S.card - 1) := by
    have hswap : ∑ l : V →ₗ[K] W,
        (S.offDiag.filter (fun p => (fun x => l (p.1 x)) = (fun x => l (p.2 x)))).card =
        ∑ p ∈ S.offDiag, (univ.filter (fun l : V →ₗ[K] W =>
          (fun x => l (p.1 x)) = (fun x => l (p.2 x)))).card := by
      simp only [card_filter]
      exact sum_comm
    rw [← sum_mul, hswap, sum_mul, sum_const, card_univ, smul_eq_mul]
    calc ∑ p ∈ S.offDiag, (univ.filter (fun l : V →ₗ[K] W =>
          (fun x => l (p.1 x)) = (fun x => l (p.2 x)))).card * Fintype.card W
        ≤ ∑ _p ∈ S.offDiag, Fintype.card (V →ₗ[K] W) := by
          refine sum_le_sum fun p hp => ?_
          obtain ⟨-, -, hne⟩ := mem_offDiag.mp hp
          obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
          refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_))
            (card_vanish_mul_le (sub_ne_zero.mpr hx))
          intro l hl
          have hlx := congrFun (mem_filter.mp hl).2 x
          refine mem_filter.mpr ⟨mem_univ _, ?_⟩
          rw [map_sub, sub_eq_zero]
          exact hlx
      _ = Fintype.card (V →ₗ[K] W) * (S.card * (S.card - 1)) := by
          rw [sum_const, smul_eq_mul, offDiag_card, Nat.mul_sub_one, mul_comm]
  obtain ⟨l, -, hl⟩ := exists_le_of_sum_le univ_nonempty key
  exact ⟨l, hl⟩

/-- Some linear map `V → W`, applied to the values of the elements of `S`, has an image `I` with
`2|W|·|S| ≤ 2|W|·|I| + |S|(|S| - 1)`. -/
theorem exists_linearMap_image [Finite V] [Fintype W] {X : Type*} (S : Finset (X → V)) :
    ∃ l : V →ₗ[K] W, ∃ I : Finset (X → W), (∀ c ∈ I, ∃ m ∈ S, c = fun x => l (m x)) ∧
      2 * Fintype.card W * S.card ≤ 2 * Fintype.card W * I.card + S.card * (S.card - 1) := by
  classical
  obtain ⟨l, hl⟩ := exists_linearMap_collisions (K := K) (W := W) S
  refine ⟨l, S.image (fun m x => l (m x)), fun c hc => ?_, ?_⟩
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp hc
    exact ⟨m, hm, rfl⟩
  · have h := two_mul_card_le_image_add_collisions (fun (m : X → V) x => l (m x)) S
    have h' := Nat.mul_le_mul_left (Fintype.card W) h
    calc 2 * Fintype.card W * S.card = Fintype.card W * (2 * S.card) := by ring
      _ ≤ Fintype.card W * (2 * (S.image (fun m x => l (m x))).card +
            (S.offDiag.filter (fun p => (fun x => l (p.1 x)) = (fun x => l (p.2 x)))).card) := h'
      _ = 2 * Fintype.card W * (S.image (fun m x => l (m x))).card +
            (S.offDiag.filter (fun p => (fun x => l (p.1 x)) = (fun x => l (p.2 x)))).card *
              Fintype.card W := by ring
      _ ≤ _ := Nat.add_le_add_left hl _

end LinearMaps

/-- The arithmetic of Proposition 6.2 of the paper: if every subset `S'` of `S` satisfies
`2q|S'| ≤ 2qL + |S'|(|S'| - 1)` and `2L ≤ q`, then `|S| ≤ 2L - 1` and `|S|(q - L) ≤ Lq`. -/
theorem descent_arith {β : Type*} (S : Finset β) {q L : ℕ} (hq : 0 < q) (h2 : 2 * L ≤ q)
    (h : ∀ S' ⊆ S, 2 * q * S'.card ≤ 2 * q * L + S'.card * (S'.card - 1)) :
    S.card ≤ 2 * L - 1 ∧ S.card * (q - L) ≤ L * q := by
  have hlt : S.card ≤ 2 * L - 1 := by
    by_contra hcon
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · obtain ⟨S', hS', hcard⟩ := exists_subset_card_eq (s := S) (n := 1) (by omega)
      have := h S' hS'
      rw [hcard] at this
      omega
    · obtain ⟨S', hS', hcard⟩ := exists_subset_card_eq (s := S) (n := 2 * L) (by omega)
      have h' := h S' hS'
      rw [hcard] at h'
      obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
      have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [e] at h'
      have h3 := Nat.mul_le_mul_right (k + 1) h2
      nlinarith
  refine ⟨hlt, ?_⟩
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have h0 : S.card = 0 := by omega
    rw [h0]
    omega
  · have h' := h S (Subset.refl S)
    obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
    have h4 : S.card * (S.card - 1) ≤ S.card * (2 * k) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, Nat.sub_le_iff_le_add]
    nlinarith

section Generator

variable {K : Type*} [Field K] {ι κ : Type*} [Fintype κ]

/-- The word of the message `m` under the generator `G`: `enc G m i = ∑ k, G i k • m k`. -/
def enc {V : Type*} [AddCommGroup V] [Module K V] (G : ι → κ → K) (m : κ → V) (i : ι) : V :=
  ∑ k, G i k • m k

/-- A linear map on the values commutes with the encoding. -/
theorem map_enc {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (l : V →ₗ[K] W) (G : ι → κ → K) (m : κ → V) (i : ι) :
    l (enc G m i) = enc G (fun k => l (m k)) i := by
  simp only [enc, map_sum, map_smul]

/-- Every `V`-valued word has at most `L` messages whose words agree with it on at least `a`
coordinates of `D`. -/
def GenListBound (G : ι → κ → K) (D : Finset ι) (V : Type*) [AddCommGroup V] [Module K V]
    (a L : ℕ) : Prop :=
  ∀ (w : ι → V) (S : Finset (κ → V)), (∀ m ∈ S, a ≤ (agr D w (enc G m)).card) → S.card ≤ L

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The inequality behind Proposition 6.2 of the paper: a list `S` of a `V`-valued word, projected
by a good linear map `V → W`, gives a list of a `W`-valued word with at least
`|S| - |S|(|S|-1)/(2|W|)` members. -/
theorem descent_ineq [Finite V] [Fintype W] {G : ι → κ → K} {D : Finset ι} {a L : ℕ}
    (hL : GenListBound G D W a L) (w : ι → V) (S : Finset (κ → V))
    (hS : ∀ m ∈ S, a ≤ (agr D w (enc G m)).card) :
    2 * Fintype.card W * S.card ≤ 2 * Fintype.card W * L + S.card * (S.card - 1) := by
  obtain ⟨l, I, hI, hle⟩ := exists_linearMap_image (K := K) (W := W) S
  have hIL : I.card ≤ L := by
    refine hL (fun i => l (w i)) I fun c hc => ?_
    obtain ⟨m, hm, rfl⟩ := hI c hc
    refine (hS m hm).trans (card_le_card fun i hi => ?_)
    refine mem_agr.mpr ⟨(mem_agr.mp hi).1, ?_⟩
    rw [← map_enc, (mem_agr.mp hi).2]
  exact hle.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hIL) _)

/-- **Proposition 6.2 of the paper**, for a code given by a generator. If every `W`-valued word has
at most `L` list members and `2L ≤ |W|`, then every list `S` of a word with values in any finite
`K`-vector space `V` has `|S| ≤ 2L - 1` and `|S|·(|W| - L) ≤ L·|W|`, that is
`|S| ≤ L/(1 - L/|W|)`. -/
theorem descent [Finite V] [Fintype W] {G : ι → κ → K} {D : Finset ι} {a L : ℕ}
    (hL : GenListBound G D W a L) (h2 : 2 * L ≤ Fintype.card W) (w : ι → V)
    (S : Finset (κ → V)) (hS : ∀ m ∈ S, a ≤ (agr D w (enc G m)).card) :
    S.card ≤ 2 * L - 1 ∧ S.card * (Fintype.card W - L) ≤ L * Fintype.card W :=
  descent_arith S (Fintype.card_pos_iff.mpr ⟨0⟩) h2 fun S' hS' =>
    descent_ineq hL w S' fun m hm => hS m (hS' hm)

/-- The bound of Proposition 6.2 of the paper as a quotient: `|S| ≤ L/(1 - L/|W|)`. -/
theorem descent_div [Finite V] [Fintype W] {G : ι → κ → K} {D : Finset ι} {a L : ℕ}
    (hL : GenListBound G D W a L) (h2 : 2 * L ≤ Fintype.card W) (w : ι → V)
    (S : Finset (κ → V)) (hS : ∀ m ∈ S, a ≤ (agr D w (enc G m)).card) :
    (S.card : ℚ) ≤ (L : ℚ) / (1 - (L : ℚ) / (Fintype.card W : ℚ)) := by
  obtain ⟨h1, h⟩ := descent hL h2 w S hS
  have hq : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨0⟩
  rcases Nat.eq_zero_or_pos L with rfl | hLpos
  · have h0 : S.card = 0 := by omega
    simp [h0]
  · have hq' : (0 : ℚ) < (Fintype.card W : ℚ) := by exact_mod_cast hq
    have hLq : L ≤ Fintype.card W := by omega
    have hcast : (S.card : ℚ) * ((Fintype.card W : ℚ) - L) ≤ L * Fintype.card W := by
      have := (Nat.cast_le (α := ℚ)).mpr h
      rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hLq] at this
    have hpos : (0 : ℚ) < 1 - (L : ℚ) / (Fintype.card W : ℚ) := by
      rw [sub_pos, div_lt_one hq']
      exact_mod_cast (by omega : L < Fintype.card W)
    rw [le_div_iff₀ hpos]
    have e : (S.card : ℚ) * (1 - (L : ℚ) / (Fintype.card W : ℚ)) =
        (S.card : ℚ) * ((Fintype.card W : ℚ) - L) / (Fintype.card W : ℚ) := by
      field_simp
    rw [e, div_le_iff₀ hq']
    exact hcast

end Generator

end Interleave
