/-
The induction of the period descent, without polynomials: note 39 Lemma 1.2 and Theorem 1.3, and
the counting of Theorem R of note 46.

* `greedy_cover`: a list in which every sublist of more than `f` members contains a bad triple has
  a sublist `S₀` of at most `f` members such that every other member is a bad third of a pair of
  `S₀` (take a largest sublist without bad triple).
* `one_step`: if moreover every pair has at most `W` bad thirds, the list has at most
  `f + C(f, 2) W` members.
* `supersaturation`: note 39 Lemma 1.2 as stated: a list of `L > f ≥ 2` members has a pair with at
  least `(L - 2) / C(f + 1, 3)` bad thirds.
* `bnd`, `bnd_le`: the recursion `a_j ≤ f + G 2^(N - j) a_{j+1}` of note 39 Theorem 1.3, unrolled
  from the level `j₀`: `a_0 + 1 ≤ G^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (a_{j₀} + 1)`, for
  `f + 1 ≤ 4 G` and `j₀ ≤ N - 1`.
* `abstract_descent`: **Theorem R in abstract form.** A family of problems with levels; the members
  of a problem periodic for a pair and a direction inject into the members of a problem of the next
  level; at most `2^(N - j)` directions at level `j`; every list of more than `f` members of a
  problem of level `< j₀` contains a triple that is periodic for some direction (hypothesis PL);
  every list of level `j₀` has at most `B` members. Then every list of level `0` has at most
  `G^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (B + 1) - 1` members, for every `G ≥ C(f, 2)` with
  `f + 1 ≤ 4 G`.
* `abstract_descent_notes`: the same with `G = C(f + 1, 3)`, the constant of the notes, for
  `f ≥ 2`. `abstract_descent_sharp`: with `G = C(f, 2)`.
* `bndDP`, `bndDP_le`, `abstract_descent_DP`: note 37 Corollary 3.4 and Theorem 3.5 in abstract
  form: under DP`(B)` (every list has a pair for which all but `B` members are periodic), every
  list of level `0` has at most `2^(N j₀ - j₀ (j₀ - 1) / 2) (j₀ (B + 2) + B₀)` members.
-/
import Mathlib

open Finset
open scoped Classical

namespace PeriodDescent

/-! ### One level -/

section OneStep

variable {C : Type*}

/-- A largest sublist without bad triple has at most `f` members, and every other member is a bad
third of one of its pairs. -/
theorem greedy_cover (S : Finset C) (bad : C → C → C → Prop) (f : ℕ)
    (hsym1 : ∀ x y z, bad x y z → bad x z y) (hsym2 : ∀ x y z, bad x y z → bad y x z)
    (hPL : ∀ S' ⊆ S, f < S'.card →
      ∃ x ∈ S', ∃ y ∈ S', ∃ z ∈ S', x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ bad x y z) :
    ∃ S0 ⊆ S, S0.card ≤ f ∧ ∀ c ∈ S, c ∉ S0 → ∃ x ∈ S0, ∃ y ∈ S0, x ≠ y ∧ bad x y c := by
  have hne : (S.powerset.filter (fun S' : Finset C => ∀ x ∈ S', ∀ y ∈ S', ∀ z ∈ S',
      x ≠ y → x ≠ z → y ≠ z → ¬ bad x y z)).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset S, ?_⟩⟩
    intro x hx
    exact absurd hx (Finset.notMem_empty x)
  obtain ⟨S0, hS0, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  have hS0S : S0 ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hS0).1
  have hprim := (Finset.mem_filter.mp hS0).2
  refine ⟨S0, hS0S, ?_, ?_⟩
  · by_contra hcon
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hb⟩ := hPL S0 hS0S (not_le.mp hcon)
    exact hprim x hx y hy z hz hxy hxz hyz hb
  · intro c hc hcS0
    by_contra hno
    have hno' : ∀ x ∈ S0, ∀ y ∈ S0, x ≠ y → ¬ bad x y c := by
      intro x hx y hy hxy hb
      exact hno ⟨x, hx, y, hy, hxy, hb⟩
    have hins : insert c S0 ∈ S.powerset.filter (fun S' : Finset C => ∀ x ∈ S', ∀ y ∈ S',
        ∀ z ∈ S', x ≠ y → x ≠ z → y ≠ z → ¬ bad x y z) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hc hS0S), ?_⟩
      intro x hx y hy z hz hxy hxz hyz hb
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · have hx' : x ∈ S0 := (Finset.mem_insert.mp hx).resolve_left hxz
        have hy' : y ∈ S0 := (Finset.mem_insert.mp hy).resolve_left hyz
        exact hno' x hx' y hy' hxy hb
      · rcases Finset.mem_insert.mp hy with rfl | hy'
        · have hx' : x ∈ S0 := (Finset.mem_insert.mp hx).resolve_left hxy
          exact hno' x hx' z hz' hxz (hsym1 _ _ _ hb)
        · rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hno' y hy' z hz' hyz (hsym1 _ _ _ (hsym2 _ _ _ hb))
          · exact hprim x hx' y hy' z hz' hxy hxz hyz hb
    have h1 := hmax _ hins
    rw [Finset.card_insert_of_notMem hcS0] at h1
    omega

/-- The cover of `greedy_cover`, counted: `W` bounds the sets of bad thirds of the pairs of `S₀`. -/
private theorem cover_count (S S0 : Finset C) (bad : C → C → C → Prop) (W : ℕ)
    (hsym2 : ∀ x y z, bad x y z → bad y x z)
    (hcov : ∀ c ∈ S, c ∉ S0 → ∃ x ∈ S0, ∃ y ∈ S0, x ≠ y ∧ bad x y c)
    (hW : ∀ x ∈ S0, ∀ y ∈ S0, x ≠ y → ∀ T ⊆ S, (∀ c ∈ T, bad x y c) → T.card ≤ W) :
    S.card ≤ S0.card + S0.card.choose 2 * W := by
  have hsub : S ⊆ S0 ∪ (S0.powersetCard 2).biUnion
      (fun p => S.filter (fun c => ∃ x ∈ p, ∃ y ∈ p, x ≠ y ∧ bad x y c)) := by
    intro c hc
    by_cases hc0 : c ∈ S0
    · exact Finset.mem_union_left _ hc0
    · obtain ⟨x, hx, y, hy, hxy, hb⟩ := hcov c hc hc0
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨{x, y}, ?_, ?_⟩)
      · refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hxy⟩
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht'
        · exact hx
        · rw [Finset.mem_singleton.mp ht']
          exact hy
      · exact Finset.mem_filter.mpr ⟨hc, x, by simp, y, by simp, hxy, hb⟩
  have hT : ∀ p ∈ S0.powersetCard 2,
      (S.filter (fun c => ∃ x ∈ p, ∃ y ∈ p, x ≠ y ∧ bad x y c)).card ≤ W := by
    intro p hp
    obtain ⟨hpS0, hp2⟩ := Finset.mem_powersetCard.mp hp
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hp2
    have hx : x ∈ S0 := hpS0 (by simp)
    have hy : y ∈ S0 := hpS0 (by simp)
    refine hW x hx y hy hxy _ (Finset.filter_subset _ _) ?_
    intro c hc
    obtain ⟨_, x', hx', y', hy', hxy', hb⟩ := Finset.mem_filter.mp hc
    rcases Finset.mem_insert.mp hx' with rfl | hx''
    · rcases Finset.mem_insert.mp hy' with rfl | hy''
      · exact absurd rfl hxy'
      · rw [Finset.mem_singleton.mp hy''] at hb
        exact hb
    · rw [Finset.mem_singleton.mp hx''] at hb hxy'
      rcases Finset.mem_insert.mp hy' with rfl | hy''
      · exact hsym2 _ _ _ hb
      · exact absurd (Finset.mem_singleton.mp hy'').symm hxy'
  calc S.card ≤ (S0 ∪ (S0.powersetCard 2).biUnion
        (fun p => S.filter (fun c => ∃ x ∈ p, ∃ y ∈ p, x ≠ y ∧ bad x y c))).card :=
        Finset.card_le_card hsub
    _ ≤ S0.card + ((S0.powersetCard 2).biUnion
        (fun p => S.filter (fun c => ∃ x ∈ p, ∃ y ∈ p, x ≠ y ∧ bad x y c))).card :=
        Finset.card_union_le _ _
    _ ≤ S0.card + ∑ p ∈ S0.powersetCard 2,
        (S.filter (fun c => ∃ x ∈ p, ∃ y ∈ p, x ≠ y ∧ bad x y c)).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ S0.card + (S0.powersetCard 2).card • W :=
        Nat.add_le_add_left (Finset.sum_le_card_nsmul _ _ _ hT) _
    _ = S0.card + S0.card.choose 2 * W := by rw [Finset.card_powersetCard, smul_eq_mul]

/-- **One level of the descent.** If every sublist of more than `f` members contains a bad triple
and every set of bad thirds of a pair has at most `W` members, the list has at most
`f + C(f, 2) W` members. -/
theorem one_step (S : Finset C) (bad : C → C → C → Prop) (f W : ℕ)
    (hsym1 : ∀ x y z, bad x y z → bad x z y) (hsym2 : ∀ x y z, bad x y z → bad y x z)
    (hPL : ∀ S' ⊆ S, f < S'.card →
      ∃ x ∈ S', ∃ y ∈ S', ∃ z ∈ S', x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ bad x y z)
    (hW : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ T ⊆ S, (∀ c ∈ T, bad x y c) → T.card ≤ W) :
    S.card ≤ f + f.choose 2 * W := by
  obtain ⟨S0, hS0S, hS0f, hcov⟩ := greedy_cover S bad f hsym1 hsym2 hPL
  have h1 := cover_count S S0 bad W hsym2 hcov
    (fun x hx y hy hxy => hW x (hS0S hx) y (hS0S hy) hxy)
  calc S.card ≤ S0.card + S0.card.choose 2 * W := h1
    _ ≤ f + f.choose 2 * W :=
      Nat.add_le_add hS0f (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hS0f))

private theorem sub_two_le_choose_three : ∀ s : ℕ, 2 ≤ s → s - 2 ≤ s.choose 3 := by
  intro s
  induction s with
  | zero => intro h; omega
  | succ s ih =>
    intro hs
    rcases Nat.lt_or_ge s 2 with h | h
    · have : s = 1 := by omega
      subst this
      simp
    · have h1 : (s + 1).choose 3 = s.choose 2 + s.choose 3 := Nat.choose_succ_succ' s 2
      have h2 : 0 < s.choose 2 := Nat.choose_pos h
      have h3 := ih h
      omega

/-- **Note 39 Lemma 1.2 (supersaturation), as stated.** Let a list have `L` members and no
sublist of `f + 1` members without bad triple, `L > f ≥ 2`. Then there is a pair `(x, y)` and a set
`T` of other members, all of them bad thirds of the pair, with `L - 2 ≤ C(f + 1, 3) |T|`. (The
proof is not the count of bad triples of the note: it goes through `greedy_cover`, which gives
the constant `C(f, 2)` in `one_step`.) -/
theorem supersaturation (S : Finset C) (bad : C → C → C → Prop) (f : ℕ) (hf : 2 ≤ f)
    (hL : f < S.card)
    (hsym1 : ∀ x y z, bad x y z → bad x z y) (hsym2 : ∀ x y z, bad x y z → bad y x z)
    (hPL : ∀ S' ⊆ S, f < S'.card →
      ∃ x ∈ S', ∃ y ∈ S', ∃ z ∈ S', x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ bad x y z) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ∃ T ⊆ S, (∀ c ∈ T, c ≠ x ∧ c ≠ y ∧ bad x y c) ∧
      S.card - 2 ≤ (f + 1).choose 3 * T.card := by
  obtain ⟨S0, hS0S, hS0f, hcov⟩ := greedy_cover S bad f hsym1 hsym2 hPL
  -- `S₀` has two members at least
  have hs2 : 2 ≤ S0.card := by
    by_contra hlt
    have h0 : S0.card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h1 := cover_count S S0 bad 0 hsym2 hcov (by
      intro x hx y hy hxy
      exfalso
      have h2 : ({x, y} : Finset C).card ≤ S0.card := Finset.card_le_card (by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht'
        · exact hx
        · rw [Finset.mem_singleton.mp ht']
          exact hy)
      rw [Finset.card_pair hxy] at h2
      omega)
    omega
  -- a pair of `S₀` with the largest number of bad thirds
  have hne : (S0.offDiag).Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S0.card)
    exact ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S0.offDiag
    (fun p : C × C => (S.filter (fun c => c ≠ p.1 ∧ c ≠ p.2 ∧ bad p.1 p.2 c)).card) hne
  obtain ⟨hp1, hp2, hp12⟩ := Finset.mem_offDiag.mp hp
  refine ⟨p.1, hS0S hp1, p.2, hS0S hp2, hp12,
    S.filter (fun c => c ≠ p.1 ∧ c ≠ p.2 ∧ bad p.1 p.2 c), Finset.filter_subset _ _,
    fun c hc => (Finset.mem_filter.mp hc).2, ?_⟩
  have hW : ∀ x ∈ S0, ∀ y ∈ S0, x ≠ y → ∀ T ⊆ S, (∀ c ∈ T, c ≠ x ∧ c ≠ y ∧ bad x y c) →
      T.card ≤ (S.filter (fun c => c ≠ p.1 ∧ c ≠ p.2 ∧ bad p.1 p.2 c)).card := by
    intro x hx y hy hxy T hTS hT
    refine le_trans (Finset.card_le_card ?_) (hmax (x, y) (Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩))
    intro c hc
    exact Finset.mem_filter.mpr ⟨hTS hc, hT c hc⟩
  have hcov' : ∀ c ∈ S, c ∉ S0 → ∃ x ∈ S0, ∃ y ∈ S0, x ≠ y ∧ (c ≠ x ∧ c ≠ y ∧ bad x y c) := by
    intro c hc hc0
    obtain ⟨x, hx, y, hy, hxy, hb⟩ := hcov c hc hc0
    exact ⟨x, hx, y, hy, hxy, fun h => hc0 (h ▸ hx), fun h => hc0 (h ▸ hy), hb⟩
  have h1 := cover_count S S0 (fun x y c => c ≠ x ∧ c ≠ y ∧ bad x y c) _
    (fun x y z h => ⟨h.2.1, h.1, hsym2 _ _ _ h.2.2⟩) hcov' hW
  generalize (S.filter (fun c => c ≠ p.1 ∧ c ≠ p.2 ∧ bad p.1 p.2 c)).card = W at h1 ⊢
  have hW1 : 1 ≤ W := by
    by_contra hW0
    have hW0' : W = 0 := by omega
    rw [hW0', mul_zero, add_zero] at h1
    omega
  -- `L - 2 ≤ (s - 2) + C(s, 2) W ≤ (C(s, 3) + C(s, 2)) W = C(s + 1, 3) W ≤ C(f + 1, 3) W`
  have h5 : S0.card - 2 ≤ S0.card.choose 3 * W :=
    (sub_two_le_choose_three S0.card hs2).trans (Nat.le_mul_of_pos_right _ hW1)
  have h6 : (S0.card + 1).choose 3 = S0.card.choose 2 + S0.card.choose 3 :=
    Nat.choose_succ_succ' S0.card 2
  have h7 : (S0.card + 1).choose 3 ≤ (f + 1).choose 3 :=
    Nat.choose_le_choose 3 (by omega)
  have h8 : (S0.card + 1).choose 3 * W ≤ (f + 1).choose 3 * W := Nat.mul_le_mul_right _ h7
  rw [h6, add_mul] at h8
  omega

end OneStep

/-! ### The recursion -/

/-- The bound of the recursion, counted from the level `j₀`: `bnd 0 = B` bounds the lists of level
`j₀`, and `bnd (i + 1) = f + G 2^(N - j) bnd i` with `j = j₀ - (i + 1)` those of level `j`. -/
def bnd (N j0 f G B : ℕ) : ℕ → ℕ
  | 0 => B
  | i + 1 => f + G * 2 ^ (N - (j0 - (i + 1))) * bnd N j0 f G B i

/-- The recursion unrolled over `i` levels. -/
theorem bnd_le (N j0 f G B : ℕ) (hfG : f + 1 ≤ 4 * G) (hj0 : j0 + 1 ≤ N) :
    ∀ i, i ≤ j0 →
      bnd N j0 f G B i + 1 ≤ G ^ i * 2 ^ (i * (N - j0) + i * (i + 1) / 2) * (B + 1) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [bnd]
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have hexp : N - (j0 - (i + 1)) = (N - j0) + (i + 1) := by omega
    have he2 : (i + 1) * (N - j0) + (i + 1) * (i + 1 + 1) / 2
        = ((N - j0) + (i + 1)) + (i * (N - j0) + i * (i + 1) / 2) := by
      have h1 : (i + 1) * (i + 1 + 1) = i * (i + 1) + 2 * (i + 1) := by ring
      rw [h1, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      ring
    have hpow4 : 4 ≤ 2 ^ ((N - j0) + (i + 1)) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ ((N - j0) + (i + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc : f + 1 ≤ G * 2 ^ ((N - j0) + (i + 1)) :=
      hfG.trans (by rw [mul_comm 4 G]; exact Nat.mul_le_mul_left G hpow4)
    show f + G * 2 ^ (N - (j0 - (i + 1))) * bnd N j0 f G B i + 1 ≤ _
    rw [hexp, he2]
    calc f + G * 2 ^ ((N - j0) + (i + 1)) * bnd N j0 f G B i + 1
        = G * 2 ^ ((N - j0) + (i + 1)) * bnd N j0 f G B i + (f + 1) := by ring
      _ ≤ G * 2 ^ ((N - j0) + (i + 1)) * bnd N j0 f G B i + G * 2 ^ ((N - j0) + (i + 1)) :=
          Nat.add_le_add_left hc _
      _ = G * 2 ^ ((N - j0) + (i + 1)) * (bnd N j0 f G B i + 1) := by ring
      _ ≤ G * 2 ^ ((N - j0) + (i + 1))
            * (G ^ i * 2 ^ (i * (N - j0) + i * (i + 1) / 2) * (B + 1)) :=
          Nat.mul_le_mul_left _ ih'
      _ = G ^ (i + 1) * 2 ^ ((N - j0) + (i + 1) + (i * (N - j0) + i * (i + 1) / 2)) * (B + 1) := by
          rw [pow_succ, pow_add]
          ring

/-- The exponent of two: `∑_{j < j₀} (N - j) = N j₀ - j₀ (j₀ - 1) / 2`. -/
theorem expo_eq (N j0 : ℕ) (h : j0 ≤ N) :
    j0 * (N - j0) + j0 * (j0 + 1) / 2 = N * j0 - j0 * (j0 - 1) / 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, N = j0 + d := ⟨N - j0, by omega⟩
  rw [Nat.add_sub_cancel_left]
  rcases Nat.eq_zero_or_pos j0 with rfl | hpos
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, j0 = m + 1 := ⟨j0 - 1, by omega⟩
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  have h1 : (m + 1) * (m + 1 + 1) = 2 * (t + (m + 1)) := by nlinarith
  have h2 : (m + 1) * (m + 1 - 1) = 2 * t := by
    rw [Nat.add_sub_cancel]
    nlinarith
  have h3 : (m + 1 + d) * (m + 1) = (m + 1) * d + (2 * t + (m + 1)) := by nlinarith
  rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), h3]
  omega

/-- The closed form of the recursion: `a_0 + 1 ≤ G^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (a_{j₀} + 1)`. -/
theorem bnd_closed (N j0 f G B : ℕ) (hfG : f + 1 ≤ 4 * G) (hj0 : j0 + 1 ≤ N) :
    bnd N j0 f G B j0 + 1 ≤ G ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2) * (B + 1) := by
  have h := bnd_le N j0 f G B hfG hj0 j0 le_rfl
  rwa [expo_eq N j0 (by omega)] at h

/-! ### Theorem R, abstract form -/

/-- **Theorem R of note 46 (note 39 Theorem 1.3), abstract form.**

Problems `p` have a level; `mem p c` says that `c` is a member of `p`; `dirs p` are the directions
(the nonzero points of the quotient), at most `2^(N - j)` at level `j`; `per p a c₀ c₁ c` says that
the triple function of `(c₀, c₁, c)` has the period `a`, a property of the unordered triple
(`hsym1`, `hsym2`).

* `hdesc` (the descent step): for a problem of level `j < j₀`, two distinct members and a
  direction, the members periodic for them inject into the members of a problem of level `j + 1`.
* `hPL` (the hypothesis PL`(f, j₀)`): at every level `j < j₀`, every list of more than `f` members
  contains three distinct members that are periodic for some direction.
* `hbase`: every list of level `j₀` has at most `B` members.

Then every list of level `0` has at most `G^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (B + 1) - 1` members,
for every `G` with `C(f, 2) ≤ G` and `f + 1 ≤ 4 G`. -/
theorem abstract_descent {Pb C A : Type*} (level : Pb → ℕ) (mem : Pb → C → Prop)
    (dirs : Pb → Finset A) (per : Pb → A → C → C → C → Prop) (N j0 f G B : ℕ)
    (hGf : f.choose 2 ≤ G) (hfG : f + 1 ≤ 4 * G) (hj0 : j0 + 1 ≤ N)
    (hdirs : ∀ p, level p < j0 → (dirs p).card ≤ 2 ^ (N - level p))
    (hsym1 : ∀ p a c0 c1 c, per p a c0 c1 c → per p a c0 c c1)
    (hsym2 : ∀ p a c0 c1 c, per p a c0 c1 c → per p a c1 c0 c)
    (hdesc : ∀ p, level p < j0 → ∀ c0 c1, mem p c0 → mem p c1 → c0 ≠ c1 → ∀ a ∈ dirs p,
      ∃ p', level p' = level p + 1 ∧ ∃ φ : C → C,
        (∀ c, mem p c → per p a c0 c1 c → mem p' (φ c)) ∧
        (∀ c c', mem p c → per p a c0 c1 c → mem p c' → per p a c0 c1 c' → φ c = φ c' → c = c'))
    (hPL : ∀ p, level p < j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) → f < S.card →
      ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ∃ a ∈ dirs p, per p a x y z)
    (hbase : ∀ p, level p = j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) → S.card ≤ B) :
    ∀ p, level p = 0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) →
      S.card + 1 ≤ G ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2) * (B + 1) := by
  -- the lists of level `j₀ - i` have at most `bnd i` members
  have key : ∀ i, i ≤ j0 → ∀ p, level p + i = j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) →
      S.card ≤ bnd N j0 f G B i := by
    intro i
    induction i with
    | zero =>
      intro _ p hp S hS
      exact hbase p (by omega) S hS
    | succ i ih =>
      intro hi p hp S hS
      have hlev : level p < j0 := by omega
      have hlevel : j0 - (i + 1) = level p := by omega
      -- every pair has at most `|dirs| bnd i` periodic thirds
      have hW : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ T ⊆ S, (∀ c ∈ T, ∃ a ∈ dirs p, per p a x y c) →
          T.card ≤ 2 ^ (N - level p) * bnd N j0 f G B i := by
        intro x hx y hy hxy T hTS hT
        have hsub : T ⊆ (dirs p).biUnion (fun a => T.filter (fun c => per p a x y c)) := by
          intro c hc
          obtain ⟨a, ha, hper⟩ := hT c hc
          exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨hc, hper⟩⟩
        have hMa : ∀ a ∈ dirs p, (T.filter (fun c => per p a x y c)).card ≤ bnd N j0 f G B i := by
          intro a ha
          obtain ⟨p', hp', φ, hφmem, hφinj⟩ := hdesc p hlev x y (hS x hx) (hS y hy) hxy a ha
          have hcard : ((T.filter (fun c => per p a x y c)).image φ).card
              = (T.filter (fun c => per p a x y c)).card := by
            refine Finset.card_image_of_injOn ?_
            intro c hc c' hc' hcc
            have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
            have h2 := Finset.mem_filter.mp (Finset.mem_coe.mp hc')
            exact hφinj c c' (hS c (hTS h1.1)) h1.2 (hS c' (hTS h2.1)) h2.2 hcc
          rw [← hcard]
          refine ih (by omega) p' (by omega) _ ?_
          intro c hc
          obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
          have h1 := Finset.mem_filter.mp hc'
          exact hφmem c' (hS c' (hTS h1.1)) h1.2
        calc T.card
            ≤ ((dirs p).biUnion (fun a => T.filter (fun c => per p a x y c))).card :=
              Finset.card_le_card hsub
          _ ≤ ∑ a ∈ dirs p, (T.filter (fun c => per p a x y c)).card := Finset.card_biUnion_le
          _ ≤ (dirs p).card • bnd N j0 f G B i := Finset.sum_le_card_nsmul _ _ _ hMa
          _ ≤ 2 ^ (N - level p) * bnd N j0 f G B i := by
              rw [smul_eq_mul]
              exact Nat.mul_le_mul_right _ (hdirs p hlev)
      have h1 := one_step S (fun x y z => ∃ a ∈ dirs p, per p a x y z) f
        (2 ^ (N - level p) * bnd N j0 f G B i)
        (fun x y z ⟨a, ha, h⟩ => ⟨a, ha, hsym1 p a x y z h⟩)
        (fun x y z ⟨a, ha, h⟩ => ⟨a, ha, hsym2 p a x y z h⟩)
        (fun S' hS' hcard => hPL p hlev S' (fun c hc => hS c (hS' hc)) hcard) hW
      show S.card ≤ f + G * 2 ^ (N - (j0 - (i + 1))) * bnd N j0 f G B i
      rw [hlevel]
      calc S.card ≤ f + f.choose 2 * (2 ^ (N - level p) * bnd N j0 f G B i) := h1
        _ ≤ f + G * (2 ^ (N - level p) * bnd N j0 f G B i) :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ hGf) _
        _ = f + G * 2 ^ (N - level p) * bnd N j0 f G B i := by ring
  intro p hp S hS
  have h1 := key j0 le_rfl p (by omega) S hS
  have h2 := bnd_closed N j0 f G B hfG hj0
  omega

theorem choose_two_le_choose_three (f : ℕ) : f.choose 2 ≤ (f + 1).choose 3 := by
  have h : (f + 1).choose 3 = f.choose 2 + f.choose 3 := Nat.choose_succ_succ' f 2
  omega

theorem succ_le_four_mul_choose {f : ℕ} (hf : 2 ≤ f) : f + 1 ≤ 4 * f.choose 2 := by
  have h1 : f.choose 2 = f * (f - 1) / 2 := Nat.choose_two_right f
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 2 := ⟨f - 2, by omega⟩
  have h2 : (m + 2) * (m + 2 - 1) = 2 * (m + 1) + m * (m + 1) := by
    have : m + 2 - 1 = m + 1 := by omega
    rw [this]
    ring
  have h3 : m + 1 ≤ (m + 2).choose 2 := by
    rw [h1, h2, Nat.mul_add_div (by norm_num : 0 < 2)]
    omega
  omega

/-- **Theorem R, abstract form, with the constant of the notes**: `G = C(f + 1, 3)`, `f ≥ 2`,
`j₀ ≤ N - 1`. The conclusion is the count
`C(f + 1, 3)^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (B + 1)`. -/
theorem abstract_descent_notes {Pb C A : Type*} (level : Pb → ℕ) (mem : Pb → C → Prop)
    (dirs : Pb → Finset A) (per : Pb → A → C → C → C → Prop) (N j0 f B : ℕ)
    (hf : 2 ≤ f) (hj0 : j0 + 1 ≤ N)
    (hdirs : ∀ p, level p < j0 → (dirs p).card ≤ 2 ^ (N - level p))
    (hsym1 : ∀ p a c0 c1 c, per p a c0 c1 c → per p a c0 c c1)
    (hsym2 : ∀ p a c0 c1 c, per p a c0 c1 c → per p a c1 c0 c)
    (hdesc : ∀ p, level p < j0 → ∀ c0 c1, mem p c0 → mem p c1 → c0 ≠ c1 → ∀ a ∈ dirs p,
      ∃ p', level p' = level p + 1 ∧ ∃ φ : C → C,
        (∀ c, mem p c → per p a c0 c1 c → mem p' (φ c)) ∧
        (∀ c c', mem p c → per p a c0 c1 c → mem p c' → per p a c0 c1 c' → φ c = φ c' → c = c'))
    (hPL : ∀ p, level p < j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) → f < S.card →
      ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ∃ a ∈ dirs p, per p a x y z)
    (hbase : ∀ p, level p = j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) → S.card ≤ B) :
    ∀ p, level p = 0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) →
      S.card + 1 ≤ ((f + 1).choose 3) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2) * (B + 1) :=
  abstract_descent level mem dirs per N j0 f ((f + 1).choose 3) B (choose_two_le_choose_three f)
    ((succ_le_four_mul_choose hf).trans (Nat.mul_le_mul_left 4 (choose_two_le_choose_three f)))
    hj0 hdirs hsym1 hsym2 hdesc hPL hbase

/-- **A sharper constant**: `G = C(f, 2)` in place of `C(f + 1, 3)`. This is not in the notes. -/
theorem abstract_descent_sharp {Pb C A : Type*} (level : Pb → ℕ) (mem : Pb → C → Prop)
    (dirs : Pb → Finset A) (per : Pb → A → C → C → C → Prop) (N j0 f B : ℕ)
    (hf : 2 ≤ f) (hj0 : j0 + 1 ≤ N)
    (hdirs : ∀ p, level p < j0 → (dirs p).card ≤ 2 ^ (N - level p))
    (hsym1 : ∀ p a c0 c1 c, per p a c0 c1 c → per p a c0 c c1)
    (hsym2 : ∀ p a c0 c1 c, per p a c0 c1 c → per p a c1 c0 c)
    (hdesc : ∀ p, level p < j0 → ∀ c0 c1, mem p c0 → mem p c1 → c0 ≠ c1 → ∀ a ∈ dirs p,
      ∃ p', level p' = level p + 1 ∧ ∃ φ : C → C,
        (∀ c, mem p c → per p a c0 c1 c → mem p' (φ c)) ∧
        (∀ c c', mem p c → per p a c0 c1 c → mem p c' → per p a c0 c1 c' → φ c = φ c' → c = c'))
    (hPL : ∀ p, level p < j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) → f < S.card →
      ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ∃ a ∈ dirs p, per p a x y z)
    (hbase : ∀ p, level p = j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) → S.card ≤ B) :
    ∀ p, level p = 0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) →
      S.card + 1 ≤ (f.choose 2) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2) * (B + 1) :=
  abstract_descent level mem dirs per N j0 f (f.choose 2) B le_rfl (succ_le_four_mul_choose hf)
    hj0 hdirs hsym1 hsym2 hdesc hPL hbase

/-! ### Note 37 Theorem 3.5, abstract form -/

/-- The bound of the recursion of note 37 Corollary 3.4, counted from the level `j₀`:
`bndDP 0 = B₀` and `bndDP (i + 1) = (B + 2) + 2^(N - j) bndDP i` with `j = j₀ - (i + 1)`. -/
def bndDP (N j0 B B0 : ℕ) : ℕ → ℕ
  | 0 => B0
  | i + 1 => (B + 2) + 2 ^ (N - (j0 - (i + 1))) * bndDP N j0 B B0 i

theorem bndDP_le (N j0 B B0 : ℕ) (hj0 : j0 ≤ N) :
    ∀ i, i ≤ j0 →
      bndDP N j0 B B0 i ≤ 2 ^ (i * (N - j0) + i * (i + 1) / 2) * (i * (B + 2) + B0) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [bndDP]
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have hexp : N - (j0 - (i + 1)) = (N - j0) + (i + 1) := by omega
    have he2 : (i + 1) * (N - j0) + (i + 1) * (i + 1 + 1) / 2
        = ((N - j0) + (i + 1)) + (i * (N - j0) + i * (i + 1) / 2) := by
      have h1 : (i + 1) * (i + 1 + 1) = i * (i + 1) + 2 * (i + 1) := by ring
      rw [h1, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      ring
    have hpos : 1 ≤ 2 ^ ((N - j0) + (i + 1) + (i * (N - j0) + i * (i + 1) / 2)) :=
      Nat.one_le_two_pow
    show (B + 2) + 2 ^ (N - (j0 - (i + 1))) * bndDP N j0 B B0 i ≤ _
    rw [hexp, he2]
    calc (B + 2) + 2 ^ ((N - j0) + (i + 1)) * bndDP N j0 B B0 i
        ≤ (B + 2) + 2 ^ ((N - j0) + (i + 1))
            * (2 ^ (i * (N - j0) + i * (i + 1) / 2) * (i * (B + 2) + B0)) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ ih') _
      _ = 1 * (B + 2) + 2 ^ ((N - j0) + (i + 1) + (i * (N - j0) + i * (i + 1) / 2))
            * (i * (B + 2) + B0) := by
          rw [pow_add ((2 : ℕ)) ((N - j0) + (i + 1))]
          ring
      _ ≤ 2 ^ ((N - j0) + (i + 1) + (i * (N - j0) + i * (i + 1) / 2)) * (B + 2)
            + 2 ^ ((N - j0) + (i + 1) + (i * (N - j0) + i * (i + 1) / 2))
              * (i * (B + 2) + B0) :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ hpos) _
      _ = 2 ^ ((N - j0) + (i + 1) + (i * (N - j0) + i * (i + 1) / 2))
            * ((i + 1) * (B + 2) + B0) := by ring

/-- **Note 37 Theorem 3.5 (with Corollary 3.4), abstract form.** In the setting of
`abstract_descent`, replace the hypothesis PL by DP`(B)`: at every level `j < j₀`, every list has
a pair `(c₀, c₁)` for which at most `B` members are not periodic for any direction. Then every
list of level `0` has at most `2^(N j₀ - j₀ (j₀ - 1) / 2) (j₀ (B + 2) + B₀)` members, `B₀` a
bound for the lists of level `j₀`. -/
theorem abstract_descent_DP {Pb C A : Type*} (level : Pb → ℕ) (mem : Pb → C → Prop)
    (dirs : Pb → Finset A) (per : Pb → A → C → C → C → Prop) (N j0 B B0 : ℕ) (hj0 : j0 ≤ N)
    (hdirs : ∀ p, level p < j0 → (dirs p).card ≤ 2 ^ (N - level p))
    (hdesc : ∀ p, level p < j0 → ∀ c0 c1, mem p c0 → mem p c1 → c0 ≠ c1 → ∀ a ∈ dirs p,
      ∃ p', level p' = level p + 1 ∧ ∃ φ : C → C,
        (∀ c, mem p c → per p a c0 c1 c → mem p' (φ c)) ∧
        (∀ c c', mem p c → per p a c0 c1 c → mem p c' → per p a c0 c1 c' → φ c = φ c' → c = c'))
    (hDP : ∀ p, level p < j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) → 2 ≤ S.card →
      ∃ c0 ∈ S, ∃ c1 ∈ S, c0 ≠ c1 ∧
        ∀ T ⊆ S, (∀ c ∈ T, ¬ ∃ a ∈ dirs p, per p a c0 c1 c) → T.card ≤ B)
    (hbase : ∀ p, level p = j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) → S.card ≤ B0) :
    ∀ p, level p = 0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) →
      S.card ≤ 2 ^ (N * j0 - j0 * (j0 - 1) / 2) * (j0 * (B + 2) + B0) := by
  have key : ∀ i, i ≤ j0 → ∀ p, level p + i = j0 → ∀ S : Finset C, (∀ c ∈ S, mem p c) →
      S.card ≤ bndDP N j0 B B0 i := by
    intro i
    induction i with
    | zero =>
      intro _ p hp S hS
      exact hbase p (by omega) S hS
    | succ i ih =>
      intro hi p hp S hS
      have hlev : level p < j0 := by omega
      have hlevel : j0 - (i + 1) = level p := by omega
      show S.card ≤ (B + 2) + 2 ^ (N - (j0 - (i + 1))) * bndDP N j0 B B0 i
      rw [hlevel]
      rcases Nat.lt_or_ge S.card 2 with hsmall | hbig
      · omega
      obtain ⟨c0, hc0, c1, hc1, h01, hB⟩ := hDP p hlev S hS hbig
      -- the members periodic for the pair and a direction
      have hMa : ∀ a ∈ dirs p, (S.filter (fun c => per p a c0 c1 c)).card ≤ bndDP N j0 B B0 i := by
        intro a ha
        obtain ⟨p', hp', φ, hφmem, hφinj⟩ := hdesc p hlev c0 c1 (hS c0 hc0) (hS c1 hc1) h01 a ha
        have hcard : ((S.filter (fun c => per p a c0 c1 c)).image φ).card
            = (S.filter (fun c => per p a c0 c1 c)).card := by
          refine Finset.card_image_of_injOn ?_
          intro c hc c' hc' hcc
          have h1 := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
          have h2 := Finset.mem_filter.mp (Finset.mem_coe.mp hc')
          exact hφinj c c' (hS c h1.1) h1.2 (hS c' h2.1) h2.2 hcc
        rw [← hcard]
        refine ih (by omega) p' (by omega) _ ?_
        intro c hc
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
        have h1 := Finset.mem_filter.mp hc'
        exact hφmem c' (hS c' h1.1) h1.2
      have hsub : S ⊆ S.filter (fun c => ¬ ∃ a ∈ dirs p, per p a c0 c1 c)
          ∪ (dirs p).biUnion (fun a => S.filter (fun c => per p a c0 c1 c)) := by
        intro c hc
        by_cases hper : ∃ a ∈ dirs p, per p a c0 c1 c
        · obtain ⟨a, ha, h⟩ := hper
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨hc, h⟩⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, hper⟩)
      have h1 : (S.filter (fun c => ¬ ∃ a ∈ dirs p, per p a c0 c1 c)).card ≤ B :=
        hB _ (Finset.filter_subset _ _) fun c hc => (Finset.mem_filter.mp hc).2
      calc S.card
          ≤ (S.filter (fun c => ¬ ∃ a ∈ dirs p, per p a c0 c1 c)).card
            + ((dirs p).biUnion (fun a => S.filter (fun c => per p a c0 c1 c))).card :=
            (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        _ ≤ B + ∑ a ∈ dirs p, (S.filter (fun c => per p a c0 c1 c)).card :=
            Nat.add_le_add h1 Finset.card_biUnion_le
        _ ≤ B + (dirs p).card • bndDP N j0 B B0 i :=
            Nat.add_le_add_left (Finset.sum_le_card_nsmul _ _ _ hMa) _
        _ ≤ (B + 2) + 2 ^ (N - level p) * bndDP N j0 B B0 i := by
            rw [smul_eq_mul]
            exact Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ (hdirs p hlev))
  intro p hp S hS
  have h1 := key j0 le_rfl p (by omega) S hS
  have h2 := bndDP_le N j0 B B0 hj0 j0 le_rfl
  rw [expo_eq N j0 hj0] at h2
  exact h1.trans h2

end PeriodDescent
