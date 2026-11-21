/-
Theorem 6.1 of the paper, the tree bound: a list-size bound for single words gives one for
interleaved words with any number of lanes, through the recursion
`N(P) = N(P - g) + (L - 1) N(⌊P/2⌋)`.

The proof follows the paper: the list members are the leaves of a tree whose node of depth `i` is
a choice of codewords for the first `i` lanes, with `T` the set of coordinates where they all
agree with the word. Here the lanes are processed by induction on a finite set `J` of lanes, and
a node is a set `S` of list members that are pairwise different on `J`.
-/
import Interleave.Basic

open Finset

namespace Interleave

/-- The recursion of Theorem 6.1 of the paper: `N(P) = 1` for `P < 2g`, and
`N(P) = N(P - g) + (L - 1) N(⌊P/2⌋)` for `P ≥ 2g`. (For `g = 0` it is `1`.) -/
def treeN (L g P : ℕ) : ℕ :=
  if h : 0 < g ∧ 2 * g ≤ P then treeN L g (P - g) + (L - 1) * treeN L g (P / 2) else 1
termination_by P
decreasing_by all_goals omega

theorem treeN_of_not {L g P : ℕ} (h : ¬(0 < g ∧ 2 * g ≤ P)) : treeN L g P = 1 := by
  conv_lhs => rw [treeN]
  simp only [h, ↓reduceDIte]

theorem treeN_of_lt {L g P : ℕ} (h : P < 2 * g) : treeN L g P = 1 :=
  treeN_of_not (by omega)

theorem treeN_zero_left (L P : ℕ) : treeN L 0 P = 1 :=
  treeN_of_not (by omega)

theorem treeN_of_le {L g P : ℕ} (hg : 0 < g) (h : 2 * g ≤ P) :
    treeN L g P = treeN L g (P - g) + (L - 1) * treeN L g (P / 2) := by
  conv_lhs => rw [treeN]
  simp only [hg, h, and_self, ↓reduceDIte]

theorem treeN_pos (L g P : ℕ) : 0 < treeN L g P := by
  induction P using Nat.strong_induction_on with
  | _ P ih =>
    by_cases h : 0 < g ∧ 2 * g ≤ P
    · rw [treeN_of_le h.1 h.2]
      exact Nat.add_pos_left (ih _ (by omega)) _
    · rw [treeN_of_not h]
      exact Nat.one_pos

/-- `N` is non-decreasing. -/
theorem treeN_mono (L g : ℕ) {P Q : ℕ} (hPQ : P ≤ Q) : treeN L g P ≤ treeN L g Q := by
  induction Q using Nat.strong_induction_on generalizing P with
  | _ Q ih =>
    by_cases hQ : 0 < g ∧ 2 * g ≤ Q
    · by_cases hP : 0 < g ∧ 2 * g ≤ P
      · rw [treeN_of_le hP.1 hP.2, treeN_of_le hQ.1 hQ.2]
        exact Nat.add_le_add (ih _ (by omega) (by omega))
          (Nat.mul_le_mul_left _ (ih _ (by omega) (by omega)))
      · rw [treeN_of_not hP, treeN_of_le hQ.1 hQ.2]
        exact le_trans (treeN_pos L g (Q - g)) (Nat.le_add_right _ _)
    · have hP : ¬(0 < g ∧ 2 * g ≤ P) := fun h => hQ ⟨h.1, h.2.trans hPQ⟩
      rw [treeN_of_not hP, treeN_of_not hQ]

/-- `N = L` on `[2g, 3g)`. -/
theorem treeN_eq_L {L g P : ℕ} (hL : 1 ≤ L) (h2 : 2 * g ≤ P) (h3 : P < 3 * g) :
    treeN L g P = L := by
  rw [treeN_of_le (by omega) h2, treeN_of_lt (by omega), treeN_of_lt (by omega)]
  omega

/-- `N = 2L - 1` on `[3g, 4g)`. -/
theorem treeN_eq_two_mul {L g P : ℕ} (hL : 1 ≤ L) (h3 : 3 * g ≤ P) (h4 : P < 4 * g) :
    treeN L g P = 2 * L - 1 := by
  rw [treeN_of_le (by omega) (by omega), treeN_eq_L hL (by omega) (by omega),
    treeN_of_lt (by omega)]
  omega

/-- `N = L² + L - 1` on `[4g, 5g)`. -/
theorem treeN_eq_sq {L g P : ℕ} (hL : 1 ≤ L) (h4 : 4 * g ≤ P) (h5 : P < 5 * g) :
    treeN L g P = L * L + L - 1 := by
  rw [treeN_of_le (by omega) (by omega), treeN_eq_two_mul hL (by omega) (by omega),
    treeN_eq_L hL (by omega) (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : k + 1 - 1 = k := by omega
  have e3 : (k + 1) * (k + 1) + (k + 1) - 1 = (k + 1) * (k + 1) + k := by omega
  rw [e1, e2, e3]
  ring

theorem treeN_le_L {L g P : ℕ} (hL : 1 ≤ L) (h3 : P < 3 * g) : treeN L g P ≤ L := by
  by_cases h2 : 2 * g ≤ P
  · exact (treeN_eq_L hL h2 h3).le
  · rw [treeN_of_lt (by omega)]
    exact hL

theorem treeN_le_two_mul {L g P : ℕ} (hL : 1 ≤ L) (h4 : P < 4 * g) :
    treeN L g P ≤ 2 * L - 1 := by
  by_cases h3 : 3 * g ≤ P
  · exact (treeN_eq_two_mul hL h3 h4).le
  · exact (treeN_le_L hL (by omega)).trans (by omega)

theorem treeN_le_sq {L g P : ℕ} (hL : 1 ≤ L) (h5 : P < 5 * g) :
    treeN L g P ≤ L * L + L - 1 := by
  by_cases h4 : 4 * g ≤ P
  · exact (treeN_eq_sq hL h4 h5).le
  · refine (treeN_le_two_mul hL (by omega)).trans ?_
    have : L ≤ L * L := Nat.le_mul_self L
    omega

variable {ι α : Type*}

/-- The claim in the proof of Theorem 6.1 of the paper: below a node with agreement set `T`, the
number of leaves is at most `N(|T| - d)`. The node is the set `S`: tuples whose lanes in `J` are
codewords agreeing with the lanes of `w` on at least `a` common coordinates of `T`, pairwise
different on the lanes of `J`. -/
theorem tree_core {D : Finset ι} {C : Set (ι → α)} {d a L : ℕ} (hC : AgreeLE D C d)
    (hda : d < a) (hL : ListBound D C a L) {m : Type*} (w : ι → m → α) (J : Finset m) :
    ∀ (T : Finset ι) (S : Finset (ι → m → α)), T ⊆ D →
      (∀ c ∈ S, ∀ j ∈ J, lane j c ∈ C) →
      (∀ c ∈ S, ∃ U ⊆ T, a ≤ U.card ∧ ∀ i ∈ U, ∀ j ∈ J, w i j = c i j) →
      (∀ c ∈ S, ∀ c' ∈ S, (∀ j ∈ J, lane j c = lane j c') → c = c') →
      S.card ≤ treeN L (a - d) (T.card - d) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro T S _ _ _ hinj
    have h1 : S.card ≤ 1 :=
      card_le_one.mpr fun c hc c' hc' => hinj c hc c' hc' (fun j hj => absurd hj (notMem_empty j))
    exact h1.trans (treeN_pos _ _ _)
  | insert j J hj ih =>
    intro T S hTD hmem hagr hinj
    -- the agreement set of the child by `b`
    obtain ⟨Ta, hTa⟩ : ∃ Ta : (ι → α) → Finset ι, ∀ b i, i ∈ Ta b ↔ i ∈ T ∧ w i j = b i :=
      ⟨fun b => T.filter (fun i => w i j = b i), fun b i => mem_filter⟩
    have hTsub : ∀ b, Ta b ⊆ T := fun b i hi => ((hTa b i).mp hi).1
    -- the leaves below the child by `b`
    have hfib : ∀ b, (S.filter (fun c => lane j c = b)).card ≤
        treeN L (a - d) ((Ta b).card - d) := by
      intro b
      refine ih (Ta b) _ ((hTsub b).trans hTD) ?_ ?_ ?_
      · intro c hc j' hj'
        exact hmem c (mem_filter.mp hc).1 j' (mem_insert_of_mem hj')
      · intro c hc
        obtain ⟨hcS, hcb⟩ := mem_filter.mp hc
        obtain ⟨U, hUT, hUa, hU⟩ := hagr c hcS
        refine ⟨U, fun i hi => (hTa b i).mpr ⟨hUT hi, ?_⟩, hUa,
          fun i hi j' hj' => hU i hi j' (mem_insert_of_mem hj')⟩
        rw [← hcb]
        exact hU i hi j (mem_insert_self _ _)
      · intro c hc c' hc' h
        obtain ⟨hcS, hcb⟩ := mem_filter.mp hc
        obtain ⟨hcS', hcb'⟩ := mem_filter.mp hc'
        refine hinj c hcS c' hcS' fun j' hj' => ?_
        rcases mem_insert.mp hj' with rfl | hj'
        · exact hcb.trans hcb'.symm
        · exact h j' hj'
    -- a child is a codeword close to lane `j` of the word (Fact 2)
    have hch : ∀ b ∈ S.image (lane j),
        b ∈ C ∧ a ≤ (Ta b).card ∧ a ≤ (agr D (lane j w) b).card := by
      intro b hb
      obtain ⟨c, hcS, rfl⟩ := mem_image.mp hb
      obtain ⟨U, hUT, hUa, hU⟩ := hagr c hcS
      have hUTa : U ⊆ Ta (lane j c) := fun i hi =>
        (hTa _ i).mpr ⟨hUT hi, hU i hi j (mem_insert_self _ _)⟩
      have hTaAgr : Ta (lane j c) ⊆ agr D (lane j w) (lane j c) := fun i hi =>
        mem_agr.mpr ⟨hTD ((hTa _ i).mp hi).1, ((hTa _ i).mp hi).2⟩
      exact ⟨hmem c hcS j (mem_insert_self _ _), hUa.trans (card_le_card hUTa),
        hUa.trans (card_le_card (hUTa.trans hTaAgr))⟩
    have hchL : (S.image (lane j)).card ≤ L :=
      hL (lane j w) _ fun b hb => ⟨(hch b hb).1, (hch b hb).2.2⟩
    -- Fact 1: two children share at most `d` coordinates of `T`
    have hfact1 : ∀ b ∈ S.image (lane j), ∀ b' ∈ S.image (lane j), b ≠ b' →
        (Ta b).card + (Ta b').card ≤ T.card + d := by
      intro b hb b' hb' hne
      have h1 := card_union_add_card_inter (Ta b) (Ta b')
      have h2 : (Ta b ∪ Ta b').card ≤ T.card :=
        card_le_card (union_subset (hTsub b) (hTsub b'))
      have h3 : (Ta b ∩ Ta b').card ≤ d := by
        refine le_trans (card_le_card ?_) (hC b (hch b hb).1 b' (hch b' hb').1 hne)
        intro i hi
        obtain ⟨hi1, hi2⟩ := mem_inter.mp hi
        exact mem_agr.mpr ⟨hTD ((hTa b i).mp hi1).1,
          ((hTa b i).mp hi1).2.symm.trans ((hTa b' i).mp hi2).2⟩
      omega
    have hsum : S.card = ∑ b ∈ S.image (lane j), (S.filter (fun c => lane j c = b)).card :=
      card_eq_sum_card_image (lane j) S
    rcases (S.image (lane j)).eq_empty_or_nonempty with he | hne
    · rw [hsum, he, sum_empty]
      exact Nat.zero_le _
    -- the heavy child
    obtain ⟨h, hh, hmax⟩ := exists_max_image (S.image (lane j)) (fun b => (Ta b).card) hne
    rw [hsum, ← add_sum_erase _ _ hh]
    rcases ((S.image (lane j)).erase h).eq_empty_or_nonempty with he | hne'
    · rw [he, sum_empty, add_zero]
      exact (hfib h).trans (treeN_mono _ _ (Nat.sub_le_sub_right (card_le_card (hTsub h)) d))
    -- two children or more: Facts 3 and 4
    obtain ⟨b', hb'⟩ := hne'
    obtain ⟨hb'h, hb'm⟩ := mem_erase.mp hb'
    have h1 := hfact1 h hh b' hb'm (Ne.symm hb'h)
    have ha1 := (hch h hh).2.1
    have ha2 := (hch b' hb'm).2.1
    have hcond : 0 < a - d ∧ 2 * (a - d) ≤ T.card - d := by omega
    rw [treeN_of_le hcond.1 hcond.2]
    refine Nat.add_le_add ((hfib h).trans (treeN_mono _ _ (by omega))) ?_
    calc ∑ b ∈ (S.image (lane j)).erase h, (S.filter (fun c => lane j c = b)).card
        ≤ ∑ _b ∈ (S.image (lane j)).erase h, treeN L (a - d) ((T.card - d) / 2) := by
          refine sum_le_sum fun b hb => ?_
          obtain ⟨hbh, hbm⟩ := mem_erase.mp hb
          have h2 := hfact1 b hbm h hh hbh
          have h3 := hmax b hbm
          exact (hfib b).trans (treeN_mono _ _ (by omega))
      _ = ((S.image (lane j)).card - 1) * treeN L (a - d) ((T.card - d) / 2) := by
          rw [sum_const, card_erase_of_mem hh, smul_eq_mul]
      _ ≤ (L - 1) * treeN L (a - d) ((T.card - d) / 2) :=
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hchL 1)

variable {D : Finset ι} {C : Set (ι → α)} {d a L : ℕ}

/-- **Theorem 6.1 of the paper.** If two distinct codewords agree on at most `d` coordinates,
`d < a`, and every word has at most `L` codewords within agreement `a`, then every interleaved
word, with any finite number of lanes, has at most `N(n - d)` tuples of codewords within agreement
`a`, where `N = treeN L (a - d)` and `n = |D|`. -/
theorem interleave_listBound (hC : AgreeLE D C d) (hda : d < a) (hL : ListBound D C a L)
    (m : Type*) [Finite m] :
    ListBound D (interleave m C) a (treeN L (a - d) (D.card - d)) := by
  classical
  have := Fintype.ofFinite m
  intro w S hS
  refine tree_core hC hda hL w univ D S (Subset.refl _) (fun c hc j _ => (hS c hc).1 j) ?_ ?_
  · intro c hc
    exact ⟨agr D w c, agr_subset _ _ _, (hS c hc).2,
      fun i hi j _ => congrFun (mem_agr.mp hi).2 j⟩
  · intro c _ c' _ h
    funext i j
    exact congrFun (h j (mem_univ j)) i

/-- Theorem 6.1, first special case: for `a > (n + d)/2` the interleaved list has at most one
element. No list hypothesis is needed. -/
theorem interleave_listBound_one (hC : AgreeLE D C d) (h2 : D.card + d < 2 * a) (m : Type*) :
    ListBound D (interleave m C) a 1 :=
  (hC.interleave m).listBound_one h2

/-- The bound of Theorem 6.1 can be replaced by any `B` it does not exceed when `1 ≤ L`, and
which is `0` when `L = 0`, provided there is at least one lane. -/
theorem interleave_listBound_le (hC : AgreeLE D C d) (hda : d < a) (hL : ListBound D C a L)
    (m : Type*) [Finite m] [Nonempty m] {B : ℕ} (h0 : L ≤ B)
    (hB : 1 ≤ L → treeN L (a - d) (D.card - d) ≤ B) : ListBound D (interleave m C) a B := by
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · exact (hL.interleave_zero m).mono le_rfl h0
  · exact (interleave_listBound hC hda hL m).mono le_rfl (hB hpos)

/-- Theorem 6.1, second special case: for `a > (n + 2d)/3` interleaving costs nothing. -/
theorem interleave_listBound_same (hC : AgreeLE D C d) (hda : d < a) (hL : ListBound D C a L)
    (h3 : D.card + 2 * d < 3 * a) (m : Type*) [Finite m] [Nonempty m] :
    ListBound D (interleave m C) a L :=
  interleave_listBound_le hC hda hL m le_rfl fun h1 => treeN_le_L h1 (by omega)

/-- For `a > (n + 2d)/3` the largest interleaved list and the largest single-lane list are
equal. -/
theorem interleave_listBound_iff (hC : AgreeLE D C d) (hda : d < a)
    (h3 : D.card + 2 * d < 3 * a) (m : Type*) [Finite m] [Nonempty m] :
    ListBound D (interleave m C) a L ↔ ListBound D C a L :=
  ⟨fun h => h.of_interleave, fun h => interleave_listBound_same hC hda h h3 m⟩

/-- Theorem 6.1, third special case: for `a > (n + 3d)/4` the interleaved list has at most
`2L - 1` elements. -/
theorem interleave_listBound_two_mul (hC : AgreeLE D C d) (hda : d < a)
    (hL : ListBound D C a L) (h4 : D.card + 3 * d < 4 * a) (m : Type*) [Finite m] [Nonempty m] :
    ListBound D (interleave m C) a (2 * L - 1) :=
  interleave_listBound_le hC hda hL m (by omega) fun h1 => treeN_le_two_mul h1 (by omega)

/-- Theorem 6.1, fourth special case: for `a > (n + 4d)/5` the interleaved list has at most
`L² + L - 1` elements. -/
theorem interleave_listBound_sq (hC : AgreeLE D C d) (hda : d < a) (hL : ListBound D C a L)
    (h5 : D.card + 4 * d < 5 * a) (m : Type*) [Finite m] [Nonempty m] :
    ListBound D (interleave m C) a (L * L + L - 1) :=
  interleave_listBound_le hC hda hL m (by have := Nat.le_mul_self L; omega)
    fun h1 => treeN_le_sq h1 (by omega)

end Interleave
