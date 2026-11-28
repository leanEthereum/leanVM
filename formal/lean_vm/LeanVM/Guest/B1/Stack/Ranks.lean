/-
  LeanVM.Guest.B1.Stack.Ranks

  The guest's ranking of the block groups places every block where `stackOffsets` does.
-/

module

public import LeanVM.Guest.B1.Stack.Offsets
public import LeanVM.Guest.B1.Stack.CertifyS

/-!
# The ranks place the blocks as `stackOffsets` does

`grpOf b`: block `b`'s group. With the groups ranked by strictly falling keys `csN` (`53 κ + 52 -
b0`), rank `r`'s group's block `b0 + j` is at `csTot r + j·2^κ`, the sum of `2^size` over the blocks
`StkBefore` it (`rank_offset`), and the ranks' total is the sum over every block (`ranks_total`).
-/

namespace LeanVM.Guest.B1.Stack

@[expose] public section

/-- Block `b`'s group. -/
def grpOf (b : ℕ) : ℕ := ((List.range 8).find? fun gi ↦ decide (b < (csG gi).b0 + (csG gi).len)).getD 0

theorem grpOf_facts : ∀ b < 52, grpOf b < 8 ∧ (csG (grpOf b)).b0 ≤ b ∧
    b < (csG (grpOf b)).b0 + (csG (grpOf b)).len := by decide

theorem grpOf_block : ∀ gi < 8, ∀ j < (csG gi).len, grpOf ((csG gi).b0 + j) = gi := by decide

theorem groups_disjoint : ∀ g1 < 8, ∀ g2 < 8, (csG g1).b0 < (csG g2).b0 →
    (csG g1).b0 + (csG g1).len ≤ (csG g2).b0 := by decide

theorem groups_b0_le : ∀ gi < 8, (csG gi).b0 ≤ 48 := by decide

theorem groups_b0_inj : ∀ g1 < 8, ∀ g2 < 8, (csG g1).b0 = (csG g2).b0 → g1 = g2 := by decide

/-- The blocks, group by group. -/
theorem sum_blocks (f : ℕ → ℕ) :
    ∑ b ∈ Finset.range 52, f b = ∑ gi ∈ Finset.range 8, ∑ j ∈ Finset.range (csG gi).len, f ((csG gi).b0 + j) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, csG, csGroups, List.getD_cons_zero,
    List.getD_cons_succ]
  ring

/-- A ranking: the groups by strictly falling keys. -/
structure Ranking (kv : ℕ → ℕ) (ρ : ℕ → ℕ) : Prop where
  lt : ∀ r < 8, ρ r < 8
  desc : ∀ r < 7, csN kv (ρ (r + 1)) < csN kv (ρ r)

theorem Ranking.anti {kv : ℕ → ℕ} {ρ : ℕ → ℕ} (h : Ranking kv ρ) :
    ∀ r1 r2, r1 < r2 → r2 < 8 → csN kv (ρ r2) < csN kv (ρ r1) := by
  intro r1 r2 h12 h2
  induction r2 with
  | zero => omega
  | succ r ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h12 with hl | hl
    · exact lt_trans (h.desc r (by omega)) (ih hl (by omega))
    · subst hl; exact h.desc r1 (by omega)

theorem Ranking.inj {kv : ℕ → ℕ} {ρ : ℕ → ℕ} (h : Ranking kv ρ) {r1 r2 : ℕ} (h1 : r1 < 8)
    (h2 : r2 < 8) (he : ρ r1 = ρ r2) : r1 = r2 := by
  rcases Nat.lt_trichotomy r1 r2 with h' | h' | h'
  · have := h.anti r1 r2 h' h2; rw [he] at this; omega
  · exact h'
  · have := h.anti r2 r1 h' h1; rw [he] at this; omega

theorem Ranking.surj {kv : ℕ → ℕ} {ρ : ℕ → ℕ} (h : Ranking kv ρ) :
    ∀ gi < 8, ∃ r < 8, ρ r = gi := by
  have himg : (Finset.range 8).image ρ = Finset.range 8 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (h.lt r (Finset.mem_range.1 hr))
    · rw [Finset.card_image_of_injOn (fun a ha b hb e ↦ h.inj (Finset.mem_range.1 ha)
        (Finset.mem_range.1 hb) e)]
  intro gi hgi
  have : gi ∈ (Finset.range 8).image ρ := by rw [himg]; exact Finset.mem_range.2 hgi
  obtain ⟨r, hr, e⟩ := Finset.mem_image.1 this
  exact ⟨r, Finset.mem_range.1 hr, e⟩

/-- The groups summed in rank order. -/
theorem Ranking.sum_groups {kv : ℕ → ℕ} {ρ : ℕ → ℕ} (h : Ranking kv ρ) (F : ℕ → ℕ) :
    ∑ gi ∈ Finset.range 8, F gi = ∑ r ∈ Finset.range 8, F (ρ r) := by
  symm
  apply Finset.sum_nbij ρ (fun r hr ↦ Finset.mem_range.2 (h.lt r (Finset.mem_range.1 hr)))
    (fun a ha b hb e ↦ h.inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) e)
  · intro gi hgi
    obtain ⟨r, hr, e⟩ := h.surj gi (Finset.mem_range.1 hgi)
    exact ⟨r, Finset.mem_range.2 hr, e⟩
  · intro _ _; rfl

/-- A key's order: a larger key is a larger `κ`, or the same and an earlier first block. -/
theorem csN_lt_iff {kv : ℕ → ℕ} {g1 g2 : ℕ} (h1 : g1 < 8) (h2 : g2 < 8) :
    csN kv g1 < csN kv g2 ↔ csKap kv g1 < csKap kv g2 ∨
      (csKap kv g1 = csKap kv g2 ∧ (csG g2).b0 < (csG g1).b0) := by
  have := groups_b0_le g1 h1
  have := groups_b0_le g2 h2
  unfold csN
  omega

theorem sum_rank_split (a : ℕ → ℕ) (c : ℕ) {r : ℕ} (hr : r < 8) :
    ∑ r' ∈ Finset.range 8, (if r' < r then a r' else if r' = r then c else 0) =
      ∑ r' ∈ Finset.range r, a r' + c := by
  have key : ∀ n, r < n → ∑ r' ∈ Finset.range n, (if r' < r then a r' else if r' = r then c else 0) =
      ∑ r' ∈ Finset.range r, a r' + c := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | h
      · rw [ih h]
        simp [show ¬ n < r by omega, show n ≠ r by omega]
      · subst h
        simp only [lt_irrefl, ↓reduceIte]
        congr 1
        exact Finset.sum_congr rfl fun r' hr' ↦ by simp [Finset.mem_range.1 hr']
  exact key 8 hr

/-- **Rank `r`'s block `b0 + j`** is at `csTot r + j·2^κ`, the blocks before it. -/
theorem rank_offset {kv : ℕ → ℕ} {ρ : ℕ → ℕ} (h : Ranking kv ρ) {r j : ℕ} (hr : r < 8)
    (hj : j < (csG (ρ r)).len) :
    stkBeforeSum (fun b ↦ csKap kv (grpOf b)) 52 ((csG (ρ r)).b0 + j) =
      csTot kv ρ r + j * 2 ^ csKap kv (ρ r) := by
  set gi := ρ r with hgi
  have hgi8 : gi < 8 := h.lt r hr
  set b := (csG gi).b0 + j
  unfold stkBeforeSum
  rw [Finset.sum_filter, sum_blocks, h.sum_groups]
  have inner : ∀ r' ∈ Finset.range 8, (∑ j' ∈ Finset.range (csG (ρ r')).len,
      if StkBefore (fun b ↦ csKap kv (grpOf b)) ((csG (ρ r')).b0 + j') b then
        2 ^ csKap kv (grpOf ((csG (ρ r')).b0 + j')) else 0) =
      if r' < r then csSize kv (ρ r') else if r' = r then j * 2 ^ csKap kv gi else 0 := by
    intro r' hr'
    have hr'8 := Finset.mem_range.1 hr'
    have hg' := h.lt r' hr'8
    have hblk : ∀ j' < (csG (ρ r')).len, grpOf ((csG (ρ r')).b0 + j') = ρ r' :=
      fun j' hj' ↦ grpOf_block _ hg' j' hj'
    have hb : grpOf b = gi := grpOf_block gi hgi8 j hj
    have hterm : ∀ j' ∈ Finset.range (csG (ρ r')).len,
        (if StkBefore (fun b ↦ csKap kv (grpOf b)) ((csG (ρ r')).b0 + j') b then
          2 ^ csKap kv (grpOf ((csG (ρ r')).b0 + j')) else 0) =
        if csKap kv gi < csKap kv (ρ r') ∨ (csKap kv (ρ r') = csKap kv gi ∧ (csG (ρ r')).b0 + j' < b)
        then 2 ^ csKap kv (ρ r') else 0 := fun j' hj' ↦ by
      simp only [StkBefore, hblk j' (Finset.mem_range.1 hj'), hb]
    rw [Finset.sum_congr rfl hterm]
    rcases Nat.lt_trichotomy r' r with hlt | heq | hgt
    · -- an earlier rank: every block before
      have hn := h.anti r' r hlt hr
      rw [csN_lt_iff hgi8 hg'] at hn
      have hall : ∀ j' ∈ Finset.range (csG (ρ r')).len, csKap kv gi < csKap kv (ρ r') ∨
          (csKap kv (ρ r') = csKap kv gi ∧ (csG (ρ r')).b0 + j' < b) := fun j' hj' ↦ by
        rcases hn with hn | ⟨hk, hb0⟩
        · exact Or.inl hn
        · refine Or.inr ⟨hk.symm, ?_⟩
          have := groups_disjoint _ hg' _ hgi8 hb0
          have := Finset.mem_range.1 hj'
          omega
      rw [Finset.sum_congr rfl (g := fun _ ↦ 2 ^ csKap kv (ρ r')) fun j' hj' ↦ by
        simp only [hall j' hj', ↓reduceIte]]
      simp [hlt, csSize]
    · -- the same rank: the blocks before `b0 + j`
      subst heq
      rw [← hgi]
      simp only [lt_irrefl, ↓reduceIte, false_or, true_and]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
      congr 1
      rw [show (Finset.range (csG gi).len).filter (fun j' ↦ (csG gi).b0 + j' < b) = Finset.range j by
        ext j'; simp only [Finset.mem_filter, Finset.mem_range, b]; omega]
      simp
    · -- a later rank: no block before
      have hn := h.anti r r' hgt hr'8
      rw [csN_lt_iff hg' hgi8] at hn
      simp only [show ¬ r' < r by omega, show r' ≠ r by omega, ↓reduceIte]
      refine Finset.sum_eq_zero fun j' hj' ↦ ?_
      have hno : ¬ (csKap kv gi < csKap kv (ρ r') ∨
          (csKap kv (ρ r') = csKap kv gi ∧ (csG (ρ r')).b0 + j' < b)) := by
        rcases hn with hn | ⟨hk, hb0⟩
        · omega
        · have := groups_disjoint _ hgi8 _ hg' hb0
          have := Finset.mem_range.1 hj'
          omega
      simp only [hno, ↓reduceIte]
  rw [Finset.sum_congr rfl inner, sum_rank_split _ _ hr]
  rfl

end
end LeanVM.Guest.B1.Stack
