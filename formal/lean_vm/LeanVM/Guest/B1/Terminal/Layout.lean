/-
  LeanVM.Guest.B1.Terminal.Layout

  The layout facts `check_opening_terminal` needs: where `placementsOf` puts a committed column
  and a column with a `q_keccak` slot, and that every offset and size fits the stack.
-/

module

public import LeanVM.Guest.B1.Terminal.InterfaceP
public import LeanVM.Guest.B1.Placement.Kappas

/-!
# The layout

`placementsOf kappas` (V:1128-1140) places the committed columns (`committedCols`, all but the
`KECCAK` columns with a `q_keccak` slot and its output lanes) at `stackOffsets`'s offsets and each
slotted column at `q_keccak`'s offset plus its slot's `2^κ` words (`placement_committed`,
`placement_slot`). Every offset is below
`2^stackLog` (`stackOffsets_lt`), every size at most `stackLog` (`size_le_stackLog`), and every
offset a multiple of its block's `2^κ` (`stackOffsets_dvd`: the blocks lie largest first, the
order `mergeSort` sorts, `List.pairwise_mergeSort`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `KECCAK`'s output lanes are global columns `106 .. 130`. -/
theorem keccakOutputColumns_eq : keccakOutputColumns = (List.range 25).map (106 + ·) := by
  decide +kernel

/-- The `q_keccak` slots of the global columns (`keccakSlot`, V:1105): the input lanes
`81 .. 105` at slots `0 .. 24`, `KECCAK`'s fourteen operand and flag columns `66 .. 79` at slots
`50 .. 63`. -/
def slotOfCol (c : ℕ) : Option ℕ :=
  if 81 ≤ c ∧ c < 106 then some (c - 81) else if 66 ≤ c ∧ c < 80 then some (c - 16) else none

theorem keccakSlot_eq_all :
    (List.range 158).all (fun c ↦ keccakSlot c == slotOfCol c) = true := by
  decide +kernel

theorem keccakSlot_eq {c : ℕ} (hc : c < 158) : keccakSlot c = slotOfCol c := by
  have := List.all_eq_true.mp keccakSlot_eq_all c (List.mem_range.mpr hc)
  simpa using this

/-- Committed column `cc`'s global column: `0 .. 65`, then `KECCAK`'s free column `80`, then its
read counts `131 .. 157`. -/
def colOfCommitted (cc : ℕ) : ℕ := if cc < 66 then cc else if cc = 66 then 80 else cc + 64

theorem committedCols_idxOf_all :
    (List.range Tables.nCommittedCols).all
      (fun cc ↦ (Tables.committedCols 158).idxOf ((Tables.committedCols 158).getD cc 0) == cc) =
      true := by
  rw [Tables.committedCols_158]; decide +kernel

theorem committedCols_idxOf {cc : ℕ} (hcc : cc < Tables.nCommittedCols) :
    (Tables.committedCols 158).idxOf ((Tables.committedCols 158).getD cc 0) = cc := by
  have := List.all_eq_true.mp committedCols_idxOf_all cc (List.mem_range.mpr hcc)
  simpa using this

/-- Committed column `cc`'s global column. -/
theorem committedCols_getD {cc : ℕ} (hcc : cc < Tables.nCommittedCols) :
    (Tables.committedCols 158).getD cc 0 = colOfCommitted cc := by
  have hcc' : cc < 94 := hcc
  have hall : (List.range 94).all (fun c ↦ (Tables.committedCols 158).getD c 0 == colOfCommitted c) =
      true := by
    rw [Tables.committedCols_158]; decide +kernel
  simpa using List.all_eq_true.mp hall cc (List.mem_range.mpr hcc')

theorem colOfCommitted_all :
    (List.range Tables.nCommittedCols).all (fun cc ↦ decide (colOfCommitted cc < 158) &&
      slotOfCol (colOfCommitted cc) == none &&
      decide (colOfCommitted cc ∉ keccakOutputColumns)) = true := by
  rw [keccakOutputColumns_eq]; decide +kernel

theorem colOfCommitted_facts {cc : ℕ} (hcc : cc < Tables.nCommittedCols) :
    colOfCommitted cc < 158 ∧ slotOfCol (colOfCommitted cc) = none ∧
      colOfCommitted cc ∉ keccakOutputColumns := by
  have := List.all_eq_true.mp colOfCommitted_all cc (List.mem_range.mpr hcc)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- The placements, column by column. -/
theorem placementsOf_getD (kappas : List ℕ) {g : ℕ} (hg : g < kappas.length) :
    (placementsOf kappas).1.getD g none =
      match keccakSlot g with
      | some slot => some (Placement.mk (kappas.getD g 0)
          ((stackOffsets (Tables.committedKappas kappas)).1.getD
            ((Tables.committedCols kappas.length).idxOf qkeccak) 0 + slot * 2 ^ kappas.getD g 0))
      | none =>
        if g ∈ keccakOutputColumns then none else some (Placement.mk (kappas.getD g 0)
          ((stackOffsets (Tables.committedKappas kappas)).1.getD
            ((Tables.committedCols kappas.length).idxOf g) 0)) := by
  unfold placementsOf Tables.committedKappas Tables.committedCols
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
    List.getElem?_eq_getElem hg, Option.map_some, Option.getD_some, zero_add]
  rfl

theorem placementsOf_snd (kappas : List ℕ) :
    (placementsOf kappas).2 = max Whir.minLogStack (stackOffsets (Tables.committedKappas kappas)).2 :=
  rfl

/-- **A committed column's placement**: its size and `stackOffsets`'s offset. -/
theorem placement_committed {layout : Layout} {kappas : List ℕ} (hl : kappas.length = 158)
    (hP : layout.placements = (placementsOf kappas).1) {cc : ℕ} (hcc : cc < Tables.nCommittedCols) :
    layout.placement ((Tables.committedCols 158).getD cc 0) =
      Placement.mk ((Tables.committedKappas kappas).getD cc 0)
        ((stackOffsets (Tables.committedKappas kappas)).1.getD cc 0) := by
  have hg := committedCols_getD hcc
  obtain ⟨hglt, hs, ho⟩ := colOfCommitted_facts hcc
  rw [← hg] at hglt hs ho
  rw [Layout.placement, hP, placementsOf_getD _ (by rw [hl]; exact hglt), keccakSlot_eq hglt, hs, hl,
    committedCols_idxOf hcc]
  simp only [ho, ↓reduceIte, Option.getD_some]
  have hlen : cc < (Tables.committedCols 158).length := by
    rw [Tables.committedCols_158_length]; exact hcc
  have e : (Tables.committedKappas kappas).getD cc 0 =
      kappas.getD ((Tables.committedCols 158).getD cc 0) 0 := by
    rw [Tables.committedKappas, hl, List.getD_eq_getElem _ _ (by simpa using hlen),
      List.getElem_map, List.getD_eq_getElem _ _ hlen]
  rw [e]

/-- **A slotted column's placement** (an input lane or a spare slot's column): its size,
`q_keccak`'s offset plus its slot's `2^κ` words. -/
theorem placement_slot {layout : Layout} {kappas : List ℕ} (hl : kappas.length = 158)
    (hP : layout.placements = (placementsOf kappas).1) {g s : ℕ} (hg : g < 158)
    (hs : slotOfCol g = some s) :
    layout.placement g =
      Placement.mk (kappas.getD g 0) ((stackOffsets (Tables.committedKappas kappas)).1.getD 4 0 +
          s * 2 ^ kappas.getD g 0) := by
  have h4 := committedCols_idxOf (cc := 4) (by decide)
  rw [committedCols_getD (by decide)] at h4
  rw [Layout.placement, hP, placementsOf_getD _ (by omega), keccakSlot_eq hg, hs, hl]
  rw [show qkeccak = 4 from rfl, show colOfCommitted 4 = 4 from rfl] at *
  rw [h4]
  rfl

/-! ## Offsets and sizes -/

theorem le_two_pow_log2Ceil (N : ℕ) : N ≤ 2 ^ log2Ceil N := log2Ceil_le_iff.mp le_rfl

/-- The fold of `stackOffsets` keeps every entry `0` or below the running total. -/
theorem stackOffsets_fold (size : ℕ → ℕ) : ∀ (order : List ℕ) (acc : List ℕ × ℕ),
    (∀ i, acc.1.getD i 0 = 0 ∨ acc.1.getD i 0 < acc.2) →
    let r := order.foldl (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i)) acc
    (∀ i, r.1.getD i 0 = 0 ∨ r.1.getD i 0 < r.2) ∧ r.2 = acc.2 + (order.map (2 ^ size ·)).sum
  | [], acc, h => by simpa using h
  | k :: order, acc, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have step : ∀ i, (acc.1.set k acc.2).getD i 0 = 0 ∨
        (acc.1.set k acc.2).getD i 0 < acc.2 + 2 ^ size k := by
      intro i
      rw [List.getD_eq_getElem?_getD, List.getElem?_set]
      split
      · split
        · right; simp only [Option.getD_some]; have := Nat.one_le_two_pow (n := size k); omega
        · left; rfl
      · rw [← List.getD_eq_getElem?_getD]
        rcases h i with h0 | hlt
        · left; exact h0
        · right; exact lt_of_lt_of_le hlt (Nat.le_add_right _ _)
    obtain ⟨h1, h2⟩ := stackOffsets_fold size order (acc.1.set k acc.2, acc.2 + 2 ^ size k) step
    exact ⟨h1, by rw [h2]; ring⟩

/-- **Every offset is below `2^totalLog`.** -/
theorem stackOffsets_lt (sizes : List ℕ) (i : ℕ) :
    (stackOffsets sizes).1.getD i 0 < 2 ^ (stackOffsets sizes).2 := by
  unfold stackOffsets
  obtain ⟨h1, h2⟩ := stackOffsets_fold (fun i ↦ sizes.getD i 0)
    ((List.range sizes.length).mergeSort fun i j ↦ decide (sizes.getD j 0 < sizes.getD i 0) ||
      (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0, 0) (fun i ↦ by
      left; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl)
  simp only at h1 h2 ⊢
  rcases h1 i with h0 | hlt
  · rw [h0]; exact Nat.two_pow_pos _
  · exact lt_of_lt_of_le hlt (le_two_pow_log2Ceil _)

/-- The total `stackOffsets` lays out is the sum of the blocks. -/
theorem stackOffsets_total (sizes : List ℕ) :
    2 ^ (stackOffsets sizes).2 ≥ (sizes.map (2 ^ ·)).sum := by
  unfold stackOffsets
  obtain ⟨-, h2⟩ := stackOffsets_fold (fun i ↦ sizes.getD i 0)
    ((List.range sizes.length).mergeSort fun i j ↦ decide (sizes.getD j 0 < sizes.getD i 0) ||
      (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j)))
    (List.replicate sizes.length 0, 0) (fun i ↦ by
      left; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl)
  simp only at h2 ⊢
  refine le_trans (le_of_eq ?_) (le_two_pow_log2Ceil _)
  rw [h2, zero_add, ((List.mergeSort_perm _ _).map _).sum_eq]
  have : (List.range sizes.length).map (fun i ↦ 2 ^ sizes.getD i 0) = sizes.map (2 ^ ·) := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using h2)]
    rfl
  rw [this]

/-- **Every size is at most the total's log.** -/
theorem size_le_stackOffsets (sizes : List ℕ) {i : ℕ} (hi : i < sizes.length) :
    sizes.getD i 0 ≤ (stackOffsets sizes).2 := by
  have h1 := Tables.tb_single_le_sum_map sizes i hi
  have h2 := stackOffsets_total sizes
  by_contra hc
  have : 2 ^ (stackOffsets sizes).2 < 2 ^ sizes.getD i 0 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega


/-! ## Alignment -/

/-- Along an order of non-increasing sizes, the fold of `stackOffsets` keeps every entry a
multiple of its block's size, and the running total a multiple of every block still to come. -/
theorem stackOffsets_fold_dvd (size : ℕ → ℕ) (le : ℕ → ℕ → Bool)
    (hle : ∀ a b, le a b = true → size b ≤ size a) :
    ∀ (order : List ℕ) (acc : List ℕ × ℕ), order.Pairwise (fun a b ↦ le a b = true) →
      (∀ i, 2 ^ size i ∣ acc.1.getD i 0) → (∀ k ∈ order, 2 ^ size k ∣ acc.2) →
      ∀ i, 2 ^ size i ∣ (order.foldl
        (fun (acc : List ℕ × ℕ) i ↦ (acc.1.set i acc.2, acc.2 + 2 ^ size i)) acc).1.getD i 0
  | [], acc, _, h1, _ => h1
  | k :: order, acc, hp, h1, h2 => by
    rw [List.foldl_cons]
    obtain ⟨hk, hp⟩ := List.pairwise_cons.mp hp
    refine stackOffsets_fold_dvd size le hle order _ hp (fun i ↦ ?_) (fun k' hk' ↦ ?_)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set]
      split
      · rename_i hki
        subst hki
        split
        · exact h2 _ List.mem_cons_self
        · exact dvd_zero _
      · rw [← List.getD_eq_getElem?_getD]; exact h1 i
    · exact dvd_add (h2 k' (List.mem_cons_of_mem _ hk'))
        (Nat.pow_dvd_pow 2 (hle k k' (hk k' hk')))

/-- **Every offset is a multiple of its block's size**: `stackOffsets` lays the blocks out
largest first. -/
theorem stackOffsets_dvd (sizes : List ℕ) (i : ℕ) :
    2 ^ sizes.getD i 0 ∣ (stackOffsets sizes).1.getD i 0 := by
  let le : ℕ → ℕ → Bool := fun i j ↦ decide (sizes.getD j 0 < sizes.getD i 0) ||
    (decide (sizes.getD i 0 = sizes.getD j 0) && decide (i ≤ j))
  have hle : ∀ a b, le a b = true → sizes.getD b 0 ≤ sizes.getD a 0 := by
    intro a b h
    simp only [le, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    omega
  have hs := List.pairwise_mergeSort (le := le)
    (fun a b c h1 h2 ↦ by
      simp only [le, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1 h2 ⊢; omega)
    (fun a b ↦ by
      simp only [le, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]; omega)
    (List.range sizes.length)
  exact stackOffsets_fold_dvd (fun i ↦ sizes.getD i 0) le hle _ _ hs
    (fun i ↦ by
      have h0 : (List.replicate sizes.length 0).getD i 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
      show 2 ^ _ ∣ (List.replicate sizes.length 0).getD i 0
      rw [h0]; exact dvd_zero _)
    (fun _ _ ↦ dvd_zero _) i

end
end LeanVM.Guest.B1.VerifySub
