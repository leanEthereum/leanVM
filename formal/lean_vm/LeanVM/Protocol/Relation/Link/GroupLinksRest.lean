/-
  LeanVM.Protocol.Relation.Link.GroupLinksRest

  The drawn group's polynomial split into the state link's part and the rest (the program and the
  memory), and the stack's values at an executed row as the row side reads them.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksCollapse
public import LeanVM.Protocol.Relation.Link.GroupLinksTables
public import LeanVM.Protocol.Relation.Link.GroupLinksPos

/-!
# The state part and the rest

`lk_groupF_split`: for one-hot pointers, `groupF v = indexClaim − lkStatePart v − lkRest v`, where
`lkStatePart` sums the cycle pointers' shares (pointer column `0`) over the executed rows and
`lkRest` the base terms and the other pointer columns' shares (`lk_linkIdx_closed`).
`lkVals_bool`: at an executed row, the row side reads a non-pointer column's value off the stack
(`tableValue`); `form_evaluate_congr`: a form's value depends on its columns alone.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-- The cycle pointers' shares over the executed rows. -/
def lkStatePart (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ)
    (v : Fin (linkDrawn layout chunks + 1) → E) : E :=
  ∑ t ∈ range nTables, ∑ u ∈ range (tableRowCount layout t),
    lkPtrC layout chunks q (chV layout chunks v) (boolL (linkRows layout) u)
      (honestValues layout q (boolL (linkRows layout) u)) (ptrIndex chunks (wordAt layout q t 0 u)) t 0

/-- The base terms and the program and memory pointers' shares over the executed rows. -/
def lkRest (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ)
    (v : Fin (linkDrawn layout chunks + 1) → E) : E :=
  ∑ t ∈ range nTables, ∑ u ∈ range (tableRowCount layout t),
    (lkBaseC layout (chV layout chunks v) (boolL (linkRows layout) u)
        (honestValues layout q (boolL (linkRows layout) u)) t +
      ∑ k ∈ Ico 1 (ptrsOf layout t).length, lkPtrC layout chunks q (chV layout chunks v)
        (boolL (linkRows layout) u) (honestValues layout q (boolL (linkRows layout) u))
        (ptrIndex chunks (wordAt layout q t k u)) t k)

theorem ptrsOf_eq {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {t : ℕ} (ht : t < nTables) : ptrsOf layout t = (tables.getD t default).links.pointers := by
  have hT := (announced_facts hA).2.1
  unfold ptrsOf
  rw [hT, List.getD_eq_getElem _ _ (by simp [tables_length, ht]), List.getElem_map,
    List.getD_eq_getElem _ _ (by simp [tables_length, ht])]

theorem two_le_ptrsOf {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {t : ℕ} (ht : t < nTables) : 2 ≤ (ptrsOf layout t).length := by
  have h := congrArg List.length (lkt_pointers t ht).1
  rw [ptrsOf_eq hA ht]
  simp only [List.length_take, List.length_cons, List.length_nil] at h
  omega

/-- **The drawn group's polynomial, split**: the state link's part and the rest. -/
theorem lk_groupF_split {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
    (hone : PointersOneHot layout q chunks) (v : Fin (linkDrawn layout chunks + 1) → E) :
    groupF layout chunks q v = indexClaim layout chunks (List.ofFn v).tail -
      lkStatePart layout chunks q v - lkRest layout chunks q v := by
  rw [groupF, lk_linkIdx_closed hA q hch hone _ _ (chV_tau_length hch v), sub_sub]
  refine congrArg (fun z ↦ indexClaim layout chunks (List.ofFn v).tail - z) ?_
  rw [lkStatePart, lkRest, ← sum_add_distrib]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun u _ ↦ ?_
  have h2 := two_le_ptrsOf hA (mem_range.mp ht)
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  ring

/-! ## The stack's values at an executed row -/

theorem foldl_mul_congr {g h : ℕ → E} (l : List ℕ) : ∀ (init : E), (∀ i ∈ l, g i = h i) →
    l.foldl (fun acc i ↦ acc * g i) init = l.foldl (fun acc i ↦ acc * h i) init := by
  induction l with
  | nil => intro _ _; simp only [List.foldl_nil]
  | cons i l ih =>
    intro init hl
    simp only [List.foldl_cons]
    rw [hl i (by simp)]
    exact ih _ fun j hj ↦ hl j (by simp [hj])

/-- **A form's value depends on its columns alone.** -/
theorem form_evaluate_congr (f : Form) {g h : ℕ → E} (hgh : ∀ c ∈ lkFormCols f, g c = h c) :
    f.evaluate g = f.evaluate h := by
  unfold Form.evaluate
  refine congrArg sumE (List.map_congr_left fun m hm ↦ ?_)
  exact foldl_mul_congr _ _ fun i hi ↦ hgh i (List.mem_flatMap.mpr ⟨m, hm, hi⟩)

/-- **The row side's values at an executed row**: a non-pointer column's value is the stack's. -/
theorem lkVals_bool (layout : Layout) {μ : ℕ} (q : Column μ) {t : ℕ} (ht : t < layout.tables.length)
    {u : ℕ} (hu : u < 2 ^ heightOf layout t) {c : ℕ} (hc : c < (layout.tables.getD t default).width)
    (hnp : c ∉ ptrsOf layout t) :
    (lkVals layout (honestValues layout q (boolL (linkRows layout) u)) t).getD c 0 =
      tableValue layout q t c u := by
  rw [← lkVals_honest layout q _ []]
  have hs := sent_honest layout q (boolL (linkRows layout) u) [] ht
  have hmem : c ∈ nonPointerOf layout t (layout.tables.getD t default) := by
    unfold nonPointerOf
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hc, ?_⟩
    simpa [ptrsOf] using hnp
  show (valuesOf layout ((rowStart layout (honestMessage layout q (boolL (linkRows layout) u) [])).sent.drop
    (sentBefore layout t)) (layout.tables.getD t default, t)).getD c 0 = _
  rw [valuesOf_getD layout _ (layout.tables.getD t default, t) _ (by rw [hs, chunkOf]) hmem,
    take_boolL (heightOf_le layout t), Nat.mod_eq_of_lt hu, rowMle_boolL hu]
  rfl

end

end LeanVM.Protocol.Relation

/-- info: 'LeanVM.Protocol.Relation.lk_groupF_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lk_groupF_split

/-- info: 'LeanVM.Protocol.Relation.lkVals_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lkVals_bool
