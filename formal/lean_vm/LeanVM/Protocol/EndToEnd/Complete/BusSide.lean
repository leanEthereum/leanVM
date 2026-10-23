/-
  LeanVM.Protocol.EndToEnd.Complete.BusSide

  One side of the verifier program's leaf decomposition, read algebraically: the Python's bus
  layout places its blocks where `stackLeaves` does, its selectors are the blocks' selectors, the
  forms it accumulates evaluate to the selector-weighted fingerprints of the blocks, and the
  side's total is the tree value plus the framework and the padding.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusStack
public import LeanVM.Protocol.EndToEnd.Complete.Facts
public import LeanVM.Protocol.Verifier

/-!
# One side of the leaf decomposition

`accumulateSide` (`python-verifier/verifier.py:589-604` at leanVM
`3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45`) takes a side's GKR value and its layout
(`bus_layout`, `verifier.py:514-519`) and returns the forms with the side's table blocks added and
the side's total. This module states what it computes:

* `busLayout_framework`, `busLayout_tables`, `busLayout_depth`: the layout's selectors at a point
  are the blocks' selectors `blockSel` (`Placement.eq_above` at an aligned placement), and its
  depth is the ceiling logarithm of the blocks' total;
* `evaluate_addScaled`: `Form.add_scaled` adds the scaled form's value;
* `accFold_spec`: each table's form for the side evaluates, at any row, to its value before plus
  `Σ_b sel_b · blockVal_b(row)` over the side's blocks the table owns, where `blockVal` is
  `β + Σ_slot w_slot · coordinate_slot(row)`, the value of the block's form (`blockForm`); the
  other sides are untouched;
* `padSum`: the padding term the side's total adds, `Σ_b sel_b · pad_{rows_b} · (blockVal_b(p) +
  1)` at the owner's padding row `p`.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete Finset

@[expose] public section

/-! ## The layout -/

/-- The sizes of a side: the framework's, then the blocks'. -/
def sideSizes (fw : List ℕ) (blocks : List BusBlock) : List ℕ := fw ++ blocks.map (·.logRows)

theorem length_stackOffsets (sizes : List ℕ) : (stackOffsets sizes).1.length = sizes.length := by
  rw [stackOffsets_eq]
  simp [placeFold_length]

/-- The placement `bus_layout` gives block `b`. -/
theorem getElem_busPlacements (sizes : List ℕ) (b : ℕ) (hb : b < sizes.length) :
    (List.zipWith (fun size offset ↦ ({ vars := size, index := offset } : Placement)) sizes
      (stackOffsets sizes).1)[b]'(by simp [length_stackOffsets, hb]) =
      { vars := sizes.getD b 0, index := blockOffset sizes b } := by
  simp only [List.getElem_zipWith, blockOffset]
  rw [List.getD_eq_getElem _ _ hb, List.getD_eq_getElem _ _ (by rw [length_stackOffsets]; exact hb)]

/-- An aligned placement's `eq_above` is the block's selector. -/
theorem eqAbove_aligned (v o : ℕ) (p : List E) :
    ({ vars := v, index := o } : Placement).eqAbove p =
      eqEval (boolPoint (p.length - v) (o / 2 ^ v)) (p.drop v) := by
  simp [Placement.eqAbove, selectorPoint_eq_boolPoint, Nat.shiftRight_eq_div_pow]

/-- The framework's selectors. -/
theorem busLayout_framework (fw : List ℕ) (blocks : List BusBlock) (p : List E) :
    (busLayout fw blocks).framework.map (·.eqAbove p) =
      (List.range fw.length).map fun b ↦ blockSel (sideSizes fw blocks) p.length b p := by
  apply List.ext_getElem
  · simp [busLayout, length_stackOffsets]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [busLayout, List.getElem_map, List.getElem_take, List.getElem_range]
    rw [getElem_busPlacements _ _ (by simp; omega), eqAbove_aligned]
    rfl

/-- The table blocks' selectors. -/
theorem busLayout_tables (fw : List ℕ) (blocks : List BusBlock) (p : List E) :
    (busLayout fw blocks).tables.map (·.eqAbove p) =
      (List.range blocks.length).map fun i ↦
        blockSel (sideSizes fw blocks) p.length (fw.length + i) p := by
  apply List.ext_getElem
  · simp [busLayout, length_stackOffsets]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [busLayout, List.getElem_map, List.getElem_drop, List.getElem_range]
    rw [getElem_busPlacements _ _ (by simp; omega), eqAbove_aligned]
    rfl

/-- The layout's depth is the ceiling logarithm of the blocks' total. -/
theorem busLayout_depth (fw : List ℕ) (blocks : List BusBlock) :
    (busLayout fw blocks).depth = log2Ceil (blockTotal (sideSizes fw blocks)) := by
  simp only [busLayout]
  rw [stackOffsets_eq]
  simp only [placeFold_snd, zero_add, blockTotal]
  congr 1
  exact ((perm_stackOrder _).map _).sum_eq

/-- The blocks fit in the cube of the ceiling logarithm of their total. -/
theorem blockTotal_le (sizes : List ℕ) : blockTotal sizes ≤ 2 ^ log2Ceil (blockTotal sizes) := by
  rw [log2Ceil_eq_clog]
  exact Nat.le_pow_clog (by norm_num) _

/-! ## Forms -/

/-- The value of a monomial with its coefficient. -/
theorem foldl_mul_col (col : ℕ → E) : ∀ (m : List ℕ) (c : E),
    m.foldl (fun acc i ↦ acc * col i) c = c * (m.map col).prod
  | [], c => by simp
  | i :: m, c => by rw [List.foldl_cons, foldl_mul_col col m, List.map_cons, List.prod_cons]; ring

/-- A form's value is the sum of its monomials' values. -/
theorem evaluate_eq_sum (f : Form) (col : ℕ → E) :
    f.evaluate col = (f.terms.map fun t ↦ t.2 * (t.1.map col).prod).sum := by
  rw [Form.evaluate, sumE_eq]
  exact congrArg List.sum (List.map_congr_left fun t _ ↦ foldl_mul_col col t.1 t.2)

theorem sum_addTerm (col : ℕ → E) : ∀ (terms : List (List ℕ × E)) (m : List ℕ) (c : E),
    ((addTerm terms m c).map fun t ↦ t.2 * (t.1.map col).prod).sum =
      (terms.map fun t ↦ t.2 * (t.1.map col).prod).sum + c * (m.map col).prod
  | [], m, c => by simp [addTerm]
  | (m', c') :: rest, m, c => by
    unfold addTerm
    split_ifs with h
    · subst h; simp; ring
    · simp only [List.map_cons, List.sum_cons, sum_addTerm col rest]; ring

/-- **`Form.add_scaled` adds the scaled form's value.** -/
theorem evaluate_addScaled (f g : Form) (w : E) (col : ℕ → E) :
    (f.addScaled g w).evaluate col = f.evaluate col + w * g.evaluate col := by
  rw [evaluate_eq_sum, evaluate_eq_sum, evaluate_eq_sum, Form.addScaled]
  simp only
  generalize f.terms = acc
  induction g.terms generalizing acc with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, sum_addTerm, List.map_cons, List.sum_cons]
    ring

@[simp] theorem evaluate_const (c : E) (col : ℕ → E) : (Form.const c).evaluate col = c := by
  simp [evaluate_eq_sum, Form.const]

@[simp] theorem evaluate_empty (col : ℕ → E) : ({} : Form).evaluate col = 0 := by
  simp [evaluate_eq_sum]

/-- Monomials of degree at most two. -/
def Deg2 (f : Form) : Prop := ∀ t ∈ f.terms, t.1.length ≤ 2

theorem deg2_addTerm : ∀ (terms : List (List ℕ × E)) (m : List ℕ) (c : E),
    (∀ t ∈ terms, t.1.length ≤ 2) → m.length ≤ 2 → ∀ t ∈ addTerm terms m c, t.1.length ≤ 2
  | [], m, c, _, hm => by simp [addTerm, hm]
  | (m', c') :: rest, m, c, h, hm => by
    unfold addTerm
    split_ifs
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact h (m', c') List.mem_cons_self
      · exact h t (by simp [ht])
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact h _ (by simp)
      · exact deg2_addTerm rest m c (fun t' ht' ↦ h t' (by simp [ht'])) hm t ht

theorem deg2_foldl_addTerm (w : E) : ∀ (ts acc : List (List ℕ × E)),
    (∀ t ∈ acc, t.1.length ≤ 2) → (∀ t ∈ ts, t.1.length ≤ 2) →
      ∀ t ∈ ts.foldl (fun acc t ↦ addTerm acc t.1 (w * t.2)) acc, t.1.length ≤ 2
  | [], _, hacc, _ => hacc
  | t :: ts, acc, hacc, hts => by
    rw [List.foldl_cons]
    exact deg2_foldl_addTerm w ts _ (deg2_addTerm acc t.1 _ hacc (hts t (by simp)))
      fun t' ht' ↦ hts t' (by simp [ht'])

theorem deg2_addScaled {f g : Form} (hf : Deg2 f) (hg : Deg2 g) (w : E) :
    Deg2 (f.addScaled g w) :=
  deg2_foldl_addTerm w g.terms f.terms hf hg

theorem deg2_const (c : E) : Deg2 (Form.const c) := by simp [Deg2, Form.const]

/-! ## Accumulating a side -/

/-- `List.modify` read back at an index. -/
theorem getD_modify {α : Type} (l : List α) (i j : ℕ) (f : α → α) (d : α) :
    (l.modify i f).getD j d = if i = j ∧ j < l.length then f (l.getD j d) else l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases hj : j < l.length
  · rw [List.getElem?_eq_getElem hj]
    by_cases hij : i = j <;> simp [hij, hj]
  · rw [List.getElem?_eq_none (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-- A block's fingerprint at a row, with the side's challenge: `β + Σ_slot w_slot ·
coordinate_slot(row)`. -/
def blockVal (β : E) (w : List E) (b : BusBlock) (col : ℕ → E) : E :=
  β + (b.coordinates.zipIdx.map fun cs ↦ w.getD cs.2 0 * cs.1.evaluate col).sum

/-- The weighted coordinates' fold adds their weighted values. -/
theorem evaluate_foldl_coords' (w : List E) (col : ℕ → E) :
    ∀ (l : List (Form × ℕ)) (init : Form),
      (l.foldl (fun form (cs : Form × ℕ) ↦ form.addScaled cs.1 (w.getD cs.2 0)) init).evaluate
          col =
        init.evaluate col + (l.map fun cs ↦ w.getD cs.2 0 * cs.1.evaluate col).sum
  | [], init => by simp
  | cs :: l, init => by
    rw [List.foldl_cons, evaluate_foldl_coords' w col l, evaluate_addScaled]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem deg2_foldl_coords' (w : List E) :
    ∀ (l : List (Form × ℕ)) (init : Form), Deg2 init → (∀ cs ∈ l, Deg2 cs.1) →
      Deg2 (l.foldl (fun form (cs : Form × ℕ) ↦ form.addScaled cs.1 (w.getD cs.2 0)) init)
  | [], init, h, _ => h
  | cs :: l, init, h, hl => by
    rw [List.foldl_cons]
    exact deg2_foldl_coords' w l _ (deg2_addScaled h (hl cs (by simp)) _)
      fun cs' h' ↦ hl cs' (by simp [h'])

/-- A block's form (`blockForm`, `verifier.py:596-598`) evaluates to its fingerprint with the
side's challenge. -/
theorem evaluate_blockForm (b : BusBlock) (w : List E) (β : E) (col : ℕ → E) :
    (blockForm b w β).evaluate col = blockVal β w b col :=
  (evaluate_foldl_coords' w col b.coordinates.zipIdx (Form.const β)).trans (by
    rw [evaluate_const, blockVal])

/-- A block's form has degree at most two when its coordinates do. -/
theorem deg2_blockForm (b : BusBlock) (w : List E) (β : E) (h : ∀ c ∈ b.coordinates, Deg2 c) :
    Deg2 (blockForm b w β) :=
  deg2_foldl_coords' w b.coordinates.zipIdx (Form.const β) (deg2_const β)
    fun cs hcs ↦ h cs.1 (List.fst_mem_of_mem_zipIdx hcs)

/-- The fold of `accumulateSide` over a side's blocks: each block's form added to its owner's form
of the side, at its selector. -/
def accFold (side : ℕ) (sideWeights : List E) (sideBeta : E) (l : List (E × BusBlock))
    (forms : List (List Form)) : List (List Form) :=
  l.foldl (fun forms (selector, block) ↦
    forms.modify block.owner fun row ↦ row.modify side fun f ↦
      f.addScaled (blockForm block sideWeights sideBeta) selector) forms

/-- The padding term of `accumulateSide` (`padding_rows`, `verifier.py:594-601`): each block's
selector, times the padding weight of its owner's rows, times its form at the padding row plus
one. -/
def padSum (sideWeights : List E) (sideBeta : E) (point : List E) (l : List (E × BusBlock)) : E :=
  (l.map fun x ↦ x.1 * paddingWeight (point.take x.2.logRows) x.2.rows *
    (blockVal sideBeta sideWeights x.2 ((tables.getD x.2.owner default).padding.getD · 0) + 1)).sum

/-- The invariant the fold keeps: the forms' shape, the other sides, the side's values. -/
theorem accFold_spec (side : ℕ) (hside : side < 3) (w : List E) (β : E) :
    ∀ (l : List (E × BusBlock)) (forms : List (List Form)), forms.length = 6 →
      (∀ t < 6, (forms.getD t []).length = 3) → (∀ x ∈ l, x.2.owner < 6) →
      (accFold side w β l forms).length = 6 ∧
      (∀ t < 6, ((accFold side w β l forms).getD t []).length = 3) ∧
      (∀ t side', side' ≠ side →
        ((accFold side w β l forms).getD t []).getD side' {} = (forms.getD t []).getD side' {}) ∧
      (∀ (t : ℕ) (col : ℕ → E),
        (((accFold side w β l forms).getD t []).getD side {}).evaluate col =
          ((forms.getD t []).getD side {}).evaluate col +
            ((l.filter fun x ↦ x.2.owner = t).map fun x ↦ x.1 * blockVal β w x.2 col).sum)
  | [], forms, h6, h3, _ => ⟨h6, h3, fun _ _ _ ↦ rfl, fun _ _ ↦ by simp [accFold]⟩
  | (sel, b) :: l, forms, h6, h3, hl => by
    have hb : b.owner < 6 := hl (sel, b) (by simp)
    set forms' := forms.modify b.owner fun row ↦ row.modify side fun f ↦
      f.addScaled (blockForm b w β) sel
    have hstep : accFold side w β ((sel, b) :: l) forms = accFold side w β l forms' := rfl
    have h6' : forms'.length = 6 := by simp [forms', h6]
    have hrow : ∀ t, (forms'.getD t []) = if b.owner = t ∧ t < forms.length then
        (forms.getD t []).modify side (fun f ↦ f.addScaled (blockForm b w β) sel)
        else forms.getD t [] := fun t ↦
      getD_modify _ _ _ _ _
    have h3' : ∀ t < 6, (forms'.getD t []).length = 3 := by
      intro t ht
      rw [hrow]; split_ifs <;> simp only [List.length_modify, h3 t ht]
    obtain ⟨r1, r2, r3, r4⟩ := accFold_spec side hside w β l forms' h6' h3'
      fun x hx ↦ hl x (by simp [hx])
    refine ⟨by rw [hstep]; exact r1, by rw [hstep]; exact r2, fun t side' hs ↦ ?_,
      fun t col ↦ ?_⟩
    · rw [hstep, r3 t side' hs, hrow]
      split_ifs
      · rw [getD_modify]; simp [Ne.symm hs]
      · rfl
    · rw [hstep, r4 t col, hrow]
      simp only [List.filter_cons]
      by_cases hbt : b.owner = t
      · subst hbt
        have hlt : b.owner < forms.length := by omega
        simp only [hlt, and_self, ↓reduceIte, decide_true, List.map_cons, List.sum_cons]
        rw [getD_modify, h3 _ hb]
        simp only [hside, and_self, ↓reduceIte]
        rw [evaluate_addScaled, evaluate_blockForm]
        ring
      · simp [hbt]

/-- The fold keeps every form of degree at most two when the blocks' coordinates are. -/
theorem accFold_deg2 (side : ℕ) (w : List E) (β : E) :
    ∀ (l : List (E × BusBlock)) (forms : List (List Form)), FormsDeg2 forms →
      (∀ x ∈ l, ∀ c ∈ x.2.coordinates, Deg2 c) → FormsDeg2 (accFold side w β l forms)
  | [], _, h, _ => h
  | (sel, b) :: l, forms, h, hl => by
    refine accFold_deg2 side w β l _ ?_ fun x hx ↦ hl x (by simp [hx])
    intro t side' term hterm
    rw [getD_modify] at hterm
    split_ifs at hterm with h1
    · rw [getD_modify] at hterm
      split_ifs at hterm with h2
      · refine deg2_addScaled ?_ (deg2_blockForm b w β fun c hc ↦ hl (sel, b) (by simp) c hc) sel
          term hterm
        exact fun term' ht' ↦ h t side' term' (h2.1 ▸ ht')
      · exact h t side' term hterm
    · exact h t side' term hterm

end
end LeanVM.Protocol.EndToEnd.Complete
