/-
  LeanVM.Guest.B1.Tables.VerifyTablesForms

  The specification's forms as values: evaluation is linear in `addScaled`, so the forms the bus
  leaves each table are sums over its blocks.
-/

module

public import LeanVM.Guest.B1.Tables.TCtx

/-!
# Forms as values (V:467-489, 589-604)

`Form.evaluate` is linear: adding a scaled form adds its scaled value (`evaluate_addScaled`),
whatever monomials merge. So a block's form is the side's `beta` plus its coordinates weighted
(`evaluate_blockForm`), and the forms `accumulateSide` leaves a table on a side are the
selector-weighted sum of its blocks' forms (`accumulateSide_forms`), the padding mass beside them
(`accumulateSide_padding`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Sums -/

theorem vt_foldl_add (l : List E) (a : E) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons]; rw [ih (a + x), ih (0 + x)]; ring

theorem vt_sumE_nil : sumE [] = 0 := rfl

theorem vt_sumE_cons (x : E) (l : List E) : sumE (x :: l) = x + sumE l := by
  simp only [sumE, List.foldl_cons]; rw [vt_foldl_add]; ring

theorem vt_sumE_append (l l' : List E) : sumE (l ++ l') = sumE l + sumE l' := by
  induction l with
  | nil => simp [vt_sumE_nil]
  | cons x l ih => rw [List.cons_append, vt_sumE_cons, vt_sumE_cons, ih]; ring

theorem vt_sumE_map_mul {α : Type} (f : α → E) (w : E) (l : List α) :
    sumE (l.map fun a => w * f a) = w * sumE (l.map f) := by
  induction l with
  | nil => simp [vt_sumE_nil]
  | cons x l ih => simp only [List.map_cons, vt_sumE_cons, ih]; ring

theorem vt_sumE_map_add {α : Type} (f g : α → E) (l : List α) :
    sumE (l.map fun a => f a + g a) = sumE (l.map f) + sumE (l.map g) := by
  induction l with
  | nil => simp [vt_sumE_nil]
  | cons x l ih => simp only [List.map_cons, vt_sumE_cons, ih]; ring

/-! ## Evaluation -/

/-- A term's value: its coefficient times its columns. -/
def termVal (column : ℕ → E) (t : List ℕ × E) : E := t.1.foldl (fun acc i ↦ acc * column i) t.2

theorem foldl_mul_col (column : ℕ → E) (m : List ℕ) (c : E) :
    m.foldl (fun acc i ↦ acc * column i) c = c * m.foldl (fun acc i ↦ acc * column i) 1 := by
  induction m generalizing c with
  | nil => simp
  | cons i m ih => simp only [List.foldl_cons]; rw [ih (c * column i), ih (1 * column i)]; ring

theorem termVal_coef (column : ℕ → E) (m : List ℕ) (c : E) :
    termVal column (m, c) = c * termVal column (m, 1) := foldl_mul_col column m c

theorem evaluate_eq (f : Form) (column : ℕ → E) :
    f.evaluate column = sumE (f.terms.map (termVal column)) := rfl

theorem sum_addTerm (column : ℕ → E) (ts : List (List ℕ × E)) (m : List ℕ) (c : E) :
    sumE ((addTerm ts m c).map (termVal column)) =
      sumE (ts.map (termVal column)) + termVal column (m, c) := by
  induction ts with
  | nil =>
    simp only [addTerm, List.map_cons, List.map_nil, vt_sumE_cons, vt_sumE_nil, zero_add, add_zero]
  | cons t ts ih =>
    obtain ⟨m', c'⟩ := t
    simp only [addTerm]
    split_ifs with h
    · subst h
      simp only [List.map_cons, vt_sumE_cons]
      rw [termVal_coef, termVal_coef column m' c', termVal_coef column m' c]; ring
    · simp only [List.map_cons, vt_sumE_cons, ih]; ring

theorem evaluate_addScaled (f g : Form) (w : E) (column : ℕ → E) :
    (f.addScaled g w).evaluate column = f.evaluate column + w * g.evaluate column := by
  simp only [Form.addScaled, evaluate_eq]
  suffices h : ∀ (ts acc : List (List ℕ × E)),
      sumE ((ts.foldl (fun acc t ↦ addTerm acc t.1 (w * t.2)) acc).map (termVal column)) =
        sumE (acc.map (termVal column)) + w * sumE (ts.map (termVal column)) from h _ _
  intro ts
  induction ts with
  | nil => intro acc; simp [vt_sumE_nil]
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons, ih, sum_addTerm, List.map_cons, vt_sumE_cons]
    rw [termVal_coef column t.1 (w * t.2), termVal_coef column t.1 t.2]; ring

theorem evaluate_const (v : E) (column : ℕ → E) : (Form.const v).evaluate column = v := by
  simp [Form.const, evaluate_eq, termVal, vt_sumE_cons, vt_sumE_nil]

theorem evaluate_empty (column : ℕ → E) : ({} : Form).evaluate column = 0 := rfl

/-- **A block's form**: the side's `beta` plus each coordinate weighted by its slot's weight. -/
theorem evaluate_blockForm (block : BusBlock) (w : List E) (beta : E) (column : ℕ → E) :
    (blockForm block w beta).evaluate column =
      beta + sumE (block.coordinates.zipIdx.map fun p ↦ w.getD p.2 0 * p.1.evaluate column) := by
  unfold blockForm
  suffices h : ∀ (l : List (Form × ℕ)) (f : Form),
      (l.foldl (fun form (coordinate, slot) ↦ form.addScaled coordinate (w.getD slot 0)) f).evaluate
        column = f.evaluate column + sumE (l.map fun p ↦ w.getD p.2 0 * p.1.evaluate column) by
    rw [h, evaluate_const]
  intro l
  induction l with
  | nil => intro f; simp [vt_sumE_nil]
  | cons p l ih =>
    intro f
    simp only [List.foldl_cons, ih, evaluate_addScaled, List.map_cons, vt_sumE_cons]; ring

/-! ## The forms a side leaves -/

/-- The form of table `t` on side `s`. -/
def formAt (forms : List (List Form)) (t s : ℕ) : Form := (forms.getD t default).getD s {}

/-- Six tables of three sides. -/
def FormsShaped (forms : List (List Form)) : Prop :=
  forms.length = 6 ∧ ∀ t < 6, (forms.getD t default).length = 3

/-- One step of `accumulateSide`'s fold (V:597-602). -/
def accStep (side : ℕ) (sideWeights : List E) (sideBeta : E) (point : List E)
    (acc : List (List Form) × E) (p : E × BusBlock) : List (List Form) × E :=
  let form := blockForm p.2 sideWeights sideBeta
  let padding := (tables.getD p.2.owner default).padding
  (acc.1.modify p.2.owner fun row ↦ row.modify side fun f ↦ f.addScaled form p.1,
    acc.2 + p.1 * paddingWeight (point.take p.2.logRows) p.2.rows *
      (form.evaluate (padding.getD · 0) + 1))

theorem accumulateSide_eq (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sideLayout : BusLayout) (fps sideWeights : List E) (sideBeta : E) (point : List E)
    (treeValue : E) :
    accumulateSide forms side blocks sideLayout fps sideWeights sideBeta point treeValue =
      let frameworkSelectors := sideLayout.framework.map (·.eqAbove point)
      let tableSelectors := sideLayout.tables.map (·.eqAbove point)
      let r := (List.zip tableSelectors blocks).foldl (accStep side sideWeights sideBeta point)
        (forms, 0)
      (r.1, treeValue + dot frameworkSelectors (fps.map (sideBeta + ·)) +
        (sumE (frameworkSelectors ++ tableSelectors) + 1) + r.2) := rfl

theorem getD_modify {α : Type} (l : List α) (i j : ℕ) (f : α → α) (d : α) :
    (l.modify i f).getD j d = if i = j ∧ j < l.length then f (l.getD j d) else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases hj : j < l.length
  · rw [List.getElem?_eq_getElem hj]
    by_cases hi : i = j <;> simp [hi, hj]
  · rw [List.getElem?_eq_none (by omega)]
    simp [hj]

theorem formsShaped_step {side : ℕ} {sideWeights : List E} {sideBeta : E} {point : List E}
    {acc : List (List Form) × E} {p : E × BusBlock} (h : FormsShaped acc.1) :
    FormsShaped (accStep side sideWeights sideBeta point acc p).1 := by
  refine ⟨by simp [accStep, h.1], fun t ht => ?_⟩
  simp only [accStep, getD_modify]
  split_ifs
  · simp only [List.length_modify]; exact h.2 t ht
  · exact h.2 t ht

theorem formAt_step {side : ℕ} {sideWeights : List E} {sideBeta : E} {point : List E}
    {acc : List (List Form) × E} {p : E × BusBlock} (h : FormsShaped acc.1) (ho : p.2.owner < 6)
    (hs : side < 3) (t s : ℕ) (column : ℕ → E) :
    (formAt (accStep side sideWeights sideBeta point acc p).1 t s).evaluate column =
      (formAt acc.1 t s).evaluate column +
        if p.2.owner = t ∧ side = s then
          p.1 * (blockForm p.2 sideWeights sideBeta).evaluate column else 0 := by
  simp only [formAt, accStep, getD_modify, h.1]
  by_cases ht : p.2.owner = t
  · subst ht
    simp only [true_and, ho, and_true, ↓reduceIte, getD_modify, h.2 _ ho]
    by_cases hss : side = s
    · subst hss; simp only [and_self, ↓reduceIte, hs, evaluate_addScaled]
    · simp [hss]
  · simp [ht]

/-- **The forms a side leaves**: the form of table `t` on side `s` gains, over the side's blocks
it owns, each block's form weighted by its selector. -/
theorem accStep_fold_forms {side : ℕ} {sideWeights : List E} {sideBeta : E} {point : List E}
    (hs : side < 3) (t s : ℕ) (column : ℕ → E) :
    ∀ (l : List (E × BusBlock)) (acc : List (List Form) × E), FormsShaped acc.1 →
      (∀ p ∈ l, p.2.owner < 6) →
      (formAt (l.foldl (accStep side sideWeights sideBeta point) acc).1 t s).evaluate column =
        (formAt acc.1 t s).evaluate column + sumE (l.map fun p ↦
          if p.2.owner = t ∧ side = s then
            p.1 * (blockForm p.2 sideWeights sideBeta).evaluate column else 0) ∧
      FormsShaped (l.foldl (accStep side sideWeights sideBeta point) acc).1
  | [], acc, h, _ => ⟨by simp [vt_sumE_nil], h⟩
  | p :: l, acc, h, ho => by
    obtain ⟨ih, hsh⟩ := accStep_fold_forms hs t s column l _ (formsShaped_step h)
      (fun q hq => ho q (List.mem_cons_of_mem _ hq))
    refine ⟨?_, hsh⟩
    rw [List.foldl_cons, ih, formAt_step h (ho p (List.mem_cons_self ..)) hs, List.map_cons,
      vt_sumE_cons]
    ring

/-- **The padding mass a side owes**: the selector-weighted padding weight of each block times
its form at the padding row, plus one. -/
theorem accStep_fold_padding {side : ℕ} {sideWeights : List E} {sideBeta : E} {point : List E} :
    ∀ (l : List (E × BusBlock)) (acc : List (List Form) × E),
      (l.foldl (accStep side sideWeights sideBeta point) acc).2 =
        acc.2 + sumE (l.map fun p ↦ p.1 * paddingWeight (point.take p.2.logRows) p.2.rows *
          ((blockForm p.2 sideWeights sideBeta).evaluate
            ((tables.getD p.2.owner default).padding.getD · 0) + 1))
  | [], acc => by simp [vt_sumE_nil]
  | p :: l, acc => by
    rw [List.foldl_cons, accStep_fold_padding l, List.map_cons, vt_sumE_cons]
    simp only [accStep]
    ring

end
end LeanVM.Guest.B1.VerifySub
