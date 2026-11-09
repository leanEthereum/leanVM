/-
  LeanVM.Protocol.EndToEnd.Front.BusForms

  The verifier's degree-two forms (`Form`, a map from monomials to coefficients) as
  values: evaluation is linear in `add_scaled`, and the leaf decomposition's accumulation of a
  side's forms is a sum over the side's blocks.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.BusSpec
public import LeanVM.Protocol.Verifier

/-!
# Forms as values

`Form.evaluate f column` (`crates/verifier/src/layout.rs:38-44` at leanVM `40f877dc`) is the sum
over the form's terms of the coefficient times the product of the monomial's columns. It is linear:

* `Form.evaluate_addScaled`: `evaluate (f.add_scaled(g, w)) = evaluate f + w · evaluate g`, whatever
  the order of the terms (`addTerm` merges a monomial into an existing coefficient or appends
  it);
* `Form.evaluate_empty`, `Form.evaluate_const`, `Form.evaluate_col`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The value of a monomial term at the columns: the coefficient times the columns' product. -/
def termVal (column : ℕ → E) (t : List ℕ × E) : E := t.2 * (t.1.map column).prod

theorem foldl_mul_eq_column (column : ℕ → E) (m : List ℕ) (c : E) :
    m.foldl (fun acc i ↦ acc * column i) c = c * (m.map column).prod := by
  induction m generalizing c with
  | nil => simp
  | cons i m ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- A form's value is the sum of its terms' values. -/
theorem Form.evaluate_eq (f : Form) (column : ℕ → E) :
    f.evaluate column = (f.terms.map (termVal column)).sum := by
  rw [Form.evaluate, sumE_eq_sum]
  congr 1
  exact List.map_congr_left fun t _ ↦ foldl_mul_eq_column column t.1 t.2

/-- Adding a term adds its value. -/
theorem sum_addTerm (column : ℕ → E) (ts : List (List ℕ × E)) (m : List ℕ) (c : E) :
    ((addTerm ts m c).map (termVal column)).sum =
      (ts.map (termVal column)).sum + c * (m.map column).prod := by
  induction ts with
  | nil => simp [addTerm, termVal]
  | cons t ts ih =>
    obtain ⟨m', c'⟩ := t
    by_cases h : m' = m
    · subst h
      simp only [addTerm, ↓reduceIte, List.map_cons, List.sum_cons, termVal]
      ring
    · simp only [addTerm, h, ↓reduceIte, List.map_cons, List.sum_cons, ih]
      ring

/-- **`add_scaled` is linear**: the value of `f + w · g` is `f`'s plus `w` times `g`'s. -/
theorem Form.evaluate_addScaled (f g : Form) (w : E) (column : ℕ → E) :
    (f.addScaled g w).evaluate column = f.evaluate column + w * g.evaluate column := by
  rw [Form.evaluate_eq, Form.evaluate_eq, Form.evaluate_eq, Form.addScaled]
  simp only
  generalize f.terms = acc
  induction g.terms generalizing acc with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, sum_addTerm, List.map_cons, List.sum_cons, termVal]
    ring

@[simp] theorem Form.evaluate_empty (column : ℕ → E) : ({} : Form).evaluate column = 0 := by
  simp [Form.evaluate_eq]

@[simp] theorem Form.evaluate_const (v : E) (column : ℕ → E) :
    (Form.const v).evaluate column = v := by
  simp [Form.evaluate_eq, Form.const, termVal]

/-! ## The leaf decomposition's forms -/

/-- The value of the form of table `t` and side `k` in a table of forms. -/
def formVal (forms : List (List Form)) (t k : ℕ) (column : ℕ → E) : E :=
  ((forms.getD t []).getD k {}).evaluate column

theorem getD_modify {α : Type} (l : List α) (i j : ℕ) (f : α → α) (d : α) (hj : j < l.length) :
    (l.modify i f).getD j d = if i = j then f (l.getD j d) else l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_modify, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj]
  split_ifs <;> simp

/-- A block's contribution to its owner's form on a side: the selector times `β` and the weighted
coordinates. -/
def blockVal (sideWeights : List E) (sideBeta selector : E) (block : BusBlock)
    (column : ℕ → E) : E :=
  selector * sideBeta + (block.coordinates.zipIdx.map fun (coordinate, slot) ↦
    selector * sideWeights.getD slot 0 * coordinate.evaluate column).sum

/-- One block's step of the accumulation. -/
def accStep (side : ℕ) (sideWeights : List E) (sideBeta : E) (forms : List (List Form))
    (sb : E × BusBlock) : List (List Form) :=
  forms.modify sb.2.owner fun row ↦ row.modify side fun form ↦
    sb.2.coordinates.zipIdx.foldl
      (fun form x ↦ form.addScaled x.1 (sb.1 * sideWeights.getD x.2 0))
      (form.addScaled (Form.const sideBeta) sb.1)

end
end LeanVM.Protocol.EndToEnd.Front
