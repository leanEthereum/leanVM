module

public import NativeVm.Equiv.Form
public import NativeVm.Equiv.Field

/-!
# Forms: the model's operations are the statement's

Through `FormW.toForm` (`NativeVm/Equiv/Form.lean`): `FormW.const` is `Form.const`, `FormW.addTerm`
(a search by `findIdx?`, then `modify` or `push`) is the statement's recursive `addTerm`
(`toForm_addTerm`), `FormW.addScaled` is `Form.addScaled` (`toForm_addScaled`), and
`FormW.evaluate` on a row of words is `Form.evaluate` on the row's values, a missing column `0`
(`toE_evaluate`).
-/

@[expose] public section

namespace NativeVm.Model

open NativeVm.Equiv LeanVM.Parameters LeanVM.Protocol

@[simp] theorem FormW.toForm_terms (f : FormW) : f.toForm.terms = f.toList.map TermW.toSpec := rfl

@[simp] theorem FormW.toForm_const (v : EW) : (FormW.const v).toForm = Verifier.Form.const v.toE :=
  rfl

theorem TermW.cols_beq_iff (t : TermW) (m : Array ℕ) :
    (t.cols == m) = true ↔ t.toSpec.1 = m.toList := by
  simp [TermW.toSpec, Array.toList_inj]

/-- `FormW.addTerm` on the terms' list. -/
private theorem addTerm_list (l : List TermW) (m : Array ℕ) (c : EW) :
    ((match l.findIdx? (fun t : TermW ↦ t.cols == m) with
      | some i => l.modify i fun t ↦ { t with coeff := t.coeff + c }
      | none => l ++ [(⟨m, 0 + c⟩ : TermW)]).map TermW.toSpec) =
      Verifier.addTerm (l.map TermW.toSpec) m.toList c.toE := by
  induction l with
  | nil => simp [Verifier.addTerm, TermW.toSpec]
  | cons t l ih =>
    rcases t with ⟨tc, tk⟩
    rw [List.findIdx?_cons]
    by_cases h : tc = m
    · subst h
      simp [TermW.toSpec, Verifier.addTerm]
    · have hb : (tc == m) = false := by simpa using h
      have h' : tc.toList ≠ m.toList := by simpa [Array.toList_inj] using h
      simp only [hb, Bool.false_eq_true, ↓reduceIte, List.map_cons, TermW.toSpec, Verifier.addTerm,
        h']
      revert ih
      rcases List.findIdx? (fun x : TermW ↦ x.cols == m) l with _ | i <;> intro ih
      · simpa [TermW.toSpec] using ih
      · simpa [List.modify_succ_cons, TermW.toSpec] using ih

theorem FormW.toForm_addTerm (f : FormW) (m : Array ℕ) (c : EW) :
    (FormW.addTerm f m c).toForm.terms = Verifier.addTerm f.toForm.terms m.toList c.toE := by
  rcases f with ⟨l⟩
  simp only [FormW.toForm_terms]
  rw [← addTerm_list]
  unfold FormW.addTerm
  simp only [List.findIdx?_toArray]
  rcases List.findIdx? (fun x : TermW ↦ x.cols == m) l with _ | i <;> simp

theorem FormW.toForm_addScaled (f other : FormW) (w : EW) :
    (f.addScaled other w).toForm = f.toForm.addScaled other.toForm w.toE := by
  simp only [FormW.toForm, Verifier.Form.addScaled, FormW.addScaled]
  congr 1
  rw [List.foldl_map, ← Array.foldl_toList]
  refine (List.foldl_hom (fun g : FormW ↦ g.toList.map TermW.toSpec) ?_).symm
  intro g t
  have := FormW.toForm_addTerm g t.cols (w * t.coeff)
  simp only [FormW.toForm_terms, EW.toE_mul] at this
  simp [TermW.toSpec, this]

/-- A monomial's product on a row of words. -/
theorem foldl_cols (cols : List ℕ) (row : Array EW) (c : EW) :
    (cols.foldl (fun acc i ↦ acc * row.getD i 0) c).toE =
      cols.foldl (fun acc i ↦ acc * (row.toList.map EW.toE).getD i 0) c.toE := by
  induction cols generalizing c with
  | nil => rfl
  | cons i cols ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 2
    rw [EW.toE_mul, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
      Array.getElem?_toList]
    rcases row[i]? <;> simp

theorem FormW.toE_evaluate (f : FormW) (row : Array EW) :
    (f.evaluate row).toE = f.toForm.evaluate fun i ↦ (row.toList.map EW.toE).getD i 0 := by
  unfold FormW.evaluate Verifier.Form.evaluate
  rw [toE_sumE, FormW.toForm_terms, Array.toList_map, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  simp only [Function.comp_apply, TermW.toSpec, ← Array.foldl_toList]
  exact foldl_cols _ _ _

end NativeVm.Model
