/-
  LeanVM.Guest.CoreMode.Fam.CarrySplit

  The nonzero facts' check of one function (`Res.carryNzG`) from slices of its body's top-level statements, each its
  own kernel evaluation: for a function alone in its range of `carry.py`, whose check in one evaluation takes more
  memory than a module may.
-/

module

public import LeanVM.Guest.CoreMode.Fam.CarryDefs

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `allB p` over the statements of `ss` from `a` to `b`, in context `ctx`. -/
noncomputable def allBSlice (p : List Ev → Stmt → Bool) (ss : List Stmt) (ctx : List Ev) (a b : ℕ) : Bool :=
  allB p ((ss.drop a).take (b - a)) ctx

theorem allB_append (p : List Ev → Stmt → Bool) (ctx : List Ev) :
    ∀ xs ys : List Stmt, allB p (xs ++ ys) ctx = (allB p xs ctx && allB p ys ctx)
  | [], _ => (Bool.true_and _).symm
  | x :: xs, ys => by
    show (allS p x ctx && allB p (xs ++ ys) ctx) = ((allS p x ctx && allB p xs ctx) && allB p ys ctx)
    rw [allB_append p ctx xs ys, Bool.and_assoc]

theorem allB_drop_of_slice {p : List Ev → Stmt → Bool} {ss : List Stmt} {ctx : List Ev} {a b : ℕ} (hab : a ≤ b)
    (h : allBSlice p ss ctx a b = true) (hr : allB p (ss.drop b) ctx = true) : allB p (ss.drop a) ctx = true := by
  have e : (ss.drop a).drop (b - a) = ss.drop b := by rw [List.drop_drop]; congr 1; omega
  rw [← List.take_append_drop (b - a) (ss.drop a), allB_append, e]
  exact Bool.and_eq_true_iff.2 ⟨h, hr⟩

theorem allB_drop_of_le {p : List Ev → Stmt → Bool} {ss : List Stmt} {ctx : List Ev} {n : ℕ}
    (h : ss.length ≤ n) : allB p (ss.drop n) ctx = true := by
  rw [List.drop_eq_nil_of_le h]
  rfl

theorem allB_of_drop_zero {p : List Ev → Stmt → Bool} {ss : List Stmt} {ctx : List Ev}
    (h : allB p (ss.drop 0) ctx = true) : allB p ss ctx = true := by
  rwa [List.drop_zero] at h

/-- `carryNzG` from its pass over the body and its two lists' checks. -/
theorem carryNzG_of {fn : Fn} (h1 : allB (nzStmt (kvNz fn)) fn.body (spineE fn.body) = true)
    (h2 : nzUp.all (fun c => c.1 != fn.name || upChk fn c.2) = true)
    (h3 : (ownNz.all fun c => c.1 != fn.name || ownChk fn (V.n c.2)) = true) : carryNzG fn = true := by
  simp only [carryNzG, h1, h2, h3, Bool.and_self]

/-- A range of one function, from its check. -/
theorem rangeOk_one {c : Fn → Bool} {a : ℕ} {f : Fn} (hf : coreProgram[a]? = some f) (h : c f = true) :
    RangeOk (fun _ fn => c fn) a 1 := by
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hf
  unfold RangeOk
  rw [List.drop_eq_getElem_cons hl, List.take_succ_cons, List.take_zero]
  simp only [walkOk, h, Bool.and_self]

end

end LeanVM.Guest.Res
