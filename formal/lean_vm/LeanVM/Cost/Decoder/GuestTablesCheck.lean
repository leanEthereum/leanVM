module

public import LeanVM.Cost.Decoder.GuestTables
public import LeanVM.Guest.CoreData

/-!
# The guest decoder's tables, checked

The literal tables of `GuestTables.lean` are the guest's: for every function `j < nFns`, its entry
pc (`(fnOf j).entryPc`) and its number of arguments (`(coreOf j).params.length`), each table one
equality of lists the kernel evaluates, one number a function. The return counts and the
registered flags are the back end's input's (`Backend/Guest/DecoderTables.lean`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Guest

@[expose] public section

theorem toArray_getD {α : Type} (l : List α) (j : ℕ) (d : α) : l.toArray.getD j d = l.getD j d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem listElementOrDefault_eq_getD {α : Type} (l : List α) (j : ℕ) (d : α) :
    listElementOrDefault l j d = l.getD j d := by
  induction l generalizing j with
  | nil => rfl
  | cons a l ih => cases j <;> simp [listElementOrDefault, ih]

theorem guestEntriesList_eq : guestEntriesList = Data.functions.map (·.entryPc) := by
  decide +kernel

theorem guestArgCountsList_eq : guestArgCountsList = 0 :: coreProgram.map (·.params.length) := by
  decide +kernel

theorem coreOf_zero_params : (coreOf 0).params.length = 0 := by
  decide +kernel

/-- **Function `j`'s entry pc** is the table's. -/
theorem guestEntries_fnOf {j : ℕ} (_ : j < nFns) : guestEntries.getD j 0 = (fnOf j).entryPc := by
  rw [toArray_getD, guestEntriesList_eq, fnOf, listElementOrDefault_eq_getD,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Data.functions[j]? <;> rfl

/-- **Function `j`'s number of arguments** is the table's. -/
theorem guestArgCounts_coreOf {j : ℕ} (_ : j < nFns) :
    guestArgCounts.getD j 0 = (coreOf j).params.length := by
  rw [toArray_getD, guestArgCountsList_eq]
  cases j with
  | zero => exact coreOf_zero_params.symm
  | succ k =>
    rw [List.getD_cons_succ, coreOf, Nat.add_sub_cancel, listElementOrDefault_eq_getD,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases coreProgram[k]? <;> rfl

end

end LeanVM.Cost.Decoder
