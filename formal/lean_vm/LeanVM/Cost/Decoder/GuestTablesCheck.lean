module

public import LeanVM.Cost.Decoder.GuestTables
public import LeanVM.Guest.Glob
import all LeanVM.Guest.Glob
meta import Lean.Elab.Tactic

/-!
# The guest decoder's tables, checked

The literal tables of `GuestTables.lean` are the guest's: for every function `j < nFns`, its entry
pc, its numbers of arguments and of return words (`(glob.sig j).entry`, `nargs`, `nret`), and its
certificate's frame cells (`(certOf j).locs`). Each table is one equality of lists, read entry by
entry: the entries and the counts by the kernel's evaluation, one number a function; the frame
cells by unfolding alone (`kernel_rfl`), the table's rows being the certificates' cells' constants,
so that no list of cells is evaluated.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Guest

open Lean Elab Tactic Meta in
/-- Closes `a = b` by `Eq.refl a`, the definitional unfolding left to the kernel: the elaborator's
`rfl` recurses once per entry of a list. -/
local elab "kernel_rfl" : tactic => liftMetaFinishingTactic fun g ↦ do
  let some (_, a, _) := (← instantiateMVars (← g.getType)).eq? | throwError "kernel_rfl: not an equality"
  g.assign (← mkEqRefl a)

@[expose] public section

theorem listElementOrDefault_eq_getD {α : Type} (l : List α) (j : ℕ) (d : α) :
    listElementOrDefault l j d = l.getD j d := by
  induction l generalizing j with
  | nil => rfl
  | cons a l ih => cases j <;> simp [listElementOrDefault, ih]

theorem getD_map_eq {α β : Type} (f : α → β) (l : List α) (j : ℕ) (d : α) (e : β) (h : e = f d) :
    (l.map f).getD j e = f (listElementOrDefault l j d) := by
  subst h
  simp [List.getD_eq_getElem?_getD, listElementOrDefault_eq_getD]

theorem toArray_getD {α : Type} (l : List α) (j : ℕ) (d : α) : l.toArray.getD j d = l.getD j d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `certOf` keeps the certificate's cells and return count. -/
theorem certOf_cells_nret (j : ℕ) :
    (certOf j).cells = (listElementOrDefault Data.certs j default).cells ∧
      (certOf j).nret = (listElementOrDefault Data.certs j default).nret := by
  unfold certOf
  generalize listElementOrDefault Data.certs j default = c
  obtain ⟨⟨⟩⟩ := c
  exact ⟨rfl, rfl⟩

theorem guestEntriesList_eq : guestEntriesList = Data.functions.map (·.entryPc) := by
  decide +kernel

theorem guestArgCountsList_eq : guestArgCountsList = 0 :: coreProgram.map (·.params.length) := by
  decide +kernel

theorem guestRetCountsList_eq : guestRetCountsList = Data.certs.map (·.nret) := by
  decide +kernel

theorem guestLocsList_eq_map : guestLocsList = Data.certs.map Check.Cert.locs := by
  kernel_rfl

theorem coreOf_zero_params : (coreOf 0).params.length = 0 := by
  decide +kernel

theorem guestEntries_eq : ∀ j < nFns, guestEntries.getD j 0 = (glob.sig j).entry := fun j _ ↦ by
  rw [toArray_getD, guestEntriesList_eq, getD_map_eq (d := default) (e := 0)] <;> rfl

theorem guestArgCounts_eq : ∀ j < nFns, guestArgCounts.getD j 0 = (glob.sig j).nargs := fun j _ ↦ by
  rw [toArray_getD, guestArgCountsList_eq]
  cases j with
  | zero => exact coreOf_zero_params.symm
  | succ k => rw [List.getD_cons_succ, getD_map_eq (d := default) (e := 0)] <;> rfl

theorem guestRetCounts_eq : ∀ j < nFns, guestRetCounts.getD j 0 = (glob.sig j).nret := fun j _ ↦ by
  rw [toArray_getD, guestRetCountsList_eq, getD_map_eq (d := default) (e := 0)]
  · exact (certOf_cells_nret j).2.symm
  · rfl

/-- The entries, argument and return counts, for every function. -/
theorem guestSig_eq : ∀ j < nFns,
    guestEntries.getD j 0 = (glob.sig j).entry ∧ guestArgCounts.getD j 0 = (glob.sig j).nargs ∧
      guestRetCounts.getD j 0 = (glob.sig j).nret :=
  fun j hj ↦ ⟨guestEntries_eq j hj, guestArgCounts_eq j hj, guestRetCounts_eq j hj⟩

/-- The cells' lists are the certificates', function by function. -/
theorem guestLocsList_eq : ∀ j < nFns, guestLocsList.getD j [] = (certOf j).locs := fun j _ ↦ by
  rw [guestLocsList_eq_map, getD_map_eq (d := default) (e := []), Check.Cert.locs, Check.Cert.locs,
    (certOf_cells_nret j).1]
  rfl

set_option maxRecDepth 100000 in
theorem guestLocsList_length : guestLocsList.length = nFns := by decide +kernel

set_option maxRecDepth 100000 in
theorem guestLocs_eq {j : ℕ} (hj : j < nFns) : (guestLocs.getD j #[]).toList = (certOf j).locs := by
  rw [← guestLocsList_eq j hj, guestLocs, guestLocsLit]
  have hl : j < guestLocsList.length := guestLocsList_length ▸ hj
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, hl]

end

end LeanVM.Cost.Decoder
