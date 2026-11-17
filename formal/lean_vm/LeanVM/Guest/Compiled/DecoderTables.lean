/-
  LeanVM.Guest.Compiled.DecoderTables

  The decoder's literal tables of registered loop helpers and return counts are the back end's
  input's.
-/

module

public import LeanVM.Guest.Compiled.Facts
public import LeanVM.Cost.Decoder.GuestTables
public import LeanVM.Cost.Decoder.GuestPlaces

/-!
# The decoder's tables of the back end's input

`Cost.Decoder.guestRegistered` flags each function the back end treats as a registered loop
helper (a loop name, registered in its input), and `Cost.Decoder.guestRetCounts` holds each
function's number of return words. The kernel compares both tables, past `__jump_tables`, with the
core program and the back end's input (`GuestData.guestInfo`) side by side (`registered_list`,
`retCounts_list`), which gives them for every function `1 ≤ j < nFns` (`guestRegistered_eq`,
`guestRetCounts_eq`).
-/

namespace LeanVM.Guest

open LeanVM.Guest.Core LeanVM.Compiler LeanVM.Guest.Compiled LeanVM.Cost.Decoder

@[expose] public section

theorem registered_list : guestRegisteredList.tail = (coreProgram.zip GuestData.guestInfo).map
    fun p => if isLoopName p.1.name && p.2.2.2.1 then 1 else 0 := by
  decide +kernel

theorem retCounts_list : guestRetCountsList.tail = GuestData.guestInfo.map (·.2.1) := by
  decide +kernel

theorem getD_toArray_succ {α : Type} (l : List α) (i : ℕ) (d : α) :
    l.toArray.getD (i + 1) d = l.tail.getD i d := by
  cases l <;> simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem coreOf_info {i : ℕ} (hi : i + 1 < nFns) :
    ∃ (hc : i < coreProgram.length) (hg : i < GuestData.guestInfo.length),
      coreOf (i + 1) = coreProgram[i]'hc ∧ infoOf (i + 1) = GuestData.guestInfo[i]'hg := by
  have hc : i < coreProgram.length := by have := coreProgram_length_succ; omega
  have hg : i < GuestData.guestInfo.length := by
    rw [GuestData.guestInfo_length]; rw [coreProgram_length] at hc; exact hc
  refine ⟨hc, hg, ?_, ?_⟩
  · rw [coreOf_eq (by omega) hi]
    simp only [Nat.add_sub_cancel]
  · unfold infoOf
    rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ hg]

theorem ite_beq_one (b : Bool) : ((if b = true then (1 : ℕ) else 0) == 1) = b := by
  cases b <;> rfl

/-- **The decoder's registered flags** are the back end's input's. -/
theorem guestRegistered_eq : ∀ j, 1 ≤ j → j < nFns →
    (guestRegistered.getD j 0 == 1) = (isLoopName (coreOf j).name && (infoOf j).2.2.1) := by
  intro j h1 h2
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hc, hg, e1, e2⟩ := coreOf_info h2
  have hz : i < ((coreProgram.zip GuestData.guestInfo).map
      fun p => if isLoopName p.1.name && p.2.2.2.1 then 1 else 0).length := by simp [hc, hg]
  rw [guestRegistered, getD_toArray_succ, registered_list, List.getD_eq_getElem _ _ hz,
    List.getElem_map, List.getElem_zip, e1, e2, ite_beq_one]

/-- **The decoder's return counts** are the back end's input's. -/
theorem guestRetCounts_eq : ∀ j, 1 ≤ j → j < nFns → guestRetCounts.getD j 0 = (infoOf j).2.1 := by
  intro j h1 h2
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨-, hg, -, e2⟩ := coreOf_info h2
  rw [guestRetCounts, getD_toArray_succ, retCounts_list,
    List.getD_eq_getElem _ _ (by simp [hg]), List.getElem_map, e2]

end
end LeanVM.Guest
