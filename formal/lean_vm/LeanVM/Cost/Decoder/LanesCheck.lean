module

public import LeanVM.Cost.Decoder.Lanes
public import LeanVM.Cost.Bounds.Decoder.GuestLocs

/-!
# The guest's packed frame cells, checked

`locAt j i` (`Lanes.lean`) is function `j`'s frame cell `i` of the table `guestLocsList`, for every
function `j`: the slots name each function's group and lane (`guestSlots_ok`, by the kernel's
evaluation of the slots and groups, numbers only, one walk of the slots), and every cell is below `2^16`
(`Bounds.guestLocsList_lt`), so the lane of a packed number is the cell (`packLanes_cell`). Every
packed number is one limb (`guestLanes_lt`: at most four functions a group, `guestLaneGroups_le`).
-/

namespace LeanVM.Cost.Decoder

@[expose] public section

/-- Each function's slot names a group, whose lane is the function (a linear walk of the slots). -/
theorem guestSlots_ok : guestSlotsList.zipIdx.all (fun p ↦
    1 ≤ p.1 / 4 && (guestLaneGroups.getD (p.1 / 4 - 1) [])[p.1 % 4]? == some p.2) = true := by
  decide +kernel

/-- A slot for every function. -/
theorem guestSlotsList_length : guestSlotsList.length = guestLocsList.length := by decide +kernel

/-- At most four functions a group. -/
theorem guestLaneGroups_le : guestLaneGroups.all (·.length ≤ 4) = true := by decide +kernel

/-- Every slot is one limb. -/
theorem guestSlotsList_lt : guestSlotsList.all (· < 2 ^ 64) = true := by decide +kernel

theorem toArray_getD' {α : Type} (l : List α) (j : ℕ) (d : α) : l.toArray.getD j d = l.getD j d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- A row of the packed table, as arrays, is its list's. -/
theorem guestLanes_getD (r : ℕ) : guestLanes.getD r #[] = (guestLanesList.getD r []).toArray := by
  rw [guestLanes, guestLocsLit, toArray_getD', List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases guestLanesList[r]? <;> rfl

/-- An entry of the packed table is its list's. -/
theorem guestLanes_entry (r i : ℕ) : (guestLanes.getD r #[]).getD i 0 = (guestLanesList.getD r []).getD i 0 := by
  rw [guestLanes_getD]; exact toArray_getD' _ _ _

/-- Group `g`'s row of the packed table. -/
theorem guestLanesList_group (g : ℕ) : guestLanesList.getD (g + 1) [] =
    packLanes ((guestLaneGroups.getD g []).map fun j ↦ guestLocsList.getD j []) := by
  rw [guestLanesList, List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getD_eq_getElem?_getD (l := guestLaneGroups)]
  cases guestLaneGroups[g]? <;> rfl

/-- Every frame cell below `2^16`. -/
theorem guestLocsList_cell_lt {r : List ℕ} (hr : r ∈ guestLocsList) {x : ℕ} (hx : x ∈ r) :
    x < 65536 := by
  have h := Bounds.guestLocsList_lt
  rw [List.all_eq_true] at h
  have h' := h r hr
  rw [List.all_eq_true] at h'
  exact of_decide_eq_true (h' x hx)

/-- The rows of a group: its functions' cells, each below `2^16`. -/
theorem group_rows_lt (g : List ℕ) :
    ∀ r ∈ g.map (fun j ↦ guestLocsList.getD j []), ∀ x ∈ r, x < 65536 := by
  intro r hr x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hr
  rcases getD_mem_or_nil guestLocsList j with h | h
  · exact guestLocsList_cell_lt h hx
  · rw [h] at hx; simp at hx

/-- **Every packed number is one limb.** -/
theorem guestLanes_lt (r i : ℕ) : (guestLanes.getD r #[]).getD i 0 < 2 ^ 64 := by
  rw [guestLanes_getD, toArray_getD']
  cases r with
  | zero =>
    have h := guestSlotsList_lt
    rw [List.all_eq_true] at h
    exact getD_lt_of_all (by norm_num) (fun x hx ↦ of_decide_eq_true (h x hx)) i
  | succ g =>
    rw [guestLanesList_group]
    refine packLanes_lt _ (group_rows_lt _) ?_ i
    rw [List.length_map]
    rcases getD_mem_or_nil guestLaneGroups g with h | h
    · have := guestLaneGroups_le
      rw [List.all_eq_true] at this
      exact of_decide_eq_true (this _ h)
    · rw [h]; simp

/-- **Function `j`'s cell `i`, read off the packed table**, is the table's, for every function. -/
theorem locAt_eq {j : ℕ} (hj : j < guestLocsList.length) (i : ℕ) :
    locAt j i = (guestLocsList.getD j []).getD i 0 := by
  have hj' : j < guestSlotsList.length := by rw [guestSlotsList_length]; exact hj
  have hs := guestSlots_ok
  rw [List.all_eq_true] at hs
  have hmem : (guestSlotsList[j], j) ∈ guestSlotsList.zipIdx :=
    List.mem_iff_getElem.2 ⟨j, by simpa using hj', by simp [List.getElem_zipIdx]⟩
  have hsj := hs _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsj
  obtain ⟨h1, h2⟩ := hsj
  unfold locAt
  simp only
  rw [guestLanes_entry 0 j, show guestLanesList.getD 0 [] = guestSlotsList from rfl,
    List.getD_eq_getElem?_getD (l := guestSlotsList), List.getElem?_eq_getElem hj', Option.getD_some]
  generalize guestSlotsList[j] = s at h1 h2
  obtain ⟨g, hg⟩ : ∃ g, s / 4 = g + 1 := ⟨s / 4 - 1, by omega⟩
  rw [hg] at h2 ⊢
  simp only [Nat.add_sub_cancel] at h2
  rw [guestLanes_entry, guestLanesList_group, packLanes_cell _ (group_rows_lt _),
    List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map, h2]
  rfl

end

end LeanVM.Cost.Decoder
