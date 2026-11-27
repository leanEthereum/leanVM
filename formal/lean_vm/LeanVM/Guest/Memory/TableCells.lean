/-
  LeanVM.Guest.Memory.TableCells

  The cells of `main`'s frame that `__jump_tables` writes: the guest's own data, apart from the
  honest memory (`Memory.lean`), which is generic over the program.
-/

module

public import LeanVM.Guest.Code
public import LeanVM.Guest.Data.FrameSizes
public import LeanVM.Guest.Data.Functions
import all LeanVM.Guest.Data.Functions

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **`main`'s jump table**: the slot each `SET` of `__jump_tables` writes in `main`'s frame,
and its word. -/
def tableCells : List (ℕ × E) :=
  Data.f0.code.filterMap fun
    | .set o k0 k1 => some (o, OffsetInstruction.immediateWord k0 k1)
    | _ => none

set_option maxRecDepth 100000 in
/-- The slots are `Data.mainCells, Data.mainCells + 1, …`, one per `SET`. -/
theorem tableCells_offsets : tableCells.map Prod.fst = List.range' Data.mainCells Data.jtSlots := by
  decide +kernel

/-- The slots lie in `main`'s frame past its header, below `Data.mainCells + Data.jtSlots`. -/
theorem tableCells_off {q : ℕ × E} (hq : q ∈ tableCells) :
    2 ≤ q.1 ∧ q.1 < Data.mainCells + Data.jtSlots := by
  have := tableCells_offsets ▸ List.mem_map_of_mem (f := Prod.fst) hq
  rw [List.mem_range'_1] at this
  have : 2 ≤ Data.mainCells := by decide
  omega

/-- Two slots at one offset are one slot. -/
theorem tableCells_agree {q q' : ℕ × E} (hq : q ∈ tableCells) (hq' : q' ∈ tableCells)
    (he : q.1 = q'.1) : q.2 = q'.2 := by
  have hnd : (tableCells.map Prod.fst).Nodup := tableCells_offsets ▸ List.nodup_range'
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq'
  have : i = j := by
    have hi' : i < (tableCells.map Prod.fst).length := by simpa using hi
    have hj' : j < (tableCells.map Prod.fst).length := by simpa using hj
    exact (List.Nodup.getElem_inj_iff hnd (hi := hi') (hj := hj')).mp (by simpa using he)
  subst this
  rfl

end
end LeanVM.Guest.Memory
