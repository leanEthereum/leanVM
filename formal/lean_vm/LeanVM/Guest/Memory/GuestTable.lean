/-
  LeanVM.Guest.Memory.GuestTable

  The guest's jump table in `main`'s frame: the cells `__jump_tables` sets, at the slots the back
  end's tables give.
-/

module

public import LeanVM.Guest.Deployed.Data
public import LeanVM.Guest.Memory
public import Statement.Data.Bytecode

/-!
# `main`'s jump table

The honest memory (`Memory.lean`) holds whatever cells the compiled code writes; at the guest,
`main`'s frame holds the jump table its first function `__jump_tables` (`Data.f0`) writes, one
slot per `SET` (`tableCells`), at the offsets `Deployed.Data.mainCells` to
`Deployed.Data.mainCells + Deployed.Data.jtSlots - 1` (`tableCells_offsets`), past the header and
one word per offset (`tableCells_off`, `tableCells_agree`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- **`main`'s jump table**: the slot each `SET` of `__jump_tables` writes in `main`'s frame,
and its word. -/
def tableCells : List (ℕ × E) :=
  Data.f0.code.filterMap fun
    | .set o k0 k1 => some (o, OffsetInstruction.immediateWord k0 k1)
    | _ => none

set_option maxRecDepth 100000 in
/-- The slots are `Deployed.Data.mainCells, Deployed.Data.mainCells + 1, …`, one per `SET`. -/
theorem tableCells_offsets : tableCells.map Prod.fst = List.range' Deployed.Data.mainCells Deployed.Data.jtSlots := by
  decide +kernel

/-- The slots lie in `main`'s frame past its header, below `Deployed.Data.mainCells + Deployed.Data.jtSlots`. -/
theorem tableCells_off {q : ℕ × E} (hq : q ∈ tableCells) :
    2 ≤ q.1 ∧ q.1 < Deployed.Data.mainCells + Deployed.Data.jtSlots := by
  have := tableCells_offsets ▸ List.mem_map_of_mem (f := Prod.fst) hq
  rw [List.mem_range'_1] at this
  have : 2 ≤ Deployed.Data.mainCells := by decide
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
