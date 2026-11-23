/-
  LeanVM.Guest.B1.Bits.BusGrindPlacedE

  `bus_grind_check__L{d}`, placed and bounded, by a tree popping nothing, exact at every node.
-/

module

public import LeanVM.Guest.B1.Bits.BusGrindPlaced
public import LeanVM.Guest.B1.Tables.FlatAtTE

/-!
# `bus_grind_check`, placed and exact

`bus_grind_check_completeDTBR`: within its frame, by a tree popping nothing whose every node is
exact on the memory (`bus_grind_relAtInE`, a leaf: `grind_check` is inlined).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`bus_grind_check__L{d}`, placed, within its frame**: a tree popping nothing, every node exact
on the memory. -/
theorem bus_grind_check_completeDTBR {d : ℕ} (hd : d ∈ busGrindDeployed) {κ : ℕ} (hκ : 11 ≤ κ)
    {args rets : List E} {Lin : Layout} (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → busGrindPre d rd args rets) :
    CompleteAtDTBR fs cert κ (busGrindName d) Lin args (Returns rets)
      (fun rd t => t.pops coreProgram rd = [] ∧ t.Every (ExactAt coreProgram rd)) (fs (busGrindName d)) :=
  fun fp => ⟨fs (busGrindName d), [], rets, [], le_rfl, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
    fun _ hl hL => bus_grind_relAtInE hd hκ hpre fp hl (by simpa using hL)⟩

end
end LeanVM.Guest.B1
