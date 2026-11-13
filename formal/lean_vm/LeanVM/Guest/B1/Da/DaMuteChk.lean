/-
  LeanVM.Guest.B1.Da.DaMuteChk

  The level arms `da_verify` dispatches to have no witness hint in their subtrees (kernel evaluation), so they pop nothing (`noWitS`).
-/

module

public import LeanVM.Guest.B1.Common.NoWitMute
public import LeanVM.Guest.B1.Da.PureAt

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

theorem dl_noWit : dlNames.all (noWitCallee idx% «da_verify») = true := by decide +kernel

/-- **A level arm of `da_verify` pops nothing.** -/
theorem daLevels_noWit {L : ℕ} (hL : L ≤ 10) : noWitS (daLevelsName L) = true :=
  noWitS_of_callee (List.all_eq_true.mp dl_noWit _ (List.mem_map.mpr ⟨L, List.mem_range.mpr (by omega), rfl⟩))

end
end LeanVM.Guest.B1.Da
