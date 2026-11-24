/-
  LeanVM.Guest.B1.Place.ArmFree3

  Group 3 of the arms' callees (from `70 * 3`, `armGrp`): exact for free or `armExactS`, and free of witness hints or
  `level_queries`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

@[expose] public section

theorem armFreeE3 : armGrpOk exLoc exRootS 3 = true := by decide +kernel

theorem armFreeM3 : armGrpOk nwLoc lqRootS 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Arm
