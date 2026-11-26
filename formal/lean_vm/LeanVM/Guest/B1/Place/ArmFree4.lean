/-
  LeanVM.Guest.B1.Place.ArmFree4

  Group 4 of the arms' callees (from `70 * 4`, `armGrp`): exact for free or `armExactS`, and free of witness hints or
  `level_queries`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

@[expose] public section

theorem armFreeE4 : armGrpOk exLoc exRootS 4 = true := by decide +kernel

theorem armFreeM4 : armGrpOk nwLoc lqRootS 4 = true := by decide +kernel

end
end LeanVM.Guest.B1.Arm
