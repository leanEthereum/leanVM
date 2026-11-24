/-
  LeanVM.Guest.B1.Place.ArmFree2

  Group 2 of the arms' callees (from `70 * 2`, `armGrp`): exact for free or `armExactS`, and free of witness hints or
  `level_queries`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

@[expose] public section

theorem armFreeE2 : armGrpOk exLoc exRootS 2 = true := by decide +kernel

theorem armFreeM2 : armGrpOk nwLoc lqRootS 2 = true := by decide +kernel

end
end LeanVM.Guest.B1.Arm
