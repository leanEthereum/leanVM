/-
  LeanVM.Guest.B1.Place.ArmFree0

  Group 0 of the arms' callees (from `70 * 0`, `armGrp`): exact for free or `armExactS`, and free of witness hints or
  `level_queries`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

@[expose] public section

theorem armFreeE0 : armGrpOk exLoc exRootS 0 = true := by decide +kernel

theorem armFreeM0 : armGrpOk nwLoc lqRootS 0 = true := by decide +kernel

end
end LeanVM.Guest.B1.Arm
