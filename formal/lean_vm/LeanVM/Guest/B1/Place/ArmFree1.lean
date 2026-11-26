/-
  LeanVM.Guest.B1.Place.ArmFree1

  Group 1 of the arms' callees (from `70 * 1`, `armGrp`): exact for free or `armExactS`, and free of witness hints or
  `level_queries`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

@[expose] public section

theorem armFreeE1 : armGrpOk exLoc exRootS 1 = true := by decide +kernel

theorem armFreeM1 : armGrpOk nwLoc lqRootS 1 = true := by decide +kernel

end
end LeanVM.Guest.B1.Arm
