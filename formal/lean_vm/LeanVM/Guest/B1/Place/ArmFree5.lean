/-
  LeanVM.Guest.B1.Place.ArmFree5

  Group 5 of the arms' callees (from `350` on, `armGrp`): exact for free or `armExactS`, and free of witness hints or
  `level_queries`, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

@[expose] public section

theorem armFreeE5 : armGrpOk exLoc exRootS 5 true = true := by decide +kernel

theorem armFreeM5 : armGrpOk nwLoc lqRootS 5 true = true := by decide +kernel

end
end LeanVM.Guest.B1.Arm
