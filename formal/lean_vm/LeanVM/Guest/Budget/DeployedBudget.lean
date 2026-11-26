/-
  LeanVM.Guest.Budget.DeployedBudget

  The deployed budget (`deployedBudget Bvf`): `mainBudget` at the deployed frame sizes, the static
  certificates' words (`Count.wSB`, `Count.wSK`) and counts (`Count.mainCounts`, `Budget/MvCount`), the children's
  loop's static counts (`l5C`, `ccS`, `vsCnt`, `Budget/L5Count`), the jump table's `SET`s and
  `main_loop2`'s arms (`B2C.xmssArmC`).
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Budget.Final
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.B2C.RunsFit
public import LeanVM.Guest.B2C.CntWeight
public import LeanVM.Guest.B1.Sig.XmssSegComplete
public import LeanVM.Guest.B1.Sig.SphincsCompleteHolds
public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.Budget.MvCount
public import LeanVM.Guest.B2C.ArmBound
public import LeanVM.Guest.Budget.L5Count
public import LeanVM.Guest.AcceptableChild

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node
open LeanVM.Guest.End (Budget)

@[expose] public section

/-- **The deployed budget**, `verify_sub`'s words `Bvf μ r` and instructions `vsCnt op μ r` for a
child of announced stack log `μ` and rate `r`. -/
noncomputable def deployedBudget (Bvf : ℕ → ℕ → ℕ) : Budget :=
  mainBudget B2C.fs Count.wSB Count.wSK Bvf (B2C.ωArm B2C.xmssArmC) Count.mainCounts l5C ccS vsCnt
    B2C.jtSets

end
end LeanVM.Guest.Budget
