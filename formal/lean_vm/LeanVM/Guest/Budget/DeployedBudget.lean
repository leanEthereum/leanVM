/-
  LeanVM.Guest.Budget.DeployedBudget

  The deployed budget (`deployedBudget Bvf`): `mainBudget` at the deployed frame sizes, the static
  certificates' words (`Count.wSB`, `Count.wSK`) and counts (`Count.mainCounts`, `Budget/MvCount`), the children's
  loop's static counts (`l5C`, `ccS`, `vsCnt`, `Budget/L5Count`), the jump table's `SET`s and
  `main_loop2`'s arms (`Deployed.xmssArmC`).
-/

module

public import LeanVM.Guest.Budget.Final
public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.Budget.MvCount
public import LeanVM.Guest.Deployed
public import LeanVM.Guest.Budget.L5Count

namespace LeanVM.Guest.Budget

open LeanVM.Guest.End (Budget)

@[expose] public section

/-- **The deployed budget**, `verify_sub`'s words `Bvf μ r` and instructions `vsCnt op μ r` for a
child of announced stack log `μ` and rate `r`. -/
noncomputable def deployedBudget (Bvf : ℕ → ℕ → ℕ) : Budget :=
  mainBudget Deployed.fs Count.wSB Count.wSK Bvf (Deployed.ωArm Deployed.xmssArmC) Count.mainCounts l5C ccS vsCnt
    Deployed.jtSets

end
end LeanVM.Guest.Budget
