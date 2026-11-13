/-
  LeanVM.Guest.Budget.DeployedBudget

  The deployed budget (`deployedBudget Bvf`): `mainBudget` at the deployed frame sizes, the static
  certificates' words (`Count.wSB`, `Count.wSK`) and counts (`Count.mainCounts`, `Budget/MvCount`), the children's
  loop's static counts (`l5C`, `ccS`, `vsCnt`, `Budget/L5Count`), the jump table's `SET`s and
  `main_loop2`'s arms (`B2C.xmssArmC`); and the guest's completeness within it, from each
  child's `verify_sub` within `Bvf` words and `vsCnt` instructions at its announced stack log and
  rate.
-/

module

public import LeanVM.Guest.Budget.Deployed
public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.Budget.MvCount
public import LeanVM.Guest.B2C.ArmBound
public import LeanVM.Guest.Budget.L5Count
public import LeanVM.Guest.AcceptableChild

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin Budget bytecode)
open LeanVM.Guest.B1.Main (VerifySubGoalsTB childBv)

@[expose] public section

/-- **The deployed budget**, `verify_sub`'s words `Bvf μ r` and instructions `vsCnt op μ r` for a
child of announced stack log `μ` and rate `r`. -/
noncomputable def deployedBudget (Bvf : ℕ → ℕ → ℕ) : Budget :=
  mainBudget B2C.fs Count.wSB Count.wSK Bvf (B2C.ωArm B2C.xmssArmC) Count.mainCounts l5C ccS vsCnt
    B2C.jtSets

/-- **The guest is complete within the deployed budget**, each child's `verify_sub` complete within
`Bvf` words at its announced stack log and rate, by a tree of `vsCnt op` instructions at it. -/
theorem guest_complete_deployed {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    (hV : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      ChildrenOk bytecode seed w →
      VerifySubGoalsTB B2C.fs B2C.cert 0 seed s w (Pvs w) (childBv Bvf w))
    (hPv : ∀ op (w : NodeWitness) c (hc : c < w.children.length) (rd : Reader) (t : Tree)
      (args rets : List E), Pvs w c t → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
        t.weight (B2C.ωArm B2C.xmssArmC op) ≤
          vsCnt op (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2) :
    GuestCompleteWithin (deployedBudget Bvf) :=
  guest_complete_budget B2C.xmssArmC B2C.xmssArmC_spec Count.mainCounts Count.mainStatics hV
    l5C ccS vsCnt fun _ _ _ _ hl op _ _ _ _ _ hv hb hT =>
      l5_honest_weight_le op hl (hPv op _) hv hb hT

end
end LeanVM.Guest.Budget
