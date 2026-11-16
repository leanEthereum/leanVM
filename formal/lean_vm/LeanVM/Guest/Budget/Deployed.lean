/-
  LeanVM.Guest.Budget.Deployed

  The guest's completeness within the explicit budget `mainBudget` at the deployed frame sizes,
  certificates and counts (`B2C`), from what is still supplied by hypothesis: the static callees'
  words (`MainStatics`), `main`'s callees' weights (`MainCounts`), `main_loop2`'s arms (leanXMSS's check, inline) within
  `C`, each child's `verify_sub` within `Bvf` at its announced stack log and rate, and the
  children's loop's instructions within `l5Lin`.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Budget.Final
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.B2C.RunsFit
public import LeanVM.Guest.B2C.DeployedEq
public import LeanVM.Guest.B1.Sig.XmssSegComplete
public import LeanVM.Guest.B1.Sig.SphincsCompleteHolds
public import LeanVM.Guest.AcceptableChild

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin bytecode)
open LeanVM.Guest.B1.Main (VerifySubGoalsTB MainStatics childBv mainPredsH hDvNH)

@[expose] public section

/-- **The guest is complete within `mainBudget`** at the deployed instance. -/
theorem guest_complete_budget {SB SK : String → ℕ} {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node name% «main_loop2» σ bufs kids).Valid coreProgram rd args rets →
        Deployed.costW (listElementOrDefault Deployed.Data.arms (fn_idx% «main_loop2») []) σ (coreOf (fn_idx% «main_loop2»)).body op ≤ C op)
    (H : ∀ op, MainCounts (Deployed.ωArm C op) Deployed.fs) (hS : MainStatics Deployed.fs SB SK)
    (hV : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      ChildrenOk bytecode seed w →
      VerifySubGoalsTB Deployed.fs B2C.cert 0 seed s w (Pvs w) (childBv Bvf w))
    (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (h5 : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = name% main_loop4 → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH w) (Pvs w)).T5 t →
        t.weight (Deployed.ωArm C op) ≤ l5Lin (c5 op) (s5 op) (v5 op) (End.work s w)) :
    GuestCompleteWithin (mainBudget Deployed.fs SB SK Bvf (Deployed.ωArm C) H c5 s5 v5 Deployed.jtSets) := by
  revert H hS hV h5
  rw [← B2C.fs_deployed, ← B2C.ωArm_deployed, ← B2C.jtSets_deployed]
  intro H hS hV h5
  exact B2C.guest_complete_b2c (mainComplete_budget B2C.fs B2C.cert B2C.cnt (B2C.ωArm C) B2C.jtSets H
    (B2C.two_le_fs _) B1.Sig.verify_lean_xmss_complete_holds
    B1.Sig.sphincs_complete B2C.runsFit hS hV
    (B2C.cnt_le_weight_arm C fun op σ bufs kids rd args rets hv => by
      rw [B2C.costW_deployed, B2C.cplArms_deployed]
      exact hC op σ bufs kids rd args rets hv)
    c5 s5 v5 h5)

end
end LeanVM.Guest.Budget
