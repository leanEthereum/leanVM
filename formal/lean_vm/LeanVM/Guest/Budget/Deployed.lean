/-
  LeanVM.Guest.Budget.Deployed

  The guest's completeness within the explicit budget `mainBudget` at the deployed frame sizes,
  certificates and counts (`B2C`), from what is still supplied by hypothesis: the static callees'
  words (`MainStatics`), `main`'s callees' weights (`MainCounts`), `__loop2`'s arms (leanXMSS's check, inline) within
  `C`, each child's `verify_sub` within `Bvf` at its announced stack log and rate, and the
  children's loop's instructions within `l5Lin`.
-/

module

public import LeanVM.Guest.Budget.Final
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.B2C.RunsFit
public import LeanVM.Guest.B2C.CntWeight
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
      (Memory.Tree.node "__loop2" σ bufs kids).Valid coreProgram rd args rets →
        B2C.costW (listElementOrDefault Data.cplArms 37 []) σ (coreOf 37).body op ≤ C op)
    (H : ∀ op, MainCounts (B2C.ωArm C op) B2C.fs) (hS : MainStatics B2C.fs SB SK)
    (hV : ∀ seed s w, NodeRelation bytecode seed s w → DeployedLimits s w →
      ChildrenOk bytecode seed w →
      VerifySubGoalsTB B2C.fs B2C.cert 0 seed s w (Pvs w) (childBv Bvf w))
    (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (h5 : ∀ seed s w, NodeRelation bytecode seed s w → DeployedLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = "__loop4" → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH w) (Pvs w)).T5 t →
        t.weight (B2C.ωArm C op) ≤ l5Lin (c5 op) (s5 op) (v5 op) (End.work s w)) :
    GuestCompleteWithin (mainBudget B2C.fs SB SK Bvf (B2C.ωArm C) H c5 s5 v5 B2C.jtSets) :=
  B2C.guest_complete_b2c (mainComplete_budget B2C.fs B2C.cert B2C.cnt (B2C.ωArm C) B2C.jtSets H
    (B2C.two_le_fs _) B1.Sig.verify_lean_xmss_complete_holds
    B1.Sig.sphincs_complete B2C.runsFit hS hV (B2C.cnt_le_weight_arm C hC)
    c5 s5 v5 h5)

end
end LeanVM.Guest.Budget
