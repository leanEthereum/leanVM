/-
  LeanVM.Guest.Budget.ClosedN

  The guest's completeness within the deployed budget with every number explicit: `verify_sub`'s
  words per child at its announced stack log, at the guest's 11 opening arms (`deployedBvAt`: the
  kernel's `Count.vsFixed` and the generated table `Count.osCs`, `Count.vsBoundAt_eq`).
-/

module

public import LeanVM.Guest.Budget.Closed
public import LeanVM.Guest.Count.VsBound
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.KernelLit
public import LeanVM.Guest.Count.Deployed

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin bytecode bytecode_length)

@[expose] public section

/-- **Completeness within a larger budget**, larger on the nodes the hypotheses admit. -/
theorem guestComplete_mono {b b' : NodeStatement → NodeWitness → ℕ} (h : End.GuestComplete b)
    (hle : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      ChildrenOk bytecode seed w → b s w ≤ b' s w) :
    End.GuestComplete b' :=
  fun seed s w hr hl hok hb => h seed s w hr hl hok ((hle seed s w hr hl hok).trans hb)

/-- The deployed budget grows with `verify_sub`'s words at the work's children's shapes. -/
theorem deployedBudget_size_mono {Bvf Bvf' : ℕ → ℕ → ℕ} (u : End.Work)
    (h : ∀ p ∈ u.childShapes, Bvf p.1 p.2 ≤ Bvf' p.1 p.2) :
    (deployedBudget Bvf).size u ≤ (deployedBudget Bvf').size u := by
  apply End.sizeOf_mono
  · simp only [deployedBudget, mainBudget, End.Linear.eval, B1.Main.mainWords]
    have := List.sum_le_sum (l := u.childShapes) (f := fun p => Bvf p.1 p.2)
      (g := fun p => Bvf' p.1 p.2) h
    omega
  · exact fun _ => le_rfl

/-- **`verify_sub`'s words for a child of announced stack log `μ`** at the deployed instance:
entry `μ - 20` for the guest's opening arms (`20 ≤ μ ≤ 30`, whatever the rate `1 ≤ r ≤ 4`); `0`
elsewhere, where no child of a node within `Limits`, its caps agreeing, is
(`B1.Main.childShape_bounds`). -/
noncomputable def deployedBvAt (μ r : ℕ) : ℕ :=
  if 20 ≤ μ ∧ μ ≤ 30 ∧ 1 ≤ r ∧ r ≤ 4 then Count.vsFixed + Count.osCs.getD (μ - 20) 0 else 0

/-- `verify_sub`'s bound at an opening arm is the table's. -/
theorem vsBoundAt_eq_deployedBvAt {μ r : ℕ} (h1 : 20 ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    B1.VerifySub.vsBoundAt Count.vsWordsOs B1.VerifySub.vkBound μ r = deployedBvAt μ r := by
  rw [Count.vsBoundAt_eq h1 h2, Count.osC_getD (by omega)]
  unfold deployedBvAt
  rw [ite_eq_left ⟨h1, h2, h3, h4⟩]

/-- **The aggregation guest is complete within the deployed budget**, `verify_sub`'s words for a
child of announced stack log `μ` and rate `r` `deployedBvAt μ r`: the budget's words
`Count.deployedWords deployedBvAt`, its instructions `Count.deployedInstrs op`. -/
theorem guest_complete_numeric : GuestCompleteWithin (deployedBudget deployedBvAt) :=
  guestComplete_mono guest_complete fun seed s w _ _ hok => deployedBudget_size_mono _
    fun p hp => by
      obtain ⟨ch, hch, rfl⟩ :=
        List.mem_map.mp (show p ∈ w.children.map (childShape bytecode) from hp)
      obtain ⟨h1, h2, h3, h4⟩ := B1.Main.childShape_bounds vsCompleteHyp_deployed hok hch
      exact (vsBoundAt_eq_deployedBvAt h1 h2 h3 h4).le

/-- The largest child's words. -/
kernel_lit deployedBvMax : ℕ := Count.vsFixed + B1.lmax Count.osCs

theorem deployedBvAt_le (μ r : ℕ) : deployedBvAt μ r ≤ deployedBvMax := by
  rw [← deployedBvMax_eq]
  unfold deployedBvAt
  split_ifs
  · refine Nat.add_le_add_left ?_ _
    rw [List.getD_eq_getElem?_getD]
    cases hi : Count.osCs[μ - 20]? with
    | none => exact Nat.zero_le _
    | some x => exact B1.le_lmax (List.mem_of_getElem? hi)
  · exact Nat.zero_le _

/-- `verify_sub`'s instructions of opcode `op` at its opening arms. -/
def childList (op : LeanVM.Parameters.Opcode) : List ℕ := (List.range 11).map fun m ↦ (Count.deployedInstrs op).childShape (m + 20) 1

/-- The largest of `verify_sub`'s instructions of each opcode over its opening arms (`Fits.childMax`). -/
kernel_lit cmXor : ℕ := B1.lmax (childList .xor)
kernel_lit cmMul : ℕ := B1.lmax (childList .mulNative)
kernel_lit cmSet : ℕ := B1.lmax (childList .setConstant)
kernel_lit cmDeref : ℕ := B1.lmax (childList .deref)
kernel_lit cmJump : ℕ := B1.lmax (childList .jump)
kernel_lit cmKeccak : ℕ := B1.lmax (childList .keccak)

end
end LeanVM.Guest.Budget
