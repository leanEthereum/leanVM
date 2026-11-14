/-
  LeanVM.Guest.Budget.ClosedN

  The guest's completeness within the deployed budget with every number explicit: `verify_sub`'s
  words per child at its announced stack log, a table of the guest's 11 opening arms
  (`deployedBvAt`, `Count.vsBoundAt_eq`).
-/

module

public import LeanVM.Guest.Budget.Closed
public import LeanVM.Guest.Count.VsBound
public import LeanVM.Guest.AcceptableChild

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
elsewhere, where no child of a node within `Limits`, its caps agreeing and no zero challenge, is
(`B1.Main.childShape_bounds`). -/
def deployedBvAt (μ r : ℕ) : ℕ :=
  if 20 ≤ μ ∧ μ ≤ 30 ∧ 1 ≤ r ∧ r ≤ 4 then
    [388016, 387619, 390584, 394633, 405250, 410562, 419149, 425180, 432727, 436026, 439001].getD (μ - 20) 0
  else 0

/-- `open_stacked`'s words at the 11 arms (`Count/VsOsAll`). -/
theorem osC_getD {m : ℕ} (hm : m < 11) : Count.osC m =
    [208731, 208334, 211299, 215348, 225965, 231277, 239864, 245895, 253442, 256741, 259716].getD m 0 := by
  interval_cases m
  · exact Count.osC_0
  · exact Count.osC_1
  · exact Count.osC_2
  · exact Count.osC_3
  · exact Count.osC_4
  · exact Count.osC_5
  · exact Count.osC_6
  · exact Count.osC_7
  · exact Count.osC_8
  · exact Count.osC_9
  · exact Count.osC_10

/-- `verify_sub`'s bound at an opening arm is the table's. -/
theorem vsBoundAt_eq_deployedBvAt {μ r : ℕ} (h1 : 20 ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    B1.VerifySub.vsBoundAt Count.vsWordsOs B1.VerifySub.vkBound μ r = deployedBvAt μ r := by
  rw [Count.vsBoundAt_eq h1 h2, osC_getD (by omega)]
  unfold deployedBvAt
  rw [ite_eq_left ⟨h1, h2, h3, h4⟩]
  interval_cases μ <;> decide

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

/-- The largest child's words: `μ = 30`. -/
theorem deployedBvAt_le (μ r : ℕ) : deployedBvAt μ r ≤ 439001 := by
  unfold deployedBvAt
  split_ifs with h
  · obtain ⟨h1, h2, -, -⟩ := h
    interval_cases μ <;> decide
  · exact Nat.zero_le _

end
end LeanVM.Guest.Budget
