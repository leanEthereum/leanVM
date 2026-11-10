/-
  LeanVM.Guest.Budget.ClosedN

  The guest's completeness within the deployed budget with every number explicit: `verify_sub`'s
  words per child at its announced stack log and rate, a table of the guest's 28 opening arms
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
    (hle : ∀ seed s w, NodeRelation bytecode seed s w → DeployedLimits s w →
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

/-- **`verify_sub`'s words for a child of announced stack log `μ` and rate `r`** at the deployed
instance: row `r - 1`, column `μ - 22` for the guest's opening arms (`22 ≤ μ ≤ 28`, `1 ≤ r ≤ 4`,
`lean_ethereum.py:3491-3493`); `0` elsewhere, where no child of a node within `Limits`, its caps agreeing and no zero
challenge, is (`B1.Main.childShape_bounds`). -/
def deployedBvAt (μ r : ℕ) : ℕ :=
  if 22 ≤ μ ∧ μ ≤ 28 ∧ 1 ≤ r ∧ r ≤ 4 then
    ([[397396, 400303, 410771, 415581, 421245, 427328, 435224],
      [316265, 320181, 330196, 332388, 335926, 339373, 346254],
      [287777, 292953, 300361, 302720, 304916, 307460, 314142],
      [272554, 275315, 282119, 282932, 285304, 289094, 296506]].getD (r - 1) []).getD (μ - 22) 0
  else 0

/-- `open_stacked`'s words at the 28 candidates (`Count/VsOsAll`). -/
theorem osC_getD {c : ℕ} (hc : c < 28) : Count.osC c =
    [211747, 214654, 225122, 229932, 235596, 241679, 249575, 130616, 134532, 144547, 146739, 150277,
      153724, 160605, 102128, 107304, 114712, 117071, 119267, 121811, 128493, 86905, 89666, 96470,
      97283, 99655, 103445, 110857].getD c 0 := by
  interval_cases c
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
  · exact Count.osC_11
  · exact Count.osC_12
  · exact Count.osC_13
  · exact Count.osC_14
  · exact Count.osC_15
  · exact Count.osC_16
  · exact Count.osC_17
  · exact Count.osC_18
  · exact Count.osC_19
  · exact Count.osC_20
  · exact Count.osC_21
  · exact Count.osC_22
  · exact Count.osC_23
  · exact Count.osC_24
  · exact Count.osC_25
  · exact Count.osC_26
  · exact Count.osC_27

/-- `verify_sub`'s bound at an opening arm is the table's. -/
theorem vsBoundAt_eq_deployedBvAt {μ r : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    B1.VerifySub.vsBoundAt Count.vsWordsOs B1.VerifySub.vkBound μ r = deployedBvAt μ r := by
  have hc : B1.Whir.candidate μ r < 28 := by unfold B1.Whir.candidate; omega
  rw [Count.vsBoundAt_eq hc, osC_getD hc]
  interval_cases μ <;> interval_cases r <;> decide

/-- **The aggregation guest is complete within the deployed budget**, `verify_sub`'s words for a
child of announced stack log `μ` and rate `r` `deployedBvAt μ r`: the budget's words
`Count.deployedWords deployedBvAt`, its instructions `Count.deployedInstrs op`. -/
theorem guest_complete_numeric : GuestCompleteWithin (deployedBudget deployedBvAt) :=
  guestComplete_mono guest_complete fun seed s w _ _ hok => deployedBudget_size_mono _
    fun p hp => by
      obtain ⟨ch, hch, rfl⟩ :=
        List.mem_map.mp (show p ∈ w.children.map (childShape bytecode) from hp)
      obtain ⟨h1, h2, h3, h4⟩ := B1.Main.childShape_bounds bytecode_length hok hch
      exact (vsBoundAt_eq_deployedBvAt h1 h2 h3 h4).le

/-- The largest child's words: `μ = 28` at rate `1`. -/
theorem deployedBvAt_le (μ r : ℕ) : deployedBvAt μ r ≤ 435224 := by
  unfold deployedBvAt
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases μ <;> interval_cases r <;> decide
  · exact Nat.zero_le _

end
end LeanVM.Guest.Budget
