/-
  LeanVM.Guest.Budget.Fits

  The deployed limits' caps keep the deployed budget's size within `2^30` and the coverage table
  below `2^23`, so the guest is complete on every node within them.
-/

module

public import LeanVM.Guest.Budget.ClosedN
public import LeanVM.Guest.Count.Deployed
public import Statement.Corollaries
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.B1.Main.Plan
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# The nodes within the deployed limits

The deployed budget (`deployedBudget deployedBvAt`: `Count.deployedWords`, `Count.deployedInstrs`)
is linear in the counts of `work`, each child charged at most at the largest opening arm, `μ = 30`
(`deployedBvAt_le`, `childShape_le_childMax`). `DeployedLimits` caps the children, their claims, the
raw signatures and the blob matrix's rows; the coverage table is `coverageSlots`
(`B1.Main.planSlots_eq`), and the declared claims are at most it (`declared_le`, the
sub-multisets). At the caps, the words are at most `2^26` and each opcode's instructions at most
`2^instrLog op` (`words_le`, `instrs_le`), so the size is at most `2^30` (`size_le`) and the coverage
table below `2^23` (`GuestLimits.of_limits`): `guest_complete_numeric` gives a valid execution within
`2^30` (`guest_complete_on_acceptable_children`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness
open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Node LeanVM.Protocol
open LeanVM.Guest.End (work bytecode)

@[expose] public section

/-- A list's entries within `M` bound its entries by index. -/
theorem getD_le_of_forall {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) (i : ℕ) : l.getD i 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => exact Nat.zero_le _
  | some x => exact h x (List.mem_of_getElem? hi)

/-- The children's charges, each within `M`. -/
theorem shapes_sum_le {ps : List (ℕ × ℕ)} (f : ℕ → ℕ → ℕ) {M : ℕ} (hf : ∀ μ r, f μ r ≤ M) :
    (ps.map fun p ↦ f p.1 p.2).sum ≤ ps.length * M := by
  have h := List.sum_le_length_nsmul (ps.map fun p ↦ f p.1 p.2) M (by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    exact hf p.1 p.2)
  rwa [List.length_map, smul_eq_mul] at h

/-- `verify_sub`'s instructions of each opcode at the largest opening arm. -/
def childMax : Opcode → ℕ
  | .xor => 98091 | .mulNative => 181054 | .setConstant => 49823 | .deref => 104791
  | .jump => 35720 | .keccak => 10497

theorem childShape_le_childMax (op : Opcode) (μ r : ℕ) :
    (Count.deployedInstrs op).childShape μ r ≤ childMax op := by
  cases op <;> exact getD_le_of_forall (by decide) (μ - 20)

/-- The log of the bound on each opcode's instructions at the deployed limits' caps. -/
def instrLog : Opcode → ℕ
  | .xor => 23 | .mulNative => 24 | .setConstant => 22 | .deref => 23 | .jump => 21 | .keccak => 21

section

variable {s : NodeStatement} {w : NodeWitness}

/-- The fields of `work` the bounds read. -/
theorem work_fields (hlim : DeployedLimits s w) :
    (work s w).declared = s.claims.xmss.length + s.claims.sphincs.length ∧
      (work s w).coverage = coverageSlots w ∧
      (work s w).rawXmss = w.xmssSignatures.length ∧
      (work s w).rawSphincs = w.sphincsSignatures.length ∧
      (work s w).rawDa = (w.daMatrix.map fun _ ↦ 1).getD 0 ∧
      (work s w).rawDaRows = (w.daMatrix.map fun p ↦ p.2.rows.length).getD 0 ∧
      (work s w).rawDaPad = (w.daMatrix.map fun p ↦ LeanDa.paddedRowCount p.2.rows.length).getD 0 ∧
      (work s w).children = w.children.length ∧
      (work s w).childClaims = (w.children.map fun child ↦
        child.statement.claims.xmss.length + child.statement.claims.sphincs.length).sum ∧
      (work s w).childShapes.length = w.children.length :=
  ⟨rfl, B1.Main.planSlots_eq hlim, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [work]⟩

/-- The blob matrix checked directly: at most one, of at most `DA_MAX_ROWS` rows (`LeanDa.maxRows`),
padded to at most `DA_MAX_ROWS`. -/
theorem da_le (hlim : DeployedLimits s w) :
    (w.daMatrix.map fun _ ↦ 1).getD 0 ≤ 1 ∧
      (w.daMatrix.map fun p ↦ p.2.rows.length).getD 0 ≤ guest_const% DA_MAX_ROWS ∧
      (w.daMatrix.map fun p ↦ LeanDa.paddedRowCount p.2.rows.length).getD 0 ≤ guest_const% DA_MAX_ROWS := by
  rcases h : w.daMatrix with _ | p
  · simp
  · have hr : p.2.rows.length ≤ guest_const% DA_MAX_ROWS := hlim.atMostMaxRows p (Option.mem_def.mpr h)
    refine ⟨le_rfl, hr, ?_⟩
    show 2 ^ Nat.clog 2 p.2.rows.length ≤ 2 ^ guest_const% DA_LOG_MAX_ROWS
    exact Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow hr)

/-- The coverage table at the caps. -/
theorem coverageSlots_le (hlim : DeployedLimits s w) : coverageSlots w ≤ 2048 + 512 + 2 ^ 17 := by
  have := hlim.atMost2048Xmss; have := hlim.atMost512Sphincs; have := hlim.atMost2Pow17ChildClaims
  unfold coverageSlots
  omega

/-- The declared claims, at most the claims held (`DeployedLimits.claimsHeldWithMultiplicity`). -/
theorem declared_le (hlim : DeployedLimits s w) :
    s.claims.xmss.length + s.claims.sphincs.length ≤ coverageSlots w := by
  have h1 := hlim.claimsHeldWithMultiplicity.1.length_le
  have h2 := hlim.claimsHeldWithMultiplicity.2.length_le
  simp only [List.length_append, List.length_map, List.length_flatten, List.map_map,
    Function.comp_def] at h1 h2
  simp only [coverageSlots, List.sum_map_add]
  omega

/-- **The deployed budget's words at the caps**, a child charged at the largest arm. -/
theorem words_le (hlim : DeployedLimits s w) :
    (Count.deployedWords deployedBvAt).eval (work s w) ≤ 2 ^ 26 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := work_fields hlim
  obtain ⟨d1, d2, d3⟩ := da_le hlim
  have := declared_le hlim; have := coverageSlots_le hlim
  have := hlim.atMostSixteenChildren; have := hlim.atMost2Pow17ChildClaims
  have := hlim.atMost2048Xmss; have := hlim.atMost512Sphincs
  have hb := shapes_sum_le (ps := (work s w).childShapes) deployedBvAt deployedBvAt_le
  simp only [End.Linear.eval, Count.deployedWords]
  omega

/-- **The deployed budget's instructions of each opcode at the caps**, a child charged at the
largest arm. -/
theorem instrs_le (hlim : DeployedLimits s w) (op : Opcode) :
    (Count.deployedInstrs op).eval (work s w) ≤ 2 ^ instrLog op := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := work_fields hlim
  obtain ⟨d1, d2, d3⟩ := da_le hlim
  have := declared_le hlim; have := coverageSlots_le hlim
  have := hlim.atMostSixteenChildren; have := hlim.atMost2Pow17ChildClaims
  have := hlim.atMost2048Xmss; have := hlim.atMost512Sphincs
  have hb := shapes_sum_le (ps := (work s w).childShapes) (Count.deployedInstrs op).childShape
    (childShape_le_childMax op)
  cases op <;>
    simp only [End.Linear.eval, Count.deployedInstrs, childMax, instrLog] at hb ⊢ <;>
    omega

/-- **The deployed budget's size at the caps is at most `2^30`.** -/
theorem size_le (hlim : DeployedLimits s w) : (deployedBudget deployedBvAt).size (work s w) ≤ 2 ^ 30 := by
  unfold End.Budget.size
  rw [Count.deployedBudget_words]
  simp only [Count.deployedBudget_instrs]
  refine (End.sizeOf_mono (words_le hlim) (instrs_le hlim)).trans ?_
  simp only [End.sizeOf, Memory.logMem, instrLog, guest_logSize, Nat.clog_pow 2 _ (by norm_num)]
  norm_num

/-- **A node within the deployed limits has its coverage table below `2^23`.** -/
theorem _root_.LeanVM.Guest.GuestLimits.of_limits (hlim : DeployedLimits s w) : GuestLimits s w :=
  ⟨hlim, by have := coverageSlots_le hlim; omega⟩

end

/-- **Every node within the deployed limits has a valid execution of the guest**
(`GuestCompleteOnAcceptableChildren`). -/
theorem guest_complete_on_acceptable_children : GuestCompleteOnAcceptableChildren :=
  fun seed s w hrel hlim hok ↦
    guest_complete_numeric seed s w hrel (GuestLimits.of_limits hlim) hok (size_le hlim)

end
end LeanVM.Guest.Budget
