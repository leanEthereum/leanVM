module

public import LeanVM.Guest.Budget.Count
public import LeanVM.Guest.Complete.Reduce

/-!
# The guest's run within its bounds, from the count

`Count.lean` bounds the count's words, rows and weighted rows by a budget. Here the run: if the
executor's run of the guest uses at most the count's words, steps and weighted table rows
(`RunWithinCount`) and the committed size is the stack's blocks at their tables' heights
(`CommittedOfRows`), a node within a budget of at most `2^24` words has memory at most `2^24`, fewer
than `2^24` steps and committed size at most `2^30`. `Complete/Open.lean` composes them into
`GuestExecutionComplete`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol
open LeanVM.Guest.Completeness LeanVM.Guest.Complete

@[expose] public section

/-- An execution's table rows weighed by each table's committed columns (`xor`, `mul`, `set`,
`deref`, `jump`, `keccak`: `7, 9, 5, 10, 14, 68`, `q_keccak`'s `64` among the last). -/
noncomputable def tableWeighted {program : LeanIsaProgram} (t : Execution program) : ℕ :=
  (List.zipWith (· * ·) [7, 9, 5, 10, 14, 68] t.tableRows).sum

/-- **The committed size from the rows** (open, `Execution.committedSize`'s arithmetic): the
memory's two columns of `2^κ` words, and each table's columns at its height `2^⌈log₂ rows⌉ ≤ 2 rows`,
or at its floor (`KECCAK`'s `2^9`) or `1` for an empty table. -/
def CommittedOfRows : Prop :=
  ∀ t : Execution guestProgram, t.committedSize ≤ 2 ^ (t.logMemorySize + 1) + 2 * tableWeighted t + 2 ^ 16

/-- **The executor's run within the count** (open): on every node `GuestExecutionComplete` covers,
the run returns an execution whose memory has at most the count's words, whose steps are at most
its rows and whose weighted table rows at most its weighted rows, the children's shapes read by
`shape`; or some child's openings collide. -/
def RunWithinCount (shape : Child → ChildShape) : Prop :=
  ∀ (statement : NodeStatement) (witness : NodeWitness),
    NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness →
    DeployedLimits statement witness →
    (∃ t, guestExecution guestProgram statement witness = .ok t ∧
      (∀ k, 23 ≤ k → nodeWords (NodeItems.ofWitness shape statement witness) ≤ 2 ^ k → t.logMemorySize ≤ k) ∧
      t.stepCount ≤ nodeRows (NodeItems.ofWitness shape statement witness) ∧
      tableWeighted t ≤ nodeWeighted (NodeItems.ofWitness shape statement witness)) ∨
    ∃ child ∈ witness.children, OpeningsCollide child.proof

/-- **The declared claims fit the slots**: `NodeRelation`'s sub-multisets. -/
theorem declaredFit_of_held {shape : Child → ChildShape} {statement : NodeStatement}
    {witness : NodeWitness} (h : SignatureClaimsHeld statement witness) :
    (NodeItems.ofWitness shape statement witness).DeclaredFit := by
  obtain ⟨-, -, hx, hs⟩ := h
  have hx := hx.length_le
  have hs := hs.length_le
  simp only [List.length_append, List.length_map, List.length_flatten, List.map_map,
    Function.comp_def] at hx hs
  simp only [NodeItems.DeclaredFit, NodeItems.holders, NodeItems.childClaims, NodeItems.ofWitness,
    List.map_map, Function.comp_def]
  rw [List.sum_map_add]
  omega

end

end LeanVM.Guest.Budget
