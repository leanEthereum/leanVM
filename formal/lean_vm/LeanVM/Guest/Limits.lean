/-
  LeanVM.Guest.Limits

  Where `NodeRelation` admits witnesses the deployed guest cannot run: the deployed limits, the
  children's openings agreeing in the guest's Merkle caps, and no zero Fiat-Shamir challenge where
  the guest divides. The hypotheses of the guest's completeness.
-/

module

public import LeanVM.Guest.Hints
public import LeanVM.Protocol.Verifier.DeferredShape
public import Statement.LeanVmGuest
public import LeanVM.Guest.NZProgram
public import LeanVM.Guest.AcceptableChild

/-!
# The limits of the guest's completeness

`NodeRelation bytecode seed s w` (`Statement/LeanVmGuest.lean`) admits witnesses on which the deployed guest
(`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM main `40f877dc`, `G:N` its lines) does
not run to completion. Completeness assumes two hypotheses beside `NodeRelation`, each a precise
predicate on the witness:

* **`DeployedLimits s w`, the deployed limits** of the node: the guest's fixed capacities and range
  checks, which the Spec does not have (at most `16` children, ...; listed at the structure). An
  honest prover within them is never refused, and `aggregate_with_stats` refuses to aggregate
  outside most of them. The guest's proofs take them with the coverage table below `2^20`
  (`GuestLimits`), which `CoveredNode` gives.
* **`ChildrenOk bytecode seed w`, every child one the guest accepts** (`AcceptableChild`, `LeanVM/Guest/AcceptableChild.lean`): besides
  `NodeRelation`'s conditions, a child's stack log at least `22` and its proof stream at most `8192`
  scalars; its openings agree in the guest's Merkle caps (the guest writes each level's Merkle
  cap once, so two openings of one query step meeting at a node of the tree must give it one
  digest; one tree's openings agree; two that disagree at a node give a Keccak-256 collision, an
  argument in prose, not proved here); and no zero challenge where the guest divides (the guest
  computes `μ = 1/λ` for each WHIR level's batching challenge `λ`, G:1400, and the basis
  coefficients `(1 + c)/(c·inv)` for the fold and tail challenges `c`, G:1709, G:1714).

The coverage table's size (`coverageSlots`) is the number of claims made; an honest run lays it out by `Coverage.coveragePlan` (`planSlots`, equal to it under `DeployedLimits`: `B1/Main/Plan.lean`'s `planSlots_eq`). The guest's proofs take it below `2^20` (`GuestLimits`, every count of `meta` and of a child's lists at most it), which `CoveredNode` gives (`coverageSlots_lt_of_coveredNode`).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

open Limits

/-! ## The deployed limits and the coverage table -/

/-- **The deployed limits, the coverage table below `2^20`**: the bound on `coverageSlots` the
guest's proofs use (every count of `meta` and of a child's lists is at most it), which
`CoveredNode` gives (`coverageSlots_lt_of_coveredNode`). -/
structure GuestLimits (statement : NodeStatement) (witness : NodeWitness) : Prop
    extends DeployedLimits statement witness where
  /-- The coverage table below `2^20`. -/
  coverageSlotsBelow2Pow20 : coverageSlots witness < 2 ^ 20

/-- **A covered node's coverage table is below `2^20`**: each family of `CoveredNode` bounds it by
at most `2^15`. -/
theorem coverageSlots_lt_of_coveredNode {witness : NodeWitness}
    (h : Completeness.CoveredNode witness) : coverageSlots witness < 2 ^ 20 := by
  unfold Completeness.CoveredNode at h
  rcases h with ⟨-, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ |
    ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> omega

/-- The deployed limits of a covered node. -/
theorem GuestLimits.of_coveredNode {statement : NodeStatement} {witness : NodeWitness}
    (hl : DeployedLimits statement witness) (h : Completeness.CoveredNode witness) :
    GuestLimits statement witness :=
  ⟨hl, coverageSlots_lt_of_coveredNode h⟩

/-- Every child's signature lists below `2^20`: each at most the coverage table's size. -/
theorem GuestLimits.childClaimListsBelow2Pow20 {statement : NodeStatement} {witness : NodeWitness}
    (limits : GuestLimits statement witness) :
    ∀ child ∈ witness.children,
      child.statement.claims.xmss.length < 2 ^ 20 ∧ child.statement.claims.sphincs.length < 2 ^ 20 := by
  intro child hchild
  have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun child : Child ↦
    child.statement.claims.xmss.length + child.statement.claims.sphincs.length) hchild)
  have h2 := limits.coverageSlotsBelow2Pow20
  unfold coverageSlots at h2
  omega

/-! ## The children's hypotheses -/

/-- **Every child is one the guest accepts.** -/
abbrev ChildrenOk (bytecode : List K) (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children, AcceptableChild bytecode seed c

/-! ## What `NodeRelation` gives of the children's fresh claims -/

end
end LeanVM.Guest
