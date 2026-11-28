/-
  LeanVM.Guest.Limits

  Where `NodeRelation` admits witnesses the deployed guest cannot run: the deployed limits and the
  children's openings agreeing in the guest's Merkle caps. The hypotheses of the guest's
  completeness.
-/

module

public import LeanVM.Guest.Hints
public import Statement.LeanVmGuest
public import Statement.LeanVmGuestCompleteness
public import LeanVM.Guest.AcceptableChild

/-!
# The limits of the guest's completeness

`NodeRelation bytecode seed s w` (`Statement/LeanVmGuest.lean`) admits witnesses on which the
deployed guest (`guests/lean_ethereum.py`) does not run to completion.
Completeness assumes two hypotheses beside `NodeRelation`, each a precise predicate on the witness:

* **`DeployedLimits s w`, the deployed limits** of the node, which the Spec does not have (listed at
  the structure): at most `16` children, which the guest enforces (`aggregate` refuses more than
  `16` children), the blob matrix's rows, and the memory budget (`NodeWitness.memoryBudget`, linear
  in the children, their claims, the raw signatures and the blob rows, at most `2^24` words), which
  neither the guest nor `aggregate` enforces: a node past it is still accepted, but completeness
  does not cover it. An honest prover within them is never refused. The guest's proofs take them
  with `NodeRelation`'s signature claims held and the coverage table below `2^23` (`GuestLimits`),
  which the budget gives (`46` words a child's claim and at least `1400` a raw signature: fewer
  than `2^19` claims).
* **`ChildrenOk bytecode seed w`, every child one the guest accepts** (`AcceptableChild`,
  `LeanVM/Guest/AcceptableChild.lean`): besides `NodeRelation`'s conditions, a child's stack log at
  least `minChildStackLog` and its proof stream at most `8192` scalars, both from `NodeRelation`'s
  acceptance (`Child/StackLog.lean`, `Child/Stream.lean`); its openings agree in the guest's Merkle
  caps (the guest writes each level's Merkle cap once, so two openings of one query step meeting at
  a node of the tree must give it one digest; one tree's openings agree). Two that disagree at a
  node exhibit a Keccak-256 collision (`OpeningsCollide`), the statement's alternative: with
  `NodeRelation`, `ChildrenOk` holds or a child's proof exhibits one
  (`Child.acceptableChildren_or_collide`, `Child/Accepted.lean`).

The coverage table's size (`coverageSlots`) is the number of claims made; an honest run lays it out
by `Coverage.coveragePlan` (`planSlots`, equal to it under `SignatureClaimsHeld`:
`B1/Main/Plan.lean`'s `planSlots_eq`). The guest's proofs take it below `2^23` (`GuestLimits`, every count of `meta` and
of a child's lists at most it), so below the guest's memory, which is at least `2^23` words
(`Memory.logMem`); the deployed limits' budget gives it (proved for the bus era's caps,
`Budget/Fits.lean`'s `GuestLimits.of_limits`, archived at tag `formal-bus-archive`).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

open Limits

/-! ## The deployed limits and the coverage table -/

/-- **The deployed limits, the signature claims held, the coverage table below `2^23`**: the
multiplicities of the declared claims (`SignatureClaimsHeld`, of `NodeRelation`) and the bound on
`coverageSlots` the guest's proofs use (every count of `meta` and of a child's lists is at most it),
below the guest's memory of at least `2^23` words. -/
structure GuestLimits (statement : NodeStatement) (witness : NodeWitness) : Prop
    extends DeployedLimits statement witness where
  /-- The signature claims held, with their multiplicities. -/
  signatureClaimsHeld : SignatureClaimsHeld statement witness
  /-- The coverage table below `2^23`. -/
  coverageSlotsBelow2Pow23 : coverageSlots witness < 2 ^ 23

/-- Every child's signature lists below `2^23`: each at most the coverage table's size. -/
theorem GuestLimits.childClaimListsBelow2Pow23 {statement : NodeStatement} {witness : NodeWitness}
    (limits : GuestLimits statement witness) :
    ∀ child ∈ witness.children,
      child.statement.claims.xmss.length < 2 ^ 23 ∧ child.statement.claims.sphincs.length < 2 ^ 23 := by
  intro child hchild
  have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun child : Child ↦
    child.statement.claims.xmss.length + child.statement.claims.sphincs.length) hchild)
  have h2 := limits.coverageSlotsBelow2Pow23
  unfold coverageSlots at h2
  omega

/-! ## The children's hypotheses -/

/-- **Every child is one the guest accepts.** -/
abbrev ChildrenOk (bytecode : List K) (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children, AcceptableChild bytecode seed c

end
end LeanVM.Guest
