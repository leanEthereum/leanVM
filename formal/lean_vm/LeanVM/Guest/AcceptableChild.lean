/-
  LeanVM.Guest.AcceptableChild

  What the guest program checks of a child (`AcceptableChild`), and the guest program's
  completeness stated with it (`GuestCompleteOnAcceptableChildren`, `GuestChildComplete`): an honest
  child is an acceptable one (`HonestChildren.lean`).
-/

module

public import Statement.LeanVmGuestCompleteness
public import LeanVM.Guest.BatchConsts
import LeanVM.Protocol.Compile.RunPure
import LeanVM.Guest.Coverage
import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts

/-!
# A child the guest program accepts

`Statement/LeanVmGuestCompleteness.lean` states the guest program's completeness for children the
verifier accepts, unless a child's proof exhibits a Keccak-256 collision (`OpeningsCollide`). The
proofs go through what the guest program checks of a child, defined here: `ChildrenProven`'s two
conditions, a stack log at least `20`, a proof stream of at most `STREAM_CAP = 8192` scalars, and
its openings agreeing in the guest program's Merkle caps at every query step of its verifier's run
(`Limits.OpeningsAgree`, `AcceptableChild`).
`GuestCompleteOnAcceptableChildren` is the guest program's completeness on nodes within the
deployed limits whose children are acceptable, for every seed; `Child/Collision.lean` shows that
the children of a node `NodeRelation` admits are acceptable, or a child's proof exhibits a
collision (`Child.acceptableChildren_or_collide`). A child carrying the honest prover's proof
(`HonestChild`) is acceptable too (`GuestChildComplete`, `HonestChildren.lean`).
-/

@[expose] public section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

namespace Coverage

/-- `STREAM_CAP` (`crates/aggregation/src/child.rs`): a child's proof stream is zero-padded to
it. -/
def childStreamCap : ℕ := guest_const% STREAM_CAP

/-- The least stack log the guest program has an opening arm for (`min_execution_stacked_log` of
its `2^19` instructions, `crates/verifier`'s `layout.rs`). -/
def minChildStackLog : ℕ := 20

/-- The deferring verifier's initial state on a child's proof under the node's seed
(`verifyDeferredWith`). -/
def childVerifierStart (seed : Digest) (child : Child) : VerifierProgramState :=
  ⟨⟨keccakF1600 (seedInput seed (statementDigest seed child.statement)), [], none⟩,
    child.proof.stream,
    child.proof.openings, []⟩

end Coverage

namespace Limits

/-- The heap index of the node at `level` (the leaves at `0`) above the leaf `leafPosition` of a
tree of height `depth`. -/
def merkleHeapIndex (depth leafPosition level : ℕ) : ℕ :=
  2 ^ (depth - level) + leafPosition / 2 ^ level

/-- The heap index of the sibling of the node at `level < depth` above the leaf `leafPosition`. -/
def siblingHeapIndex (depth leafPosition level : ℕ) : ℕ :=
  2 * merkleHeapIndex depth leafPosition (level + 1) + (!leafPosition.testBit level).toNat

/-- **The opening `queryOpening` gives the heap node `heapNode` the digest `digest`**: the node is
on its climb, with the climb's digest there, or is the sibling it carries at a level. -/
def OpeningGivesNode (depth : ℕ) (queryOpening : ℕ × Opening) (heapNode : ℕ) (digest : Digest) :
    Prop :=
  (∃ level ≤ depth, heapNode = merkleHeapIndex depth queryOpening.1 level ∧
    digest = climbTo (merkleLeafDigest queryOpening.2.leaf) queryOpening.1
      (queryOpening.2.path.take level)) ∨
  ∃ level < depth, heapNode = siblingHeapIndex depth queryOpening.1 level ∧
    digest = queryOpening.2.path.getD level default

/-- The openings of one tree of height `depth`, each at its position, agree wherever they meet:
the guest program writes each node of a level's Merkle cap once. -/
def OpeningsAgree (depth : ℕ) (queryOpenings : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ queryOpenings, ∀ b ∈ queryOpenings, ∀ heapNode digest digest',
    OpeningGivesNode depth a heapNode digest → OpeningGivesNode depth b heapNode digest' →
      digest = digest'

/-- **The query steps of a run** of the compiled verifier (Keccak-256, Keccak-f[1600]): each
`query` step as its tree's height and its positions, each with its opening in the phase it
consumes. -/
def queryStepsOf {α : Type} : VerifierProgram α → VerifierProgramState → List (ℕ × List (ℕ ×
    Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, state => match state.stream, state.sponge.ground with
    | x :: xs, none =>
      queryStepsOf (k x) { state with
        sponge := Id.run (absorb keccakF1600 state.sponge x dsObserve), stream := xs }
    | _, _ => []
  | .sample k, state =>
    let (c, sponge) := Id.run (squeeze keccakF1600 state.sponge)
    queryStepsOf (k c) { state with sponge := sponge }
  | .grind bits k, state => match state.stream, state.sponge.ground with
    | n :: xs, none =>
      let (pow, sponge) := Id.run (absorbNonce keccakF1600 state.sponge n)
      if powOk bits pow then queryStepsOf k { state with sponge := sponge, stream := xs } else []
    | _, _ => []
  | .commit height width k, state => match state.stream, state.sponge.ground with
    | x0 :: x1 :: xs, none =>
      queryStepsOf k { state with
        sponge :=
          Id.run (absorb keccakF1600
            (Id.run (absorb keccakF1600 state.sponge x0 dsObserve)) x1 dsObserve)
        stream := xs
        roots := state.roots ++ [(digestFromHalves (x0, x1), height, width)] }
    | _, _ => []
  | .query i ps k, state => match state.roots[i]?, state.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) with
      | some rows => (height, ps.zip phase) :: queryStepsOf (k rows) { state with openings := rest }
      | none => []
    | _, _ => []

end Limits

/-- **A child the guest program accepts** under the seed `seed`: what the guest program asks of
each child, `ChildrenProven`'s two conditions and the deployed ones:
* its stack log is at least `20`: the guest program has one opening arm per stack log in
  `[20, 30]`; the verifier admits stack logs from `Whir.minLogStack`;
* its proof stream is at most `STREAM_CAP = 8192` scalars;
* its openings agree in the guest program's Merkle caps: at every query step of its deferring
  verifier, run under the node's seed, the step's openings agree wherever they meet (one tree's
  openings, the honest prover's, agree). -/
structure AcceptableChild (bytecode : List K) (seed : Digest) (child : Child) : Prop where
  /-- Its deferred claim has the bytecode's shape. -/
  deferredClaimShaped : child.statement.deferredClaim.HasBytecodeShape bytecode
  /-- The deferring verifier accepts its proof. -/
  verifies : verifyDeferred bytecode seed (statementDigest seed child.statement) child.freshClaim
    child.proof = true
  /-- Its stack log is at least `20`. -/
  stackLogAtLeastMinimum : ∀ layout r, announcedLayoutAndRate bytecode child.proof.stream = some
      (layout, r) →
    Coverage.minChildStackLog ≤ layout.stackLog
  /-- Its proof stream is at most `STREAM_CAP = 8192` scalars. -/
  streamWithinCap : child.proof.stream.length ≤ Coverage.childStreamCap
  /-- Its openings agree in the guest program's Merkle caps. -/
  capsAgree : ∀ step ∈ Limits.queryStepsOf
      (deferringVerifierProgram child.freshClaim bytecode (statementDigest seed child.statement))
        (Coverage.childVerifierStart seed child),
    Limits.OpeningsAgree step.1 step.2

namespace Completeness

open Coverage

/-- **Every node within the deployed limits has a valid execution of the leanISA guest program**:
for every seed, statement and witness with `NodeRelation`, within the deployed limits
(`DeployedLimits`), every child one the guest program accepts (`AcceptableChild`: at one of its
opening arms, its openings agreeing in the caps), there is a valid execution of the guest program
on the statement's digest of committed size at most `2^30`. Proved by
`LeanVM.Guest.Budget.guest_complete_on_acceptable_children`. -/
abbrev GuestCompleteOnAcceptableChildren : Prop :=
  ∀ (seed : Digest) (statement : NodeStatement) (witness : NodeWitness),
    NodeRelation (bytecodeWords guestProgram) seed statement witness →
    DeployedLimits statement witness →
    (∀ child ∈ witness.children, AcceptableChild (bytecodeWords guestProgram) seed child) →
    ∃ execution : Execution guestProgram,
      ValidExecution guestProgram (PublicInput.ofDigest (statementDigest seed statement))
        execution ∧
      execution.committedSize ≤ 2 ^ 30

/-- **A child carrying an honest proof**: its fresh claim on the bytecode is true, and its proof
is the honest prover's, with the deployed Keccak, of an execution of the guest program on its
statement's digest under the deployed seed. Every such child that `NodeRelation` admits is
acceptable (`acceptableChildren_of_honest`). -/
def HonestChild (child : Child) : Prop :=
  let input := PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) child.statement)
  child.freshClaim.Holds (bytecodeWords guestProgram) ∧
    ∃ (execution : Execution guestProgram) (ρ : ℕ),
      LeanVM.Prover.prove (m := Id) keccakF1600 guestProgram input execution ρ (2 ^ 35) =
        some child.proof

/-- **A child carrying an honest proof is one the guest program accepts** under the deployed seed,
wherever its deferred claim has the bytecode's shape and the deferring verifier accepts its proof
with its fresh claim (`ChildrenProven`'s two conditions). Proved by
`LeanVM.Guest.Budget.guest_child_complete`. -/
def GuestChildComplete : Prop :=
  ∀ child : Child, HonestChild child →
    child.statement.deferredClaim.HasBytecodeShape (bytecodeWords guestProgram) →
    verifyDeferred (bytecodeWords guestProgram) (deployedSeed guestProgram)
      (statementDigest (deployedSeed guestProgram) child.statement) child.freshClaim child.proof =
        true →
    AcceptableChild (bytecodeWords guestProgram) (deployedSeed guestProgram) child

end Completeness

end LeanVM.Guest

end
