/-
  LeanVM.Guest.B1.Main.VerifySubGoals

  What `verify_sub`'s completeness asks of a child, and the bounds on a child's announced shape.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5TB
public import LeanVM.Guest.B1.Main.MainGoalsDvT
public import LeanVM.Guest.B1.Main.MainCoverLemmas
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Facts.Guest
public import LeanVM.Guest.B1.VerifySub.CompleteSpec
public import LeanVM.Guest.B1.Whir.Split
public import LeanVM.Guest.B1.VerifySub.Segments
public import LeanVM.Guest.ChildShape

/-!
# The children's `verify_sub` calls

`VsChildOk bytecode seed c`: what `verify_sub`'s completeness asks of a child. `childShape_bounds`: every child's
announced stack log is in `[20, 30]` and its rate in `[1, 4]`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits ChildrenOk)
open LeanVM.Guest.B1 (CompleteAtDTB Returns)
open LeanVM.Guest.B1.VerifySub (vsExpLin)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- What `verify_sub`'s completeness asks of a child `c` under the seed `seed`: its announced stack
log at least `22`, its stream within the cap, its deferring verifier accepting, and its openings
agreeing in the caps. -/
def VsChildOk (bytecode : List K) (seed : Digest) (c : Child) : Prop :=
  (∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog) ∧
    c.proof.stream.length ≤ Coverage.childStreamCap ∧
    verifyDeferred bytecode seed (statementDigest seed c.statement) c.freshClaim c.proof = true ∧
    ∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode
      (statementDigest seed c.statement)) (Coverage.childVerifierStart seed c),
      Limits.OpeningsAgree b.1 b.2

/-- `exponent_tables`' tables are `vsExpLin`'s. -/
theorem etL_eq (fs : String → ℕ) (fp : ℕ) (d : MainData) :
    vsExpLin (etB fs (mK0 d fs fp)) = etL d fs fp := rfl

/-- **Every child's announced stack log is in `[20, 30]` and its rate in `[1, 4]`** (`child_segments`). -/
theorem childShape_bounds (hbl : bytecode.length = 2 ^ 23) (hok : ChildrenOk bytecode seed w) {ch : Child}
    (hch : ch ∈ w.children) :
    20 ≤ (childShape bytecode ch).1 ∧ (childShape bytecode ch).1 ≤ 30 ∧
      1 ≤ (childShape bytecode ch).2 ∧ (childShape bytecode ch).2 ≤ 4 := by
  obtain ⟨S⟩ := VerifySub.child_segments hbl seed ch (hok _ hch).stackLogAtLeastMinimum (hok _ hch).verifies
    (hok _ hch).capsAgree
  rw [childShape_of S.hann]
  exact ⟨S.hmu20, S.hmu30, S.hr1, S.hr4⟩

end
end LeanVM.Guest.B1.Main
