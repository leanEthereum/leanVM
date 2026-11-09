/-
  LeanVM.Guest.B1.VerifySub.CompleteSpec

  `verify_sub`'s completeness statement (G7's target, 2026-10-23): one honest child at a time,
  in the placed form `CompleteAtD`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.Limits
public import LeanVM.Guest.Hints
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Bits.Log2Placed
public import LeanVM.Guest.AcceptableChild

/-!
# `verify_sub` is complete

`verify_sub_complete_Spec bytecode`: for every honest child `c` of a node under the seed `seed` —
its deferred claim shaped for the bytecode, its stack at least `2^minChildStackLog`, its stream at most
`childStreamCap` words, the deferring verifier accepting it while refusing a zero challenge where the
guest divides (`Limits.verifyDeferredNZ`), and its openings agreeing per batch over the run's query
steps (`Limits.queryStepsOf`) — and every caller's words `Lin` holding the exponent table at
`g^sqE` (`log2Lin`) and the child's fixed cells at `out = g^outE` (write-once:
`verify_sub` writes them there), `verify_sub` on the statement's and the seed's cells, `g^sqE`,
`out` is complete at every frame pointer (`CompleteAtD`), returning nothing, for
certificates whose runs fit their frames with consecutive cells (`Lift.RunsFit`,
`RunsConsec`). Its own buffers hold `Hints.childHints bytecode seed c`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main

@[expose] public section

/-- **`verify_sub` is complete on every honest child** (G7's target). -/
def verify_sub_complete_Spec (bytecode : List K) : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ), Lift.RunsFit fs cert → RunsConsec cert →
  ∀ (seed : Digest) (c : Child) (sqE outE : ℕ) (Lin : Main.Layout) (κ : ℕ), 16 ≤ κ →
    c.statement.deferredClaim.HasBytecodeShape bytecode →
    (∀ layout r, Verifier.announcedLayoutAndRate bytecode c.proof.stream = some (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog) →
    c.proof.stream.length ≤ Coverage.childStreamCap →
    Limits.verifyDeferredNZ bytecode seed (statementDigest seed c.statement) c.freshClaim c.proof = true →
    (∀ b ∈ Limits.queryStepsOf (deferringVerifierProgram c.freshClaim bytecode (statementDigest seed c.statement))
      (Coverage.childVerifierStart seed c), Limits.OpeningsAgree b.1 b.2) →
    (∀ q ∈ log2Lin sqE, q ∈ Lin) →
    (outE, DeferredClaim.cells c.freshClaim) ∈ Lin →
    CompleteAtD fs cert κ "verify_sub" Lin
      [(digestHalves (statementDigest seed c.statement)).1,
        (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
        (digestHalves seed).2, ofK (addressOfIndex sqE), ofK (addressOfIndex outE)] (Returns [])

end
end LeanVM.Guest.B1.VerifySub
