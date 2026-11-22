/-
  LeanVM.Guest.BatchConsts

  The statement's batching constants pinned to the guest's: the child count, the grind bits and
  the words of the batching's messages.
-/

module

public import Statement.LeanVmGuestCompleteness
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts

/-!
# The batching's constants

`Statement/LeanVmGuestBatching.lean` writes `maxRecursions` as a literal and derives the batching's
grinds from it and from `grindingBits`. Each is pinned here to the guest's constant, which
`guest-export` writes from leanVM's sources, so a change to `MAX_RECURSIONS`, to `grinding_bits` or
to the round's degree fails the build here: `MAX_RECURSIONS`, `BATCH_LAM_GRIND_BITS`,
`ROUND2_GRIND_BITS`, and the words the guest reads of `bc_sumcheck_msgs`, `BC_LAM_WORDS` before the
rounds and `BC_ROUND_WORDS` a round, which the statement's pushes match. The proofs read the current
values through `maxRecursions_eq`, `lambdaGrindNonceCells_eq`, `grindRound_eq`.
-/

@[expose] public section

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Node

theorem maxRecursions_eq_guest : maxRecursions = guest_const% MAX_RECURSIONS := rfl

theorem batchLambdaGrindBits_eq_guest : batchLambdaGrindBits = guest_const% BATCH_LAM_GRIND_BITS := by
  decide

theorem grindingBits_two_eq_guest : grindingBits 2 = guest_const% ROUND2_GRIND_BITS := by decide

theorem lambdaGrindNonceCells_length_eq_guest (h : BatchingHints) :
    (lambdaGrindNonceCells h).length = guest_const% BC_LAM_WORDS := by
  simp only [lambdaGrindNonceCells, show batchLambdaGrindBits ≠ 0 by decide, ite_false,
    List.length_singleton]

theorem sumcheckRoundCells_length_eq_guest (g : E × E) :
    (sumcheckRoundCells g).length = guest_const% BC_ROUND_WORDS := rfl

theorem maxRecursions_eq : maxRecursions = 16 := rfl

theorem lambdaGrindNonceCells_eq (h : BatchingHints) : lambdaGrindNonceCells h = [h.lambdaGrindNonce] := by
  simp only [lambdaGrindNonceCells, show batchLambdaGrindBits ≠ 0 by decide, ite_false]

theorem sumcheckRoundCells_eq : sumcheckRoundCells = fun g ↦ [g.1, g.2] := rfl

/-- A round's proof of work, of zero bits, is no step. -/
theorem grindRound_eq : VerifierProgram.grindProofOfWork (grindingBits 2) = VerifierProgram.ret () := by
  simp [VerifierProgram.grindProofOfWork, show grindingBits 2 = 0 by decide]

/-- A round of the batching sumcheck, its proof of work of zero bits dropped. -/
theorem sumcheckRoundsProgram_succ (claim : E) (k : ℕ) :
    sumcheckRoundsProgram claim (k + 1) = (do
      let g1 ← VerifierProgram.readScalar
      let gInfinity ← VerifierProgram.readScalar
      let challenge ← VerifierProgram.sampleChallenge
      let rest ← sumcheckRoundsProgram (sumcheckRoundPolynomial claim (g1, gInfinity) challenge) k
      return (challenge :: rest.1, rest.2)) := by
  simp only [sumcheckRoundsProgram, grindRound_eq]
  rfl

end LeanVM.Guest.Batch

namespace LeanVM.Guest

/-- The deployed limits' child count, at `maxRecursions = 16`. -/
theorem DeployedLimits.children_le_sixteen {s : LeanVM.Node.NodeStatement} {w : LeanVM.Node.NodeWitness}
    (hl : DeployedLimits s w) : w.children.length ≤ 16 :=
  hl.atMostSixteenChildren

end LeanVM.Guest

end
