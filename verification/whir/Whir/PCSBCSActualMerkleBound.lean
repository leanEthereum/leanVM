import Whir.PCSBCSSourcePrimitiveRootBudget

/-! Actual physical-query target admission, including adaptive anchor headers.
The target cap is derived from the public input scanner, not assumed or charged
through a construction ancestry ledger. The bound is an exact Q-expression. -/
set_option autoImplicit false
namespace Whir.PCSBCSActualMerkleBound
open Concrete Protocol FiatShamirGame DuplexFraming DuplexPublicSimulator
open PCSBCSSourcePrimitiveRootBudget PCSBCSMerkleQueryLog

variable (p : ParameterBounds.Profile) (Q : Nat)
    (layout : PublicLog → Node → WHIRCallerClaims.CallerLayout)
    (saved : PublicLog → Node → AnchoredHeaderCodec.Record)
    (entry : PublicLog → Node → FramedHistory)
    (answers : PublicLog → Node → FiatShamirGame.Coordinate → Digest32)
    (headers : PublicLog → Node → AnchoredHeaderRoots.Public)

theorem source_extraction_probability {T : Type}
    (program : PublicCompressionProgram.Computation T Q) :
    extractionProbability (targets p Q layout saved entry answers headers) program ≤
      PublicMerkleProbability.bound Q (Q*(Q+1)) :=
  multi_extraction_probability (targets p Q layout saved entry answers headers) Q (Q*(Q+1))
    (targets_cap p Q layout saved entry answers headers)
    (targets_grow p Q layout saved entry answers headers) program

theorem exact_merkle_loss (Q : Nat) :
    PublicMerkleProbability.bound Q (Q*(Q+1)) =
      ((Q : ℚ)^3 + 3*(Q : ℚ)^2 - 2*(Q : ℚ))/2^256 := by
  unfold PublicMerkleProbability.bound
  push_cast
  ring

#print axioms source_extraction_probability
#print axioms exact_merkle_loss
end Whir.PCSBCSActualMerkleBound
