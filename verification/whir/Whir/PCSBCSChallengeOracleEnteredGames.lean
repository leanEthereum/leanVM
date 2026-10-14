import Whir.PCSBCSChallengeOracleEnteredPartition
import Whir.PCSBCSChallengeOracleGames

/-! Whole-view transport covers all admitted data-valued live prefixes at the
public caller boundary, not just one prefix fixed before the adversary. The
bound is the proved 256-bit mode-coupling loss; it is not PCS knowledge or an
assumed hash-chain compilation theorem. -/
set_option autoImplicit false
namespace Whir.PCSBCSChallengeOracle
open Concrete FiatShamirGame DuplexModeGame

open Classical in
theorem entered_source_atomic_game_bound {AdvCoins R : Type} [Fintype AdvCoins]
    (profile : ParameterBounds.Profile) (Qcompression : Nat) (iv : Digest32)
    (boundary : Nat) (adversary : AdvCoins → Program R)
    (counted : ∀ coins, Counts Qcompression (adversary coins)) (observe : View R → Bool) :
    |realProbability iv adversary observe -
      atomicIdealProbability
        (EnteredPacket.partition (p := profile) (Q := Qcompression) (iv := iv)
          (boundary := boundary)) iv adversary counted observe| ≤ duplexModeLoss Qcompression :=
  actual_source_atomic_game_bound _ iv adversary counted observe

#print axioms entered_source_atomic_game_bound
end Whir.PCSBCSChallengeOracle
