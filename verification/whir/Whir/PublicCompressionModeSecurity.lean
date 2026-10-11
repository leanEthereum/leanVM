import Whir.PublicCompressionCouplingActualCausalBound

/-! Proved whole-view security of the pinned public-compression simulator.
The causal ledger charges output collisions, public late links, and hidden-state
guesses under the same aggregate `Counts Q` cap. Birthday bounds alone control
only subevents; the whole-view bound is `duplexModeLoss`. -/
namespace Whir.FiatShamirGame

/-- Closed form of the actual mode ledger. Subtraction takes place in ℚ, not ℕ. -/
theorem duplexModeLoss_eq (Q : Nat) :
    duplexModeLoss Q = min 1 ((2 * (Q : ℚ)^2 - (Q : ℚ)) / (2^256 : ℚ)) := by
  unfold duplexModeLoss
  rw [Nat.cast_choose_two]
  congr 1
  ring

theorem duplexModeLoss_nonneg (Q : Nat) : 0 ≤ duplexModeLoss Q := by
  unfold duplexModeLoss
  apply le_min <;> positivity

theorem duplexModeLoss_le_one (Q : Nat) : duplexModeLoss Q ≤ 1 :=
  min_le_left _ _

end Whir.FiatShamirGame

namespace Whir.DuplexPublicSimulator
open FiatShamirGame DuplexModeGame

/-- The actual fixed simulator has a proved unrestricted adaptive whole-view
certificate. No external random-compression distinguishing premise is needed. -/
theorem modeSecurity (Q : Nat) (iv : Digest32) :
    letI := seedFintype
    PublicCompressionModeBound Q Seed State (simulator Q) iv := by
  let _ := seedFintype
  constructor
  intro AdvCoins Result _ adversary counted D
  exact PublicCompressionCouplingActualJoint.actual_modeAdv_le_duplexModeLoss
    Q iv adversary counted D

#print axioms modeSecurity
#print axioms FiatShamirGame.duplexModeLoss_eq
#print axioms FiatShamirGame.duplexModeLoss_nonneg
#print axioms FiatShamirGame.duplexModeLoss_le_one
end Whir.DuplexPublicSimulator
