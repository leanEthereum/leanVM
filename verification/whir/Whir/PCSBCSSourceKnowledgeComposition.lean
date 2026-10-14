import Whir.PCSBCSSourceKnowledgeGame
import Whir.PCSBCSActualMerkleBound
import Whir.PublicCompressionProgram
import Whir.WHIRObservableSecurity

/-! Composition for the literal full-path source query budget. Native/source
refinement and the event reduction are explicit codec/trace obligations, not
assumed soundness or a supplied bad-event probability. The Merkle probability
is derived from the actual physical compiler with its causal target scanner.
This is a conditional PCS-only random-compression endpoint, not deployed
BLAKE2s knowledge security or a whole-system numerical security level. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceKnowledgeComposition
open Concrete FiatShamirGame DuplexModeGame DuplexFraming DuplexPublicSimulator
open TypedOracleCompiler PublicCompressionProgram PCSBCSMerkleQueryLog
open PCSBCSSourceKnowledgeGame

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
variable (registry : AnchoredHeaderRoots.Public)

noncomputable def merkleProbability {Coins R : Type} [Fintype Coins]
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins)) : ℚ :=
  average fun coins => average fun C : PrimitiveOracle =>
    if PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p Q boundary registry) []
      (PublicCompressionProgram.primitiveLog C iv (adversary coins) Q (counted coins)) then 1 else 0

theorem merkle_probability_bound {Coins R : Type} [Fintype Coins] [Nonempty Coins]
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins)) :
    merkleProbability (p := p) (iv := iv) (boundary := boundary) registry
      adversary counted ≤ ((Q : ℚ)^3+3*(Q : ℚ)^2-2*(Q : ℚ))/2^256 := by
  unfold merkleProbability
  have each (coins : Coins) := PublicMerkleProbability.random_compression_bound
    (PCSBCSSourcePrimitiveRootBudget.targets p Q boundary registry) Q (Q*(Q+1))
    (PCSBCSSourcePrimitiveRootBudget.targets_cap p Q boundary registry)
    (PublicCompressionProgram.compile iv (adversary coins) Q (counted coins))
  simp only [PublicMerkleProbability.alarm_trace] at each
  have bound := average_mono each
  rw [average_const,PCSBCSActualMerkleBound.exact_merkle_loss] at bound
  exact bound

/-- A pointwise reduction to the shared primitive alarm on the complete physical
trace, including collisions unrelated to a frozen opening and all verifier calls. -/
def Reduction {Coins R : Type} (adversary : Coins → Program R)
    (counted : ∀ coins, Counts Q (adversary coins))
    (failure good : View R → Bool) : Prop :=
  ∀ C coins, failure (runReal C iv (adversary coins)).view = true →
    good (runReal C iv (adversary coins)).view = true ∨
    PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p Q boundary registry) []
      (PublicCompressionProgram.primitiveLog C iv (adversary coins) Q (counted coins)) = true

private theorem real_union_bound {Coins R : Type} [Fintype Coins] [Nonempty Coins]
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins))
    (failure good : View R → Bool)
    (reduction : Reduction (p := p) (iv := iv) (boundary := boundary) registry
      adversary counted failure good) :
    realProbability iv adversary failure ≤ realProbability iv adversary good +
      merkleProbability (p := p) (iv := iv) (boundary := boundary) registry
        adversary counted := by
  classical
  unfold realProbability
  rw [distinguish_average (inferInstance : Fintype (PrimitiveOracle × Coins)),
    distinguish_average (inferInstance : Fintype (PrimitiveOracle × Coins))]
  simp only [WHIRObservableSecurity.average_product]
  rw [RawOracleCoupling.average_comm (X := PrimitiveOracle) (Y := Coins),
    RawOracleCoupling.average_comm (X := PrimitiveOracle) (Y := Coins)]
  unfold merkleProbability
  rw [← average_add]
  apply average_mono
  intro coins
  rw [← average_add]
  apply average_mono
  intro C
  by_cases failed : failure (runReal C iv (adversary coins)).view = true
  · rcases reduction C coins failed with raw | merkle
    · simp only [failed,raw,↓reduceIte]
      split <;> norm_num
    · simp only [failed,merkle,↓reduceIte]
      split <;> norm_num
  · simp only [failed,Bool.false_eq_true,↓reduceIte]
    split <;> split <;> norm_num

/-- Explicit separate q56 RBR, 256-bit coupling, and 256-bit Merkle terms.
Refinement must be proved for the actual supported source observer before this
can be read as verifier acceptance/extraction failure. -/
theorem random_compression_failure_probability {Coins R : Type}
    [Fintype Coins] [Nonempty Coins] (layout : WHIRCallerClaims.CallerLayout)
    (adversary : Coins → Program R) (counted : ∀ coins, Counts Q (adversary coins))
    (failure good : View R → Bool)
    (refines : ∀ coins, ObserverRefines (p := p) (iv := iv) (boundary := boundary)
      layout (adversary coins) (counted coins) good)
    (reduction : Reduction (p := p) (iv := iv) (boundary := boundary) registry
      adversary counted failure good) :
    realProbability iv adversary failure ≤
      (Q : ℚ)*PCSRoundByRoundKnowledge.rbrError + duplexModeLoss Q +
      ((Q : ℚ)^3+3*(Q : ℚ)^2-2*(Q : ℚ))/2^256 := by
  have union := real_union_bound registry
    adversary counted failure good reduction
  have raw := random_compression_observer_probability layout adversary counted good refines
  have merkle := merkle_probability_bound (p := p) (iv := iv) (boundary := boundary)
    registry adversary counted
  linarith

#print axioms merkle_probability_bound
#print axioms random_compression_failure_probability
end Whir.PCSBCSSourceKnowledgeComposition
