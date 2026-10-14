import Whir.WHIRNativeEvent
import Whir.WHIRObservableSecurity
import Whir.WHIRSourceMerkleSecurity
import Whir.WHIRPhysicalBinding

namespace Whir.WHIRNativeSecurity
open FiatShamirGame DuplexModeGame WHIRPhysicalDriver WHIRPhysicalDriver.Unanchored WHIRSourceChronology
open RawOracleCoupling.Concrete TypedOracleCompiler
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

variable {Coins : Type} {cap : Nat}

noncomputable local instance : Fintype PrimitiveOracle := PublicMerkleProbability.compressionOracleFintype

def sources (registry : ProductionRegistry) (Q : Nat)
    (attackers : Coins → Source cap (Input registry.context Q)) :=
  fun coins => verifyAfter cap registry Q (attackers coins)

def adversary (registry : ProductionRegistry) (Q : Nat)
    (attackers : Coins → Source cap (Input registry.context Q)) :=
  WHIRObservableSecurity.adversary registry.publicRegistry Q (sources registry Q attackers) select

/-- The physical budget includes the arbitrary attacker, the actual verifier, every repeated raw completion, and the selected terminal path. Bounds range only over reachable attacker outputs. -/
theorem counted (registry : ProductionRegistry) (Q a b Mf : Nat)
    (attackers : Coins → Source cap (Input registry.context Q))
    (before : ∀ coins, Counts a (attackers coins))
    (verifierBudget : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget registry.context Q input.packet ≤ b)
      (erase (attackers coins)))
    (paths : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => DuplexFraming.pathCost (RawWHIRKeys.coordinate registry.context input.packet.val 0) ≤ Mf)
      (erase (attackers coins)))
    (envelope : WHIRSourceBackfill.budget registry.context (a+b) Mf ≤ Q) :
    ∀ coins, DuplexModeGame.Counts Q (adversary registry Q attackers coins) :=
  WHIRObservableSecurity.adversary_counted registry.publicRegistry Q (a+b) Mf
    (sources registry Q attackers) select
    (fun coins => verifyAfter_counted cap registry Q (attackers coins) a b (before coins) (verifierBudget coins))
    (fun coins => verifyAfter_path_bound cap registry Q (attackers coins) Mf (paths coins)) envelope

/-- The bad ordinary-Merkle event is observed on the full shared compression trace, including hidden construction calls. It is used only in the random-compression world, never as the concrete primitive distinguisher. -/
def MerkleFailure (registry : ProductionRegistry) (Q : Nat)
    (attackers : Coins → Source cap (Input registry.context Q))
    (whole : ∀ coins, DuplexModeGame.Counts Q (adversary registry Q attackers coins))
    (C : PrimitiveOracle) (coins : Coins) : Prop :=
  PublicMerkleProbability.FrozenOpeningBad C
    (WHIRSourceRootPolicy.policy registry.publicRegistry Q select (sources registry Q attackers coins))
    (PublicCompressionProgram.toLog (Sampling.execute C
      (PublicCompressionProgram.compile registry.iv (adversary registry Q attackers coins) Q (whole coins))).2)

private theorem real_union_bound [Fintype Coins] [Nonempty Coins]
    (registry : ProductionRegistry) (Q : Nat)
    (attackers : Coins → Source cap (Input registry.context Q))
    (whole : ∀ coins, DuplexModeGame.Counts Q (adversary registry Q attackers coins))
    (reduction : ∀ C coins,
      WHIRNativeEvent.Failure registry Q (runReal C registry.iv (adversary registry Q attackers coins)).view.result →
      WHIRObservableSource.Failure registry.publicRegistry Q select
        (runReal C registry.iv (adversary registry Q attackers coins)).view.result ∨
      MerkleFailure registry Q attackers whole C coins) :
    realProbability registry.iv (adversary registry Q attackers) (WHIRNativeEvent.distinguisher registry Q cap) ≤
      realProbability registry.iv (adversary registry Q attackers)
        (WHIRObservableSecurity.distinguisher registry.publicRegistry Q select) +
      WHIRSourceMerkleSecurity.probability registry.publicRegistry Q (sources registry Q attackers) select whole := by
  classical
  unfold realProbability
  rw [FiatShamirGame.distinguish_average (inferInstance : Fintype (PrimitiveOracle × Coins)),
    FiatShamirGame.distinguish_average (inferInstance : Fintype (PrimitiveOracle × Coins))]
  simp only [WHIRObservableSecurity.average_product (X := PrimitiveOracle) (Y := Coins)]
  rw [RawOracleCoupling.average_comm (X := PrimitiveOracle) (Y := Coins),
    RawOracleCoupling.average_comm (X := PrimitiveOracle) (Y := Coins)]
  unfold WHIRSourceMerkleSecurity.probability PublicMerkleProbability.openingProbability
  rw [← average_add]
  apply average_mono
  intro coins
  rw [← average_add]
  apply average_mono
  intro C
  simp only [WHIRNativeEvent.distinguisher,WHIRObservableSecurity.distinguisher,decide_eq_true_eq]
  change (if WHIRNativeEvent.Failure registry Q
      (runReal C registry.iv (adversary registry Q attackers coins)).view.result then (1 : ℚ) else 0) ≤
    (if WHIRObservableSource.Failure registry.publicRegistry Q select
      (runReal C registry.iv (adversary registry Q attackers coins)).view.result then 1 else 0) +
    (if MerkleFailure registry Q attackers whole C coins then 1 else 0)
  by_cases wrong : WHIRNativeEvent.Failure registry Q
      (runReal C registry.iv (adversary registry Q attackers coins)).view.result
  · rcases reduction C coins wrong with raw | merkle
    · simp only [wrong,raw,↓reduceIte]
      split <;> norm_num
    · simp only [wrong,merkle,↓reduceIte]
      split <;> norm_num
  · simp only [wrong,↓reduceIte]
    split <;> split <;> norm_num

private theorem random_of_reduction [Fintype Coins] [Nonempty Coins]
    (registry : ProductionRegistry) (Q a b Mf free : Nat)
    (attackers : Coins → Source cap (Input registry.context Q))
    (before : ∀ coins, Counts a (attackers coins))
    (verifierBudget : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget registry.context Q input.packet ≤ b)
      (erase (attackers coins)))
    (paths : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => DuplexFraming.pathCost (RawWHIRKeys.coordinate registry.context input.packet.val 0) ≤ Mf)
      (erase (attackers coins)))
    (announcements : ∀ coins, WHIRSourceRootPolicy.FreeAnnouncements free (sources registry Q attackers coins))
    (envelope : WHIRSourceBackfill.budget registry.context (a+b) Mf ≤ Q)
    (reduction : ∀ (whole : ∀ coins, DuplexModeGame.Counts Q (adversary registry Q attackers coins)) C coins,
      WHIRNativeEvent.Failure registry Q (runReal C registry.iv (adversary registry Q attackers coins)).view.result →
      WHIRObservableSource.Failure registry.publicRegistry Q select
        (runReal C registry.iv (adversary registry Q attackers coins)).view.result ∨
      MerkleFailure registry Q attackers whole C coins) :
    realProbability registry.iv (adversary registry Q attackers) (WHIRNativeEvent.distinguisher registry Q cap) ≤
      WHIRObservableSecurity.romBound registry.publicRegistry (a+b) cap + duplexModeLoss Q +
        WHIRSourceMerkleSecurity.loss Q free := by
  have sourceA : ∀ coins, Counts (a+b) (sources registry Q attackers coins) :=
    fun coins => verifyAfter_counted cap registry Q (attackers coins) a b (before coins) (verifierBudget coins)
  have sourceQ : ∀ coins, Counts Q (sources registry Q attackers coins) :=
    fun coins => WHIRObservableSecurity.source_counted registry.publicRegistry Q (a+b) Mf
      (sources registry Q attackers coins) (sourceA coins) envelope
  have finalPaths := fun coins => verifyAfter_path_bound cap registry Q (attackers coins) Mf (paths coins)
  have whole := counted registry Q a b Mf attackers before verifierBudget paths envelope
  have unionBound := real_union_bound registry Q attackers whole (reduction whole)
  have rawBound := WHIRObservableSecurity.random_compression_list_binding registry.publicRegistry Q (a+b) Mf
    (sources registry Q attackers) select sourceA finalPaths envelope
  have merkleBound := WHIRSourceMerkleSecurity.probability_bound registry.publicRegistry Q free
    (sources registry Q attackers) select sourceQ announcements whole
  exact unionBound.trans (add_le_add rawBound merkleBound)

/-- Actual native verification, original CPU/recursion decoding, first-frozen candidates, adaptive public Fiat-Shamir, and ordinary Merkle transport compose in the shared random-compression experiment. The adaptive whole-view public-mode coupling is proved; the remaining premises are reachable source-only resource budgets in the formal valid-shape model, not universal #599/#555 implementation correspondence. -/
theorem random_compression_list_binding [Fintype Coins] [Nonempty Coins]
    (registry : ProductionRegistry) (Q a b Mf free : Nat)
    (attackers : Coins → Source cap (Input registry.context Q))
    (before : ∀ coins, Counts a (attackers coins))
    (verifierBudget : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget registry.context Q input.packet ≤ b)
      (erase (attackers coins)))
    (paths : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => DuplexFraming.pathCost (RawWHIRKeys.coordinate registry.context input.packet.val 0) ≤ Mf)
      (erase (attackers coins)))
    (announcements : ∀ coins, WHIRSourceRootPolicy.FreeAnnouncements free (sources registry Q attackers coins))
    (envelope : WHIRSourceBackfill.budget registry.context (a+b) Mf ≤ Q) :
    realProbability registry.iv (adversary registry Q attackers) (WHIRNativeEvent.distinguisher registry Q cap) ≤
      WHIRObservableSecurity.romBound registry.publicRegistry (a+b) cap + duplexModeLoss Q +
        WHIRSourceMerkleSecurity.loss Q free := by
  apply random_of_reduction registry Q a b Mf free attackers before verifierBudget paths announcements envelope
  intro whole C coins failed
  have sourceA := verifyAfter_counted cap registry Q (attackers coins) a b (before coins) (verifierBudget coins)
  have sourceQ := WHIRObservableSecurity.source_counted registry.publicRegistry Q (a+b) Mf
    (verifyAfter cap registry Q (attackers coins)) sourceA envelope
  exact WHIRPhysicalBinding.nativeFailure_or_frozen registry Q cap C (attackers coins) sourceQ (whole coins) failed

/-- Formal conditional deterministic-BLAKE2s inequality. The full-view primitive
replacement premise is not a standard efficient-adversary hash assumption:
`DuplexModeGame.concretePrimitiveGap_knownAnswer_lower_bound` forces a nearly
unit loss when its class contains the elementary known-answer observer.
No correctness/coverage premise is delegated to this replacement game. -/
theorem concrete_list_binding [Fintype Coins] [Nonempty Coins]
    (registry : ProductionRegistry) (Q a b Mf free : Nat)
    (attackers : Coins → Source cap (Input registry.context Q))
    (before : ∀ coins, Counts a (attackers coins))
    (verifierBudget : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget registry.context Q input.packet ≤ b)
      (erase (attackers coins)))
    (paths : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => DuplexFraming.pathCost (RawWHIRKeys.coordinate registry.context input.packet.val 0) ≤ Mf)
      (erase (attackers coins)))
    (announcements : ∀ coins, WHIRSourceRootPolicy.FreeAnnouncements free (sources registry Q attackers coins))
    (envelope : WHIRSourceBackfill.budget registry.context (a+b) Mf ≤ Q)
    (Allowed : (C : Type) → [Fintype C] → (Output : Type) →
      (C → Program Output) → (View Output → Bool) → Prop)
    (primitiveLoss : ℚ) (primitive : ConcretePrimitiveGap Q registry.iv primitiveLoss Allowed)
    (permitted : Allowed Coins _ (adversary registry Q attackers) (WHIRNativeEvent.distinguisher registry Q cap)) :
    concreteProbability registry.iv (adversary registry Q attackers) (WHIRNativeEvent.distinguisher registry Q cap) ≤
      WHIRObservableSecurity.romBound registry.publicRegistry (a+b) cap + duplexModeLoss Q +
        WHIRSourceMerkleSecurity.loss Q free + primitiveLoss := by
  have randomBound := random_compression_list_binding registry Q a b Mf free attackers
    before verifierBudget paths announcements envelope
  have replaced := (abs_le.mp (primitive Coins _ (adversary registry Q attackers)
    (WHIRNativeEvent.distinguisher registry Q cap) permitted
    (counted registry Q a b Mf attackers before verifierBudget paths envelope))).2
  linarith

end Whir.WHIRNativeSecurity
