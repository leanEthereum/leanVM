import Whir.WHIRNativeSecurity
import Mathlib.Data.Nat.Choose.Cast

/-! Resource-conditional budget for the pinned #552 public-duplex model.

The grouped-message `2^-79` term already includes the production Johnson list
of up to `2^32` candidates; the endpoint is adaptive list binding, not unique
binding or knowledge extraction. We charge the actual ring-switching term,
caller/WHIR allocation count, source attempts, actual duplex coupling, and ordinary Merkle loss.
No proof-of-work multiplier is supplied by this endpoint.

The illustrative caps permit a million attacker-plus-verifier source units,
65536 caller output blocks, `2^32` frozen family entries, a million free root
announcements, and `2^60` total metered public-compression units. The latter
is deliberately generous: the actual envelope is
`A + A*(pathFactor*A) + pathFactor*Mf`. The checked sufficient envelope below
allows `pathFactor ≤ 2^19` and `Mf ≤ 2^32`. These
are finite-experiment query/resource restrictions, NOT wall-clock bounds,
compiler safety, or assertions that every production input satisfies them.
The reachable verifier/path and actual envelope hypotheses are retained.

The resulting checked probability bound remains `2^-42`, not `2^-128`, with
the proved whole-view duplex loss `min 1 ((2*Q^2-Q)/2^256)`. No external mode
security premise remains. The finite random-compression experiment does not
justify deterministic BLAKE2s security or universal deployed #599/#555 source
correspondence; valid caller shapes and reachable resource hypotheses remain. -/
namespace Whir.ConcreteSecurityBudget
open FiatShamirGame DuplexModeGame WHIRPhysicalDriver WHIRPhysicalDriver.Unanchored WHIRSourceChronology
open RawOracleCoupling.Concrete TypedOracleCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Caps apply to different resources: frozen family size is not caller-output
fanout, and source units are not all physically executed compression calls. -/
structure Caps (registry : ProductionRegistry) (Q A cap free : Nat) : Prop where
  nonzero : 1 ≤ Q
  compression : Q ≤ 2^60
  source : A ≤ 2^20
  caller : registry.callerOutputCap ≤ 2^16
  family : cap ≤ 2^32
  roots : free ≤ 2^20

/-- A sufficient, non-circular accounting envelope at the chosen compression
cap. `pathFactor` is the actual caller-output/packet-completion fanout, not
a new security parameter; this lemma does not assume valid inputs have it. -/
theorem backfill_envelope_le (ctx : RawWHIRKeys.Context) (A Mf : Nat)
    (source : A ≤ 2^20) (fanout : WHIRPublicBackfill.pathFactor ctx ≤ 2^19)
    (path : Mf ≤ 2^32) :
    WHIRSourceBackfill.budget ctx A Mf ≤ 2^60 := by
  have h : WHIRSourceBackfill.budget ctx A Mf ≤
      2^20 + (2^20*(2^19*2^20) + 2^19*2^32) := by
    unfold WHIRSourceBackfill.budget
    gcongr
  exact h.trans (by norm_num)

/-- This is the existing native endpoint's RHS, not a second soundness ledger. -/
def endpointLoss (registry : ProductionRegistry) (Q A cap free : Nat) : ℚ :=
  WHIRObservableSecurity.romBound registry.publicRegistry A cap + duplexModeLoss Q +
    WHIRSourceMerkleSecurity.loss Q free

/-- Nonnegativity of the actual endpoint, needed to diagnose its concrete
full-view replacement rather than claiming a PCS attack. -/
theorem endpointLoss_nonneg (registry : ProductionRegistry) (Q A cap free : Nat)
    (nonzero : 1 ≤ Q) : 0 ≤ endpointLoss registry Q A cap free := by
  have eps := WHIRRawROM.epsilon_nonneg cap
  have hQone : (1 : ℚ) ≤ Q := by exact_mod_cast nonzero
  have hsub : (0 : ℚ) ≤ Q-1 := sub_nonneg.mpr hQone
  unfold endpointLoss WHIRObservableSecurity.romBound duplexModeLoss
    WHIRSourceMerkleSecurity.loss PublicMerkleProbability.bound
  positivity

/-- Both maxima are computed from the actual 56 production schedules. -/
theorem schedule_depths : RawWHIRKeys.maxDepth = 40 ∧
    WHIRSourceRootPolicy.productionDepth = 40 := by
  decide +kernel

/-- Full rational expression obtained by unfolding the existing endpoint.
The source-attempt factor is `A+1`, not a proof-of-work improvement. -/
theorem endpointLoss_eq (registry : ProductionRegistry) (Q A cap free : Nat) :
    endpointLoss registry Q A cap free =
      min 1 ((((40 + registry.callerOutputCap) * (A+1) : Nat) : ℚ) *
          ((1 : ℚ)/2^79 + WHIRFiatShamir.ringCharge cap)) +
      min 1 ((2 * (Q.choose 2 : ℚ) + (Q : ℚ) * Q) / (2^256 : ℚ)) +
      ((Q : ℚ) * ((Q+1) * (free+(Q+1)*41) : Nat) + 2*Q*(Q-1)) / 2^256 := by
  simp only [endpointLoss, WHIRObservableSecurity.romBound,
    allocationBudget, WHIRCallerRegistry.context, ProductionRegistry.publicRegistry,
    schedule_depths.1, WHIRRawROM.epsilon, duplexModeLoss, WHIRSourceMerkleSecurity.loss,
    WHIRSourceMerkleSecurity.rootBudget, PublicMerkleProbability.bound, schedule_depths.2]

/-- Exact polynomial whole-view mode coefficient, including the sharp linear
correction. The source-attempt and ordinary Merkle terms are unchanged. -/
theorem endpointLoss_expansion (registry : ProductionRegistry) (Q A cap free : Nat) :
    endpointLoss registry Q A cap free =
      min 1 ((((40 + registry.callerOutputCap) * (A+1) : Nat) : ℚ) *
          ((1 : ℚ)/2^79 + WHIRFiatShamir.ringCharge cap)) +
      min 1 ((2 * (Q : ℚ)^2 - Q) / (2^256 : ℚ)) +
      ((Q : ℚ) * ((Q+1) * (free+(Q+1)*41) : Nat) + 2*Q*(Q-1)) / 2^256 := by
  have coefficient : 2 * (Q.choose 2 : ℚ) + (Q : ℚ) * Q = 2 * (Q : ℚ)^2 - Q := by
    rw [Nat.cast_choose_two ℚ Q]
    ring
  simpa only [coefficient] using endpointLoss_eq registry Q A cap free

/-- Exact ledger at the illustrative caps, not an attacker-success lower
bound or a concrete deployed-system security claim. -/
theorem endpointLoss_at_caps (registry : ProductionRegistry)
    (caller : registry.callerOutputCap = 2^16) :
    endpointLoss registry (2^60) (2^20) (2^32) (2^20) =
      (5712480737351244866976450137972416606804377619 : ℚ) /
        50216813883093446110686315385661331328818843555712276103168 := by
  rw [endpointLoss_expansion, caller]
  norm_num [WHIRFiatShamir.ringCharge]

/-- The family cap's actual list/ring-switching contribution is much smaller
than `2^-79`; the existing `2^32` list factor is not silently discarded. -/
theorem ringCharge_at_cap :
    WHIRFiatShamir.ringCharge (2^32) = (2 : ℚ)/2^128 - 1/2^160 := by
  norm_num [WHIRFiatShamir.ringCharge]

/-- At the caller/source caps, the actual ROM term already exceeds `2^-43`.
Thus 42 is the strongest integral bit bound obtained uniformly from this
ledger at these caps; this is NOT a lower bound on attacker success. -/
theorem capped_rom_exceeds_43 (registry : ProductionRegistry)
    (caller : registry.callerOutputCap = 2^16) :
    (1 : ℚ)/2^43 <
      WHIRObservableSecurity.romBound registry.publicRegistry (2^20) (2^32) := by
  simp only [WHIRObservableSecurity.romBound, allocationBudget,
    WHIRCallerRegistry.context, ProductionRegistry.publicRegistry, schedule_depths.1, caller]
  norm_num [WHIRRawROM.epsilon, WHIRFiatShamir.ringCharge]

/-- Instantiates all three terms of the native endpoint under the stated caps. -/
theorem endpointLoss_le (registry : ProductionRegistry) (Q A cap free : Nat)
    (caps : Caps registry Q A cap free) :
    endpointLoss registry Q A cap free ≤ (1 : ℚ)/2^42 := by
  have allocation : allocationBudget registry.context * (A+1) ≤
      (40+2^16)*(2^20+1) := by
    simp only [allocationBudget, ProductionRegistry.context, WHIRCallerRegistry.context,
      ProductionRegistry.publicRegistry, schedule_depths.1]
    exact Nat.mul_le_mul (Nat.add_le_add_left caps.caller 40)
      (Nat.add_le_add_right caps.source 1)
  have eps : WHIRRawROM.epsilon cap ≤ WHIRRawROM.epsilon (2^32) :=
    add_le_add_right (WHIRFiatShamir.ringCharge_mono caps.family) _
  have rom : WHIRObservableSecurity.romBound registry.publicRegistry A cap ≤
      (((40+2^16)*(2^20+1) : Nat) : ℚ) * WHIRRawROM.epsilon (2^32) := by
    apply (min_le_right _ _).trans
    apply mul_le_mul
    · exact_mod_cast allocation
    · exact eps
    · exact WHIRRawROM.epsilon_nonneg cap
    · positivity
  have mode : duplexModeLoss Q ≤
      (2 * ((2^60 : Nat).choose 2 : ℚ) + (2^60 : ℚ) * 2^60) / 2^256 := by
    apply (min_le_right _ _).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.choose_le_choose 2 caps.compression) (by positivity)
    · have hQ : (Q : ℚ) ≤ (2^60 : ℚ) := by exact_mod_cast caps.compression
      exact mul_le_mul hQ hQ (by positivity) (by positivity)
  have roots : WHIRSourceMerkleSecurity.rootBudget Q free ≤
      (2^60+1)*(2^20+(2^60+1)*41) := by
    unfold WHIRSourceMerkleSecurity.rootBudget
    rw [schedule_depths.2]
    gcongr
    · exact caps.compression
    · exact caps.roots
    · exact caps.compression
  have hQ : (Q : ℚ) ≤ (2^60 : ℚ) := by exact_mod_cast caps.compression
  have hQone : (1 : ℚ) ≤ Q := by exact_mod_cast caps.nonzero
  have merkle : WHIRSourceMerkleSecurity.loss Q free ≤
      (((2^60 : ℚ) * ((2^60+1)*(2^20+(2^60+1)*41) : Nat)) +
        2*(2^60)*(2^60-1)) / 2^256 := by
    unfold WHIRSourceMerkleSecurity.loss PublicMerkleProbability.bound
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply add_le_add
    · exact mul_le_mul hQ (by exact_mod_cast roots) (by positivity) (by positivity)
    · gcongr
  have total := add_le_add (add_le_add rom mode) merkle
  apply total.trans
  norm_num [WHIRRawROM.epsilon, WHIRFiatShamir.ringCharge, Nat.choose_two_right]

/-- Actual native false-acceptance probability in the public RANDOM-compression
experiment. The actual mode coupling is instantiated internally; every original
reachable resource hypothesis and the valid-shape source model remain. -/
theorem random_compression_list_binding [Fintype Coins] [Nonempty Coins]
    {cap : Nat} (registry : ProductionRegistry) (Q a b Mf free : Nat)
    (attackers : Coins → Source cap (Input registry.context Q))
    (before : ∀ coins, Counts a (attackers coins))
    (verifierBudget : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget registry.context Q input.packet ≤ b)
      (erase (attackers coins)))
    (paths : ∀ coins, WHIRSourceBackfill.AllResults
      (fun input => DuplexFraming.pathCost
        (RawWHIRKeys.coordinate registry.context input.packet.val 0) ≤ Mf)
      (erase (attackers coins)))
    (announcements : ∀ coins, WHIRSourceRootPolicy.FreeAnnouncements free
      (WHIRNativeSecurity.sources registry Q attackers coins))
    (envelope : WHIRSourceBackfill.budget registry.context (a+b) Mf ≤ Q)
    (caps : Caps registry Q (a+b) cap free) :
    realProbability registry.iv (WHIRNativeSecurity.adversary registry Q attackers)
      (WHIRNativeEvent.distinguisher registry Q cap) ≤ (1 : ℚ)/2^42 :=
  (WHIRNativeSecurity.random_compression_list_binding registry Q a b Mf free attackers
    before verifierBudget paths announcements envelope).trans
      (endpointLoss_le registry Q (a+b) cap free caps)

/-- No small full-view replacement loss for any class admitting the efficient
one-query known-answer observer. This is not a lower bound on PCS failure. -/
theorem concrete_gap_not_small (Q : Nat) (iv : Digest32) (input : DuplexFraming.Node)
    (loss : ℚ)
    (Allowed : (C : Type) → [Fintype C] → (Output : Type) →
      (C → Program Output) → (View Output → Bool) → Prop)
    (primitive : ConcretePrimitiveGap Q iv loss Allowed) (nonzero : 1 ≤ Q)
    (observer : Allowed Unit Digest32 (knownAnswerAdversary input)
      (knownAnswerDistinguisher input)) :
    ¬ loss ≤ (1 : ℚ)/2^42 := by
  have lower := concretePrimitiveGap_knownAnswer_lower_bound Q iv input loss
    Allowed primitive nonzero observer
  have separation : (1 : ℚ)/2^42 < 1 - 1/(2^256 : ℚ) := by norm_num
  exact not_le_of_gt (separation.trans_le lower)

/-- The complete RHS of the current concrete endpoint also cannot be small
under a full-view class containing the known-answer observer. In particular,
adding the ROM/duplex/Merkle terms cannot repair the replacement premise. -/
theorem concrete_endpoint_not_small (registry : ProductionRegistry)
    (Q A cap free : Nat) (input : DuplexFraming.Node) (primitiveLoss : ℚ)
    (Allowed : (C : Type) → [Fintype C] → (Output : Type) →
      (C → Program Output) → (View Output → Bool) → Prop)
    (primitive : ConcretePrimitiveGap Q registry.iv primitiveLoss Allowed)
    (nonzero : 1 ≤ Q)
    (observer : Allowed Unit Digest32 (knownAnswerAdversary input)
      (knownAnswerDistinguisher input)) :
    ¬ endpointLoss registry Q A cap free + primitiveLoss ≤ (1 : ℚ)/2^42 := by
  intro small
  apply concrete_gap_not_small Q registry.iv input primitiveLoss Allowed
    primitive nonzero observer
  exact (le_add_of_nonneg_left (endpointLoss_nonneg registry Q A cap free nonzero)).trans small

end Whir.ConcreteSecurityBudget
