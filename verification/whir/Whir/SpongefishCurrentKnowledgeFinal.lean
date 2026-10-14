import Whir.SpongefishCurrentRefines
import Whir.SpongefishCurrentHeaderGlue
import Whir.SpongefishCurrentKnowledgeEndpoint

/-! Current #607 basic full-prefix knowledge bound with `Refines` discharged. The `Refines` obligation of `SpongefishCurrentKnowledgeEndpoint.full_knowledge_all` is discharged for every binding message shape by the per-coin caller-data builder of `SpongefishCurrentRefines.builder` with the history reply parser, so the endpoint holds in the ideal-compression model with only static public premises: a nonempty instance, the caller prelude and payload call shapes, and `Supported p (AnchoredSourceCaller.shape layout)` (valid shape whose dimension, batch and rate match the profile). The instance, tag, session IV, caller layout and hint decoder are fixed before the attacker runs. The real event, for SOME received record, is: the caller tape replays and the record binding verifies on the real primitive, the PCS opening is natively accepted (query proof of work, Merkle authentication, anchored equations), and the public straight-line extractor fails on the frozen Root0 image. Caller-side proof of work and caller equations are not required, which only enlarges the event. Completeness of the opening model (acceptance of an honest prover) is not proved here. -/
namespace Whir.SpongefishCurrentKnowledgeFinal
open Concrete FiatShamirGame DuplexModeGame SpongefishPCSRoundFrames
open SpongefishCurrentOpeningAcceptance SpongefishCurrentOpeningProgram SpongefishCurrentKnowledgeEndpoint
set_option autoImplicit false

variable {p : ParameterBounds.Profile} {layout : WHIRCallerClaims.CallerLayout}
local notation "cfg" => ParameterBounds.config p

/-- The caller-data builder of binding message shape `k` for one attacker coin. -/
noncomputable def build (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls : List Call) (decode : Decoder)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram) (k : Nat) :
    SpongefishCurrentRoundPackets.Builder p
      (fullBudget tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) grinding A) iv
      grinding (fullBoundary instanceBytes layout before payloadCalls k) :=
  SpongefishCurrentRefines.builder _ iv grinding (fullBoundary instanceBytes layout before payloadCalls k)
    (SpongefishCurrentHeaderGlue.headerFrames instanceBytes layout before) k instanceBytes layout
    (SpongefishCurrentHistoryReplies.historyReplies grinding
      (fullBoundary instanceBytes layout before payloadCalls k))
    (SpongefishCurrentBCSKnowledge.source (SpongefishCurrentRoundPackets.partition p _ iv grinding
        (fullBoundary instanceBytes layout before payloadCalls k)) iv
      (fullProgram iv tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) decode grinding
        prefixProgram)
      (fullProgram_counted iv tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) decode grinding
        prefixProgram A attacker))

/-- `Refines` holds for every binding message shape and attacker coin. -/
theorem refines_shape
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (iv : Digest32) (tag instanceBytes : List Byte) (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram) (k : Nat) :
    SpongefishCurrentBCSKnowledge.Refines
      (SpongefishCurrentRoundPackets.partition p
        (fullBudget tag instanceBytes layout before payloadCalls
          (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) grinding A) iv
        grinding (fullBoundary instanceBytes layout before payloadCalls k))
      (SpongefishCurrentRoundPackets.model p _ iv grinding
        (fullBoundary instanceBytes layout before payloadCalls k)
        (build iv tag instanceBytes layout before payloadCalls decode grinding prefixProgram A attacker k)) iv
      (fullProgram iv tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) decode grinding
        prefixProgram)
      (fullProgram_counted iv tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) decode grinding
        prefixProgram A attacker)
      (SpongefishCurrentGoodEvent.goodFull (fullBudget tag instanceBytes layout before payloadCalls
        (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k) grinding A) iv
        instanceBytes layout grinding (SpongefishCurrentHeaderGlue.headerFrames instanceBytes layout before)
        (fullBoundary instanceBytes layout before payloadCalls k) k) := by
  have opening := binding_ready instanceBytes
    (before ++ SpongefishCurrentAcceptedJoin.headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls)
    (AnchoredSourceCaller.shape layout) k
  exact SpongefishCurrentRefines.refines_full _ iv grinding _ _ k instanceBytes layout supported tag before
    payloadCalls _ decode prefixProgram _ opening
    (SpongefishCurrentHeaderGlue.headerFrames_le instanceBytes layout before payloadCalls _ _ opening)
    (fun T data col result => SpongefishCurrentHeaderGlue.openingEvents_full _ iv tag instanceBytes layout
      before payloadCalls _ decode grinding prefixProgram _ T data col result)
    (fun T data col result r input accepted root0 rootEq => SpongefishCurrentHeaderGlue.header_full _ iv tag
      instanceBytes layout before payloadCalls _ decode grinding prefixProgram beforeEq _ T data col result _ _
      r input _ accepted root0 rootEq)

open Classical in
/-- The current #607 knowledge bound with `Refines` discharged: the real probability that, for some received record, the caller tape replays with a verified record binding, the PCS opening is natively accepted, and the public straight-line extractor fails on the frozen Root0 image, is at most the sum over the four binding message shapes of `finalBound Q_k = Q_k*((17/32)^56+2^-78) + min(1,(2Q_k^2-Q_k)/2^256) + (Q_k^3+3Q_k^2-2Q_k)/2^256`, where `Q_k` is the aggregate budget of shape `k`: attacker work plus the charged verifier replay and Merkle work. -/
theorem current_knowledge {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) :
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedAnyFull coins.1 iv tag instanceBytes layout before payloadCalls decode grinding
        (prefixProgram coins.2) (fun k => SpongefishCurrentGoodEvent.ExtractionFails grinding
          (AnchoredSourceCaller.shape layout) (SpongefishCurrentHeaderGlue.headerFrames instanceBytes layout before)
          (fullBoundary instanceBytes layout before payloadCalls k.val)
          (fullBudget tag instanceBytes layout before payloadCalls
            (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val) grinding A) iv)
      then (1 : ℚ) else 0) ≤
      ∑ k : Fin 4, SpongefishCurrentBCSKnowledge.finalBound (fullBudget tag instanceBytes layout before
        payloadCalls (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
        grinding A : ℚ) :=
  full_knowledge_all iv tag instanceBytes nonempty layout before payloadCalls beforeEq payloadEq decode grinding
    prefixProgram A attacker (SpongefishCurrentHeaderGlue.headerFrames instanceBytes layout before)
    (fun k coin => build iv tag instanceBytes layout before payloadCalls decode grinding (prefixProgram coin) A
      (attacker coin) k.val)
    (fun k coin => refines_shape supported iv tag instanceBytes before payloadCalls beforeEq decode grinding
      (prefixProgram coin) A (attacker coin) k.val)

/-- Four per-shape budgets at most `B <= 2^64` give at most `B / 2^49` in total. -/
theorem four_shapes (budgets : Fin 4 → Nat) (B : Nat) (cap : B ≤ 2^64) (budget : ∀ k, budgets k ≤ B) :
    ∑ k : Fin 4, SpongefishCurrentBCSKnowledge.finalBound (budgets k : ℚ) ≤ (B : ℚ) / 2^49 := by
  have each (k : Fin 4) : SpongefishCurrentBCSKnowledge.finalBound (budgets k : ℚ) ≤ (B : ℚ) / 2^51 := by
    have within : (budgets k : ℚ) ≤ B := by exact_mod_cast budget k
    have capped : (B : ℚ) ≤ 2^64 := by exact_mod_cast cap
    refine (SpongefishCurrentBCSKnowledge.finalBound_le _ (by positivity) (within.trans capped)).trans ?_
    exact div_le_div_of_nonneg_right within (by positivity)
  refine (Finset.sum_le_sum fun k _ => each k).trans (le_of_eq ?_)
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

open Classical in
/-- Concrete level at the deployed 17-bit query grinding: if every binding message shape has aggregate budget at most `B <= 2^64`, the probability of native acceptance with public extraction failure is at most `B / 2^49` (four shapes, each at most `B / 2^51`). -/
theorem current_knowledge_level {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : Decoder) (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) (B : Nat) (cap : B ≤ 2^64)
    (budget : ∀ k : Fin 4, fullBudget tag instanceBytes layout before payloadCalls
      (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
      (SpongefishCurrentBCSKnowledge.deployedGrinding p) A ≤ B) :
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedAnyFull coins.1 iv tag instanceBytes layout before payloadCalls decode
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) (prefixProgram coins.2)
        (fun k => SpongefishCurrentGoodEvent.ExtractionFails (SpongefishCurrentBCSKnowledge.deployedGrinding p)
          (AnchoredSourceCaller.shape layout) (SpongefishCurrentHeaderGlue.headerFrames instanceBytes layout before)
          (fullBoundary instanceBytes layout before payloadCalls k.val)
          (fullBudget tag instanceBytes layout before payloadCalls
            (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
            (SpongefishCurrentBCSKnowledge.deployedGrinding p) A) iv)
      then (1 : ℚ) else 0) ≤ (B : ℚ) / 2^49 := by
  exact (current_knowledge supported iv tag instanceBytes nonempty before payloadCalls beforeEq payloadEq decode
    (SpongefishCurrentBCSKnowledge.deployedGrinding p) prefixProgram A attacker).trans
    (four_shapes _ B cap budget)

open Classical in
/-- Security level in bits at the deployed grinding: with every per-shape budget (attacker work plus the charged verifier replay and Merkle work, a worst-case charge not evaluated here for deployed layouts) at most `2^(49-λ)`, the probability of the accepted-with-extraction-failure event is at most `2^-λ`. For example per-shape budgets of `2^29` units give `2^-20` and `2^39` units give `2^-10`. -/
theorem current_knowledge_bits {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (before payloadCalls : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : Decoder) (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin)) (bits : Nat) (small : bits ≤ 49)
    (budget : ∀ k : Fin 4, fullBudget tag instanceBytes layout before payloadCalls
      (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
      (SpongefishCurrentBCSKnowledge.deployedGrinding p) A ≤ 2^(49-bits)) :
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedAnyFull coins.1 iv tag instanceBytes layout before payloadCalls decode
        (SpongefishCurrentBCSKnowledge.deployedGrinding p) (prefixProgram coins.2)
        (fun k => SpongefishCurrentGoodEvent.ExtractionFails (SpongefishCurrentBCSKnowledge.deployedGrinding p)
          (AnchoredSourceCaller.shape layout) (SpongefishCurrentHeaderGlue.headerFrames instanceBytes layout before)
          (fullBoundary instanceBytes layout before payloadCalls k.val)
          (fullBudget tag instanceBytes layout before payloadCalls
            (SpongefishCurrentBCSKnowledge.bindingCalls (AnchoredSourceCaller.shape layout) k.val)
            (SpongefishCurrentBCSKnowledge.deployedGrinding p) A) iv)
      then (1 : ℚ) else 0) ≤ 1 / 2^bits := by
  have cap : 2^(49-bits) ≤ 2^64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine (current_knowledge_level supported iv tag instanceBytes nonempty before payloadCalls beforeEq payloadEq
    decode prefixProgram A attacker _ cap budget).trans (le_of_eq ?_)
  have split : (2 : ℚ)^49 = 2^(49-bits) * 2^bits := by
    rw [← pow_add, Nat.sub_add_cancel small]
  push_cast
  rw [split]
  field_simp

#print axioms refines_shape
#print axioms current_knowledge
#print axioms current_knowledge_level
#print axioms current_knowledge_bits

end Whir.SpongefishCurrentKnowledgeFinal
