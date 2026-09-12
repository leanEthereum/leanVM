import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestSelectionMass
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_3 : SampleableType Randomness := SampleableType.ofFintype Randomness

attribute [local irreducible] signAttempt signDigestAttemptPrefix

theorem cachedDigestAttemptRate_eq_count (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    cachedDigestAttemptRate key message cache P =
      cachedMessageEntryCountWhere cache key.parameter key.root message P * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output)
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSetWhere cache key.parameter key.root message P
  let embedding : (targets : Set Randomness) ↪ fiber :=
    ⟨fun randomness =>
      ⟨⟨tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness.1),
          Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
        ⟨⟨(Classical.choose_spec (Finset.mem_filter.mp randomness.2).2).1, ⟨randomness.1, rfl⟩⟩,
          (Classical.choose_spec (Finset.mem_filter.mp randomness.2).2).2⟩⟩,
      fun left right heq => Subtype.ext <|
        (messageDigestPayload_injective key.root <|
          (tweakableHashInput_injective key.parameter (by trivial) (by trivial) <|
            congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
  have hsurjective : Function.Surjective embedding := by
    rintro ⟨⟨input, output⟩, ⟨hcached, randomness, hinput⟩, hadmissible, hP⟩
    change input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness) at hinput
    subst input
    have hh : hit randomness := ⟨output, hcached, hadmissible, hP⟩
    let target : (targets : Set Randomness) := ⟨randomness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    refine ⟨target, Subtype.ext ?_⟩
    have hout := Option.some.inj ((Classical.choose_spec (Finset.mem_filter.mp target.2).2).1.symm.trans hcached)
    exact Sigma.ext (by rfl) (heq_of_eq hout)
  have hcard : (targets.card : ENNReal) = cachedMessageEntryCountWhere cache key.parameter key.root message P := by
    have h := Set.encard_congr (Equiv.ofBijective embedding ⟨embedding.injective, hsurjective⟩)
    simpa only [cachedMessageEntryCountWhere, fiber, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      congrArg ENat.toENNReal h
  rw [cachedDigestAttemptRate, probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ = _
  rw [hcard]

noncomputable def exactDigestReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  digestAttemptExpectation digestAttemptLimit key message cache * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹

theorem probEvent_signDigestLoop_prehit_eq_count_mul_exactWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView cache key message P |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] =
      cachedMessageEntryCountWhere cache key.parameter key.root message P * exactDigestReuseWeight key message cache := by
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message cache cache le_rfl,
    cachedDigestAttemptRate_eq_count, exactDigestReuseWeight]
  ring

theorem freshSelection_add_count_exactWeight_add_exhaustion (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache +
      digestExhaustionProbability key message cache = 1 := by
  have h := freshSelection_add_cachedAttempts_add_exhaustion key message cache
  rw [cachedDigestAttemptRate_eq_count] at h
  unfold exactDigestReuseWeight
  convert h using 1; ring

end SphincsSecurity.Concrete
