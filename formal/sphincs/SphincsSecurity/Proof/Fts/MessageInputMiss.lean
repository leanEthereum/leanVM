import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.MessagePrehit
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_4 : SampleableType Randomness := SampleableType.ofFintype Randomness

theorem uniform_randomness_messageInput_cacheHit_eq_count
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output |
      ($ᵗ Randomness : ProbComp Randomness)] =
      cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSet cache key.parameter key.root message
  let embedding : (targets : Set Randomness) ↪ fiber :=
    ⟨fun randomness =>
      ⟨⟨tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness.1),
          Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
        (Classical.choose_spec (Finset.mem_filter.mp randomness.2).2), ⟨randomness.1, rfl⟩⟩,
      fun left right heq => Subtype.ext <|
        (messageDigestPayload_injective key.root <|
          (tweakableHashInput_injective key.parameter (by trivial) (by trivial) <|
            congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
  have hsurjective : Function.Surjective embedding := by
    rintro ⟨⟨input, output⟩, hcached, randomness, hinput⟩
    change input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness) at hinput
    subst input
    have hh : hit randomness := ⟨output, hcached⟩
    let target : (targets : Set Randomness) := ⟨randomness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    refine ⟨target, Subtype.ext ?_⟩
    have hout := Option.some.inj ((Classical.choose_spec (Finset.mem_filter.mp target.2).2).symm.trans hcached)
    exact Sigma.ext (by rfl) (heq_of_eq hout)
  have hcard : (targets.card : ENNReal) = cachedMessageEntryCount cache key.parameter key.root message := by
    have h := Set.encard_congr (Equiv.ofBijective embedding ⟨embedding.injective, hsurjective⟩)
    simpa only [cachedMessageEntryCount, fiber, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      congrArg ENat.toENNReal h
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ = _
  rw [hcard]

noncomputable def messageInputMissProbability (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun randomness : Randomness => cache (tweakableHashInput key.parameter .message
    (messageDigestPayload key.root message randomness)) = none | ($ᵗ Randomness : ProbComp Randomness)]

theorem messageInputMissProbability_eq_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageInputMissProbability key message cache =
      1 - cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let miss : Randomness → Prop := fun randomness => cache (tweakableHashInput key.parameter .message
    (messageDigestPayload key.root message randomness)) = none
  have hnot : Pr[fun randomness => ¬ miss randomness | ($ᵗ Randomness : ProbComp Randomness)] =
      cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    apply Eq.trans ?_ (uniform_randomness_messageInput_cacheHit_eq_count key message cache)
    apply probEvent_congr'
    · intro randomness _
      exact Option.ne_none_iff_exists'
    · rfl
  have h := probEvent_compl ($ᵗ Randomness : ProbComp Randomness) miss
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  have heq := ENNReal.eq_sub_of_add_eq probEvent_ne_top h
  rw [hnot] at heq
  exact heq

end SphincsSecurity.Concrete
