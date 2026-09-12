import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.PrefixByteAction
import SphincsSecurity.Proof.Residual.ResidualByteExecution
namespace SphincsSecurity.Concrete.CanonicalProbeRouting

theorem charge_probes_mono (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (input : HashInput)
    (memory : ExternalMemory) : memory.probes ≤ (charge parameter words disclosed known input memory).probes := by
  unfold charge
  exact Nat.le_add_right _ _

end SphincsSecurity.Concrete.CanonicalProbeRouting

namespace SphincsSecurity.Concrete.ResidualByteAction

open CanonicalProbeRouting HiddenLabelObservation
attribute [local instance] Classical.propDecidable

theorem freshPrefix_probe_route (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (input row : inputs)
    (test : Probe CanonicalCoordinate)
    (haction : freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows input = .probe row test) :
    route parameter words disclosed known input.val = .probe test := by
  unfold freshPrefix at haction
  cases hroute : route parameter words disclosed known input.val with
  | outside =>
      rw [hroute] at haction
      cases hrow : knownEncodingRowAt parameter inputs hencoding known input with
      | none => simp only [hrow, Option.elim_none] at haction; cases haction
      | some index => simp only [hrow, Option.elim_some] at haction; split at haction <;> cases haction
  | canonical position => rw [hroute] at haction; cases haction
  | probe actual =>
      rw [hroute] at haction
      cases haction
      rfl

end SphincsSecurity.Concrete.ResidualByteAction

namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def HiddenCandidateBound (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    {inputs : Finset HashInput} (state : State inputs) : Prop :=
  ∀ coordinate, CanonicalCoordinate.Hidden words disclosed coordinate →
    2 ^ digestBits ≤ (state.candidates coordinate).card + state.memory.probes

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem hashQueryResult_candidateCost_mono (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs)
    (hcharge : ∀ row test, actions input = .probe row test → route parameter words disclosed known input.val = .probe test)
    (coordinate : CanonicalCoordinate) :
    (state.candidates coordinate).card + state.memory.probes ≤
      ((hashQueryResult parameter inputs words disclosed known actions actual seed input state).2.candidates coordinate).card +
        (hashQueryResult parameter inputs words disclosed known actions actual seed input state).2.memory.probes := by
  have hmono := charge_probes_mono parameter words disclosed known input.val state.memory
  cases hcache : state.memory.cache input.val with
  | some answer =>
      simpa only [hashQueryResult, prepare, hcache, executeResult] using Nat.add_le_add_left hmono _
  | none =>
      cases haction : actions input with
      | known answer =>
          simpa only [hashQueryResult, prepare, hcache, haction, executeResult, storeReply] using Nat.add_le_add_left hmono _
      | read row =>
          simpa only [hashQueryResult, prepare, hcache, haction, executeResult, readState, environment, storeReply] using
            Nat.add_le_add_left hmono _
      | probe row test =>
          have hpaid : (charge parameter words disclosed known input.val state.memory).probes = state.memory.probes + 1 := by
            simp only [charge, hcache, hcharge row test haction]
          simp only [hashQueryResult, prepare, hcache, haction, executeResult]
          cases hrow : state.rows row with
          | some answer =>
              simp only [readState, environment, storeReply, hpaid]
              omega
          | none =>
              dsimp only
              split
              · have hcard := test.card_lower state.candidates (seed row) coordinate
                simp only [probeState, environment, storeReply, hpaid]
                omega
              · simp only [stoppedState, environment, hpaid]
                omega

theorem hashQueryResult_hiddenCandidateBound (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hbound : HiddenCandidateBound words disclosed state)
    (hcharge : ∀ row test, actions input = .probe row test → route parameter words disclosed known input.val = .probe test) :
    HiddenCandidateBound words disclosed
      (hashQueryResult parameter inputs words disclosed known actions actual seed input state).2 := by
  intro coordinate hhidden
  exact (hbound coordinate hhidden).trans
    (hashQueryResult_candidateCost_mono parameter inputs words disclosed known actions actual seed input state hcharge coordinate)

omit actions in
theorem prefixHashQueryResult_hiddenCandidateBound (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs)
    (hbound : HiddenCandidateBound words disclosed state) :
    HiddenCandidateBound words disclosed
      (hashQueryResult parameter inputs words disclosed known
        (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows) actual seed input state).2 :=
  hashQueryResult_hiddenCandidateBound parameter inputs words disclosed known _ actual seed input state hbound
    (freshPrefix_probe_route parameter inputs hencoding words disclosed known publicReplies selections rows input)

end SphincsSecurity.Concrete.ResidualByteFrontend
