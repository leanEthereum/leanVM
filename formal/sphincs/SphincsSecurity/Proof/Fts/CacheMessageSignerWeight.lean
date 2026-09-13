import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheMessageWeight

/-! ## SignerInputWeight -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def successfulSignerInputWeight (key : SecretKey) (message : Message)
    (weight : HashInput → FewTimeView → ENNReal)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : ENNReal :=
  match result.1.1, result.1.2 with
  | some signature, some view => weight
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)) view
  | _, _ => 0

noncomputable def cachedSignerInputWeight (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) : ENNReal :=
  match before input with
  | none => 0
  | some output =>
      if (∃ randomness, input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ∧
          Admissible (truncateMessageDigest output) then weight input (hashOutputFewTimeView output) else 0

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cachedSignerInputWeight_le_cacheMessageEntryWeight (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) :
    cachedSignerInputWeight key message before weight input ≤ cacheMessageEntryWeight key.parameter weight before input := by
  unfold cachedSignerInputWeight cacheMessageEntryWeight
  cases before input with
  | none => exact le_rfl
  | some output =>
      simp only
      split_ifs with hsource htarget
      · exact le_rfl
      · obtain ⟨randomness, heq⟩ := hsource.1
        exact (htarget ⟨⟨messageDigestPayload key.root message randomness, heq.symm⟩, hsource.2⟩).elim
      · exact bot_le
      · exact le_rfl

end SphincsSecurity.Concrete
