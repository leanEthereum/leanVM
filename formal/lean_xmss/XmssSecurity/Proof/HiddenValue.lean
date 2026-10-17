import XmssSecurity.Proof.IdealStatement
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp ENNReal

namespace XmssSecurity.HiddenValue

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

theorem card_digest : Fintype.card Digest = 2 ^ digestBits := by
  simp

theorem uniform_digest_point_probability (target : Digest) :
    Pr[= target | $ᵗ Digest] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample, card_digest]

end XmssSecurity.HiddenValue
