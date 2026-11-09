module

public import XmssSecurity.Proof.EvalDistEq
public import XmssSecurity.Proof.IdealStatement
public import VCVio.OracleComp.Constructions.SampleableType

@[expose] public section

open OracleComp ENNReal

namespace XmssSecurity.HiddenValue

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

theorem card_digest : Fintype.card Digest = 2 ^ digestBits := by
  simp

end XmssSecurity.HiddenValue
