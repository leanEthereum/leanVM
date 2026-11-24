module

public import VCVio.OracleComp.Constructions.SampleableType
public import XmssSecurity.Scheme

@[expose] public section

open OracleComp ENNReal

namespace XmssSecurity.HiddenValue

theorem card_digest : Fintype.card Digest = 2 ^ digestBits := by
  simp

end XmssSecurity.HiddenValue
