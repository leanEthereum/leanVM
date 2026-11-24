module

public import VCVio.OracleComp.Constructions.SampleableType
public import XmssSecurity.Scheme

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem card_randomness : Fintype.card Randomness = 2 ^ randomnessBits := by
  simp

end XmssSecurity
