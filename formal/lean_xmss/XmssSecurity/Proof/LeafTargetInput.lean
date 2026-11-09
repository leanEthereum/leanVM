module

public import XmssSecurity.Proof.HashInputLemmas
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

/-- Map a leaf input to the honest leaf input fixed by key generation at the same leaf index. -/
noncomputable def keygenLeafTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ leafIndex endpoints,
      input = Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints then
    Concrete.CacheView.leafInput secretKey.parameter h.choose
      (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart h.choose)
  else input

attribute [irreducible] keygenLeafTargetInput

end XmssSecurity

