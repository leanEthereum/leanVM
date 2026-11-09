module

public import XmssSecurity.Proof.EncodingLemmas
public import XmssSecurity.Proof.RandomOracle

@[expose] public section

namespace XmssSecurity

/-- The elementary bad events used by the current classical reduction. -/
inductive BadEvent where
  | encoding
  | chain (chain : ChainIndex)
  | suffixCollision (step : Fin verificationChainHashes)
  | leaf
  | merkle (level : Fin treeHeight)
deriving DecidableEq, Fintype

end XmssSecurity
