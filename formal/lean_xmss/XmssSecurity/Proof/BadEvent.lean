module

public import XmssSecurity.Proof.EncodingLemmas

@[expose] public section

namespace XmssSecurity

/-- The elementary bad events of the reduction, one per part of a signature a forgery can break. -/
inductive BadEvent where
  | encoding
  | chain (chain : ChainIndex)
  | suffixCollision (step : Fin verificationChainHashes)
  | leaf
  | merkle (level : Fin treeHeight)

end XmssSecurity
