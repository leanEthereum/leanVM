import XmssSecurity.Proof.EncodingLemmas
import XmssSecurity.Proof.RandomOracle

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
