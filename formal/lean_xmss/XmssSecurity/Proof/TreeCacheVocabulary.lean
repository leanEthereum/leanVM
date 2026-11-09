module

public import XmssSecurity.Proof.KeygenCache
public import XmssSecurity.Proof.CausalAuthenticationPathIndependence
public import XmssSecurity.Proof.ChainOraclePresampling
public import XmssSecurity.Proof.MerkleQueryPresence
public import XmssSecurity.Proof.CausalKeygenCoupling
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

def hashCacheLookup (cache : QueryCache HashSpec) (input : HashInput) :
    Option HashOutput :=
  cache input

/-- The domains whose key-generation entries agree between two key generations with the same tree
values: Merkle nodes of both layers and the top message digests. -/
def HashDomain.Retained : HashDomain → Prop
  | .merkle .. => True
  | .topMerkle .. => True
  | .topEncoding .. => True
  | _ => False

def MerkleHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ domain, domain.Retained ∧ AtHashAddress parameter domain input

theorem merkleHashInput_merkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    MerkleHashInput parameter (Concrete.CacheView.merkleInput parameter level node left right) :=
  ⟨.merkle level node, trivial, (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl⟩

theorem merkleHashInput_topMerkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : TopNode) (left right : Digest) :
    MerkleHashInput parameter
      (Concrete.CacheView.topMerkleInput parameter level node left right) :=
  ⟨.topMerkle level node, trivial, (atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl⟩

theorem not_merkleHashInput_of_atHashAddress (parameter : PublicParameter) (domain : HashDomain)
    (input : HashInput) (haddress : AtHashAddress parameter domain input)
    (hdomain : ¬ domain.Retained) : ¬ MerkleHashInput parameter input := by
  rintro ⟨candidate, hretained, hcandidate⟩
  rw [atHashAddress_unique parameter _ _ input hcandidate haddress] at hretained
  exact hdomain hretained

def LeafCacheOutputsCorrespond
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : ChainKey → ChainIndex → Digest)
    (left right : QueryCache HashSpec) : Prop :=
  ∀ key,
    hashCacheLookup left (Concrete.CacheView.keyLeafInput parameter key (leftEndpoints key)) =
    hashCacheLookup right (Concrete.CacheView.keyLeafInput parameter key (rightEndpoints key))

def LeafReplayOutputsCorrespond
    (parameter : PublicParameter)
    (leftStart rightStart : ChainKey → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop :=
  ∀ key,
    hashCacheLookup leftCache (Concrete.CacheView.keyLeafInput parameter key
      (Concrete.CacheReplay.keyOneTimePublicKey leftCache parameter leftStart key)) =
    hashCacheLookup rightCache (Concrete.CacheView.keyLeafInput parameter key
      (Concrete.CacheReplay.keyOneTimePublicKey rightCache parameter rightStart key))

def ReplayEndpointsMatch
    (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest)
    (endpoints : ChainKey → ChainIndex → Digest)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ key,
    endpoints key = Concrete.CacheReplay.keyOneTimePublicKey cache parameter start key

theorem merkleHashInput_ne_keyLeafInput
    (parameter : PublicParameter) (key : ChainKey)
    (endpoints : ChainIndex → Digest) (input : HashInput)
    (hinput : MerkleHashInput parameter input) :
    input ≠ Concrete.CacheView.keyLeafInput parameter key endpoints := by
  obtain ⟨domain, hretained, haddress⟩ := hinput
  intro heq
  subst input
  have hdomain := atHashAddress_unique parameter _ _ _ haddress
    ((atHashAddress_tweakableHashInput_iff parameter key.leafDomain key.leafDomain _).2 rfl)
  subst domain
  cases key <;> exact hretained

theorem LeafCacheOutputsCorrespond.cacheQuery_distinct
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : ChainKey → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (leftInput rightInput : HashInput) (output : HashOutput)
    (hleft : ∀ key, leftInput ≠ Concrete.CacheView.keyLeafInput parameter
      key (leftEndpoints key))
    (hright : ∀ key, rightInput ≠ Concrete.CacheView.keyLeafInput parameter
      key (rightEndpoints key)) :
    LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      (left.cacheQuery leftInput output) (right.cacheQuery rightInput output) := by
  intro key
  unfold hashCacheLookup
  rw [QueryCache.cacheQuery_of_ne left output (hleft key).symm,
    QueryCache.cacheQuery_of_ne right output (hright key).symm]
  exact hrel key

theorem LeafCacheOutputsCorrespond.cacheQuery_pair
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : ChainKey → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (key : ChainKey) (output : HashOutput) :
    LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      (left.cacheQuery
        (Concrete.CacheView.keyLeafInput parameter key (leftEndpoints key)) output)
      (right.cacheQuery
        (Concrete.CacheView.keyLeafInput parameter key (rightEndpoints key)) output) := by
  intro candidate
  unfold hashCacheLookup
  by_cases hkey : candidate = key
  · subst candidate
    simp only [QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne left output (by
        intro heq
        exact hkey ((Concrete.CacheView.keyLeafInput_eq_iff parameter candidate
          key (leftEndpoints candidate) (leftEndpoints key)).mp heq).1),
      QueryCache.cacheQuery_of_ne right output (by
        intro heq
        exact hkey ((Concrete.CacheView.keyLeafInput_eq_iff parameter candidate
          key (rightEndpoints candidate) (rightEndpoints key)).mp heq).1)]
    exact hrel candidate

/-- Map a leaf input of either layer to the honest leaf input key generation fixed at its address. -/
noncomputable def keygenKeyLeafTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ key endpoints,
      input = Concrete.CacheView.keyLeafInput secretKey.parameter key endpoints then
    Concrete.CacheView.keyLeafInput secretKey.parameter h.choose
      (Concrete.CacheReplay.keyOneTimePublicKey cache secretKey.parameter
        secretKey.keyChainStart h.choose)
  else input

@[simp]
theorem keygenKeyLeafTargetInput_keyLeafInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (key : ChainKey) (endpoints : ChainIndex → Digest) :
    keygenKeyLeafTargetInput secretKey cache
      (Concrete.CacheView.keyLeafInput secretKey.parameter key endpoints) =
      Concrete.CacheView.keyLeafInput secretKey.parameter key
        (Concrete.CacheReplay.keyOneTimePublicKey cache secretKey.parameter
          secretKey.keyChainStart key) := by
  unfold keygenKeyLeafTargetInput
  split
  · rename_i h
    obtain ⟨chosenEndpoints, hinput⟩ := h.choose_spec
    have hkey : h.choose = key :=
      ((Concrete.CacheView.keyLeafInput_eq_iff _ _ _ _ _).mp hinput.symm).1
    rw [hkey]
  · rename_i h
    exact (h ⟨key, endpoints, rfl⟩).elim

def chainEndpointDigit : Digit :=
  ⟨chainLength - 1, by decide⟩

end XmssSecurity
