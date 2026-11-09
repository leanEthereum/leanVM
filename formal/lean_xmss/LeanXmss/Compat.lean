module

public import Statement.LeanXmss
public import Common.WithHash

/-!
# The hash inputs by name

`Statement/LeanXmss.lean` states leanXMSS's tweakable hash (`thInput`, `th`, `thPair`,
`schemeSeedOf`, as `lean_xmss/hash.rs` does). The proofs name the inputs of leanXMSS's calls:
`P || A || payload` at a hash domain's address, the seed derivations' and the randomizer's, the
scheme seed's; and the derivations themselves.
-/

@[expose] public section

namespace LeanXmss

open HashSig

/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  addressBytes (hashDomainFields domain)

/-- The hash input `P || A || payload` of every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : HashInput :=
  littleEndianBytes 16 parameter ++ tweakBytes domain ++ payload

/-- `"leanXMSS" || S_0`, the 40-byte input of the scheme's seed `S`. -/
def seedHashInput (keySeed : MasterSeed) : HashInput :=
  seedTag ++ littleEndianBytes 32 keySeed

/-- `P || A || S`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  littleEndianBytes 16 parameter ++ addressBytes (keygenDomainFields domain) ++ littleEndianBytes
      32 seed

/-- `P || A_rnd(l, e) || S || M` (`TWEAK_RANDOMIZER = 7`): the randomizer base of a message. -/
def randomizerHashInput (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) : HashInput :=
  thInput parameter (tweakFields 7 0 (layerHi lay 0) key) (littleEndianBytes 32 seed ++ message)

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `S = H("leanXMSS" || S_0)` (`schemeSeedOf`). -/
abbrev schemeSeed (keySeed : MasterSeed) : m MasterSeed :=
  Verification.taggedSeedWithHash seedTag keySeed

/-- One seed derivation, first 16 bytes. -/
abbrev deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    m Digest :=
  Verification.thWithHash parameter (keygenDomainFields domain) (littleEndianBytes 32 seed)

/-- One seed derivation, all 32 bytes. -/
abbrev deriveOutput (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    m HashOutput :=
  Verification.thPairWithHash parameter (keygenDomainFields domain) (littleEndianBytes 32 seed)

/-- `R0`, the randomizer base of a message, first 16 bytes. -/
abbrev deriveRandomizer (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) : m Randomizer :=
  Verification.thWithHash parameter (tweakFields 7 0 (layerHi lay 0) key) (littleEndianBytes 32 seed
      ++ message)

theorem thInput_hashDomainFields (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    thInput parameter (hashDomainFields domain) payload =
      tweakableHashInput parameter domain payload := rfl

/-- The signer returned the forgery (`Common.SufCma.SignerReturnedForgery` at the requests'
messages). -/
abbrev SigningTranscript.Contains (log : OracleSpec.QueryLog SigningOracleSpec) (forgery : Forgery) : Prop :=
  Common.SufCma.SignerReturnedForgery SigningRequest.message log forgery.message forgery.signature

end LeanXmss
