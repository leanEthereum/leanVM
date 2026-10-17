import XmssSecurity.Proof.Bridge.Translate
import XmssSecurity.Proof.Deterministic.TableSigner
import XmssSecurity.Proof.Seeded.FiniteTable
import XmssSecurity.Proof.Seeded.SeedGuessing
import XmssSecurity.Proof.Seeded.CacheCoupling
import XmssSecurity.Proof.HashInputLemmas

/-!
# The seed derivations of the real scheme

Every input of the real scheme that contains the scheme's seed `S`: the parameter, the 29 pair derivations
of each one-time key of both layers, the bottom randomizer base `R0(idx, m)` of every request and the
top one `R0_top(b, r)` of every top key and bottom root. Their answers are presampled into a
programmed cache; no tweakable hash input is one of them.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- A bottom key and a pair of its chains. -/
abbrev BottomPos := LeafIndex × ChainPair
/-- A top key and a pair of its chains. -/
abbrev TopOtsPos := TopIndex × ChainPair
/-- A top key and the bottom root it signs. -/
abbrev TopRndPos := TopIndex × Digest

/-- Every derivation answer. -/
structure Derivations where
  param : HashOutput
  bottom : BottomPos → HashOutput
  top : TopOtsPos → HashOutput
  rnd : RandomizerOutputs
  topRnd : TopRndPos → HashOutput

def paramInput (seed : MasterSeed) : HashInput :=
  LeanXmss.keygenHashInput 0 .parameter seed

def bottomInput (parameter : PublicParameter) (seed : MasterSeed) (pos : BottomPos) : HashInput :=
  LeanXmss.keygenHashInput parameter (.ots LeanXmss.bottomLayer pos.1 pos.2) seed

def topInput (parameter : PublicParameter) (seed : MasterSeed) (pos : TopOtsPos) : HashInput :=
  LeanXmss.keygenHashInput parameter (.ots LeanXmss.topLayer (topKey pos.1) pos.2) seed

def rndInput (parameter : PublicParameter) (seed : MasterSeed) (request : SignRequest) : HashInput :=
  LeanXmss.randomizerHashInput parameter LeanXmss.bottomLayer request.leafIndex seed
    (LeanXmss.bytesLE 32 request.message)

def topRndInput (parameter : PublicParameter) (seed : MasterSeed) (pos : TopRndPos) : HashInput :=
  LeanXmss.randomizerHashInput parameter LeanXmss.topLayer (topKey pos.1) seed
    (LeanXmss.bytesLE 16 pos.2)

/-! ## Input layout -/

theorem paramInput_eq (seed : MasterSeed) :
    paramInput seed = bytesLE 16 0 ++ fieldBytes (tweakFields 5 0 0 0) ++ bytesLE 32 seed := rfl

theorem bottomInput_eq (parameter : PublicParameter) (seed : MasterSeed) (pos : BottomPos) :
    bottomInput parameter seed pos =
      bytesLE 16 parameter ++ fieldBytes (tweakFields 0 0 pos.2.val pos.1.val) ++ bytesLE 32 seed := by
  simp only [bottomInput, LeanXmss.keygenHashInput, LeanXmss.keygenDomainFields, LeanXmss.layerHi,
    LeanXmss.bottomLayer]
  rfl

theorem topInput_eq (parameter : PublicParameter) (seed : MasterSeed) (pos : TopOtsPos) :
    topInput parameter seed pos =
      bytesLE 16 parameter ++ fieldBytes (tweakFields 0 0 (topFlag + pos.2.val) pos.1.val) ++
        bytesLE 32 seed := by
  simp only [topInput, LeanXmss.keygenHashInput, LeanXmss.keygenDomainFields]
  have h : LeanXmss.layerHi LeanXmss.topLayer pos.2.val = topFlag + pos.2.val := by
    simp only [LeanXmss.layerHi, LeanXmss.topLayer, topFlag]
    omega
  rw [h]
  rfl

theorem rndInput_eq (parameter : PublicParameter) (seed : MasterSeed) (request : SignRequest) :
    rndInput parameter seed request =
      bytesLE 16 parameter ++ fieldBytes (tweakFields 7 0 0 request.leafIndex.val) ++
        (bytesLE 32 seed ++ bytesLE 32 request.message) := by
  simp only [rndInput, LeanXmss.randomizerHashInput, List.append_assoc]
  rfl

theorem topRndInput_eq (parameter : PublicParameter) (seed : MasterSeed) (pos : TopRndPos) :
    topRndInput parameter seed pos =
      bytesLE 16 parameter ++ fieldBytes (tweakFields 7 0 topFlag pos.1.val) ++
        (bytesLE 32 seed ++ bytesLE 16 pos.2) := by
  simp only [topRndInput, LeanXmss.randomizerHashInput, List.append_assoc]
  rfl

theorem tweakableHashInput_eq (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    tweakableHashInput parameter domain payload =
      bytesLE 16 parameter ++ fieldBytes (hashDomainFields domain) ++ (payload ++ domainSuffix domain) := by
  simp only [tweakableHashInput, tweakBytes, List.append_assoc]

/-- `P || A || payload` determines `P`, the address and the payload. -/
theorem prefix_inj {parameter parameter' : PublicParameter} {fields fields' : TweakFields}
    {payload payload' : HashInput}
    (h : bytesLE 16 parameter ++ fieldBytes fields ++ payload =
      bytesLE 16 parameter' ++ fieldBytes fields' ++ payload') :
    parameter = parameter' ∧ fields = fields' ∧ payload = payload' := by
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by simp)
  obtain ⟨hparameter, hfields⟩ := List.append_inj hprefix (by simp)
  exact ⟨bytesLE_injective 16 hparameter, fieldBytes_injective hfields, hpayload⟩

theorem ofNat_inj {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem tag_of_fields {a b c d a' b' c' d' : Nat} (h : tweakFields a b c d = tweakFields a' b' c' d') :
    BitVec.ofNat 5 a = BitVec.ofNat 5 a' := congrArg TweakFields.tag h

theorem hi_of_fields {a b c d a' b' c' d' : Nat} (h : tweakFields a b c d = tweakFields a' b' c' d')
    (hc : c < 2 ^ 24) (hc' : c' < 2 ^ 24) : c = c' := ofNat_inj hc hc' (congrArg TweakFields.hi h)

theorem lo_of_fields {a b c d a' b' c' d' : Nat} (h : tweakFields a b c d = tweakFields a' b' c' d')
    (hd : d < 2 ^ 32) (hd' : d' < 2 ^ 32) : d = d' := ofNat_inj hd hd' (congrArg TweakFields.lo h)

theorem leaf_lt (index : LeafIndex) : index.val < 2 ^ 32 := index.isLt

theorem top_lt (key : TopIndex) : key.val < 2 ^ 32 := by
  have := key.isLt
  simp only [topLifetime, treeHeight] at this
  omega

theorem pair_lt (pair : ChainPair) : pair.val < 29 := pair.isLt

/-! ## Distinct inputs -/

/-- An input of the model's verification hashes. -/
def Tweakable (input : HashInput) : Prop :=
  ∃ parameter domain payload, input = tweakableHashInput parameter domain payload

theorem tweakable_tag {input : HashInput} (h : Tweakable input) {parameter : PublicParameter}
    {fields : TweakFields} {payload : HashInput}
    (hinput : input = bytesLE 16 parameter ++ fieldBytes fields ++ payload) :
    fields.tag = 1 ∨ fields.tag = 2 ∨ fields.tag = 3 ∨ fields.tag = 12 := by
  obtain ⟨parameter', domain, payload', rfl⟩ := h
  rw [tweakableHashInput_eq] at hinput
  have hfields := (prefix_inj hinput).2.1
  rw [← hfields, hashDomainFields_tag]
  cases domain <;> simp [hashDomainTag]

theorem not_tweakable_of_tag {input : HashInput} {parameter : PublicParameter} {fields : TweakFields}
    {payload : HashInput} (hinput : input = bytesLE 16 parameter ++ fieldBytes fields ++ payload)
    (htag : fields.tag = 0 ∨ fields.tag = 5 ∨ fields.tag = 7) : ¬Tweakable input := by
  intro h
  have := tweakable_tag h hinput
  rcases htag with htag | htag | htag <;> rw [htag] at this <;> revert this <;> decide

theorem paramInput_not_tweakable (seed : MasterSeed) : ¬Tweakable (paramInput seed) :=
  not_tweakable_of_tag (paramInput_eq seed) (by decide)

theorem bottomInput_not_tweakable (parameter : PublicParameter) (seed : MasterSeed) (pos : BottomPos) :
    ¬Tweakable (bottomInput parameter seed pos) :=
  not_tweakable_of_tag (bottomInput_eq parameter seed pos) (Or.inl rfl)

theorem topInput_not_tweakable (parameter : PublicParameter) (seed : MasterSeed) (pos : TopOtsPos) :
    ¬Tweakable (topInput parameter seed pos) :=
  not_tweakable_of_tag (topInput_eq parameter seed pos) (Or.inl rfl)

theorem rndInput_not_tweakable (parameter : PublicParameter) (seed : MasterSeed) (request : SignRequest) :
    ¬Tweakable (rndInput parameter seed request) :=
  not_tweakable_of_tag (rndInput_eq parameter seed request) (Or.inr (Or.inr rfl))

theorem topRndInput_not_tweakable (parameter : PublicParameter) (seed : MasterSeed) (pos : TopRndPos) :
    ¬Tweakable (topRndInput parameter seed pos) :=
  not_tweakable_of_tag (topRndInput_eq parameter seed pos) (Or.inr (Or.inr rfl))

theorem bottomInput_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (bottomInput parameter seed) := by
  intro left right h
  rw [bottomInput_eq, bottomInput_eq] at h
  have hf := (prefix_inj h).2.1
  have hhi := hi_of_fields hf (by have := pair_lt left.2; omega) (by have := pair_lt right.2; omega)
  have hlo := lo_of_fields hf (leaf_lt left.1) (leaf_lt right.1)
  exact Prod.ext (Fin.ext hlo) (Fin.ext hhi)

theorem topInput_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (topInput parameter seed) := by
  intro left right h
  rw [topInput_eq, topInput_eq] at h
  have hf := (prefix_inj h).2.1
  have hhi := hi_of_fields hf (by have := pair_lt left.2; simp only [topFlag]; omega)
    (by have := pair_lt right.2; simp only [topFlag]; omega)
  have hlo := lo_of_fields hf (top_lt left.1) (top_lt right.1)
  exact Prod.ext (Fin.ext hlo) (Fin.ext (by omega))

theorem rndInput_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (rndInput parameter seed) := by
  intro left right h
  rw [rndInput_eq, rndInput_eq] at h
  obtain ⟨-, hf, hpayload⟩ := prefix_inj h
  have hlo := lo_of_fields hf (leaf_lt left.leafIndex) (leaf_lt right.leafIndex)
  have hm := bytesLE_injective 32 (List.append_inj hpayload (by simp)).2
  cases left
  cases right
  simp only [SignRequest.mk.injEq]
  exact ⟨Fin.ext hlo, hm⟩

theorem topRndInput_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (topRndInput parameter seed) := by
  intro left right h
  rw [topRndInput_eq, topRndInput_eq] at h
  obtain ⟨-, hf, hpayload⟩ := prefix_inj h
  have hlo := lo_of_fields hf (top_lt left.1) (top_lt right.1)
  have hr := bytesLE_injective 16 (List.append_inj hpayload (by simp)).2
  exact Prod.ext (Fin.ext hlo) hr

theorem bottomInput_ne_param (parameter : PublicParameter) (seed seed' : MasterSeed) (pos : BottomPos) :
    bottomInput parameter seed pos ≠ paramInput seed' := by
  intro h
  rw [bottomInput_eq, paramInput_eq] at h
  have h' : BitVec.ofNat 5 0 = BitVec.ofNat 5 5 := congrArg TweakFields.tag (prefix_inj h).2.1
  exact absurd h' (by decide)

theorem topInput_ne_param (parameter : PublicParameter) (seed seed' : MasterSeed) (pos : TopOtsPos) :
    topInput parameter seed pos ≠ paramInput seed' := by
  intro h
  rw [topInput_eq, paramInput_eq] at h
  have h' : BitVec.ofNat 5 0 = BitVec.ofNat 5 5 := congrArg TweakFields.tag (prefix_inj h).2.1
  exact absurd h' (by decide)

theorem topInput_ne_bottom (parameter : PublicParameter) (seed : MasterSeed) (pos : TopOtsPos)
    (pos' : BottomPos) : topInput parameter seed pos ≠ bottomInput parameter seed pos' := by
  intro h
  rw [topInput_eq, bottomInput_eq] at h
  have hhi := hi_of_fields (prefix_inj h).2.1 (by have := pair_lt pos.2; simp only [topFlag]; omega)
    (by have := pair_lt pos'.2; omega)
  have := pair_lt pos'.2
  simp only [topFlag] at hhi
  omega

theorem rndInput_ne_keygen (parameter parameter' : PublicParameter) (seed seed' : MasterSeed)
    (request : SignRequest) (fields : TweakFields) (hfields : fields.tag = 0 ∨ fields.tag = 5) :
    rndInput parameter seed request ≠ bytesLE 16 parameter' ++ fieldBytes fields ++ bytesLE 32 seed' := by
  intro h
  rw [rndInput_eq] at h
  have h' : BitVec.ofNat 5 7 = fields.tag := congrArg TweakFields.tag (prefix_inj h).2.1
  rcases hfields with hf | hf <;> rw [hf] at h' <;> exact absurd h' (by decide)

theorem topRndInput_ne_keygen (parameter parameter' : PublicParameter) (seed seed' : MasterSeed)
    (pos : TopRndPos) (fields : TweakFields) (hfields : fields.tag = 0 ∨ fields.tag = 5) :
    topRndInput parameter seed pos ≠ bytesLE 16 parameter' ++ fieldBytes fields ++ bytesLE 32 seed' := by
  intro h
  rw [topRndInput_eq] at h
  have h' : BitVec.ofNat 5 7 = fields.tag := congrArg TweakFields.tag (prefix_inj h).2.1
  rcases hfields with hf | hf <;> rw [hf] at h' <;> exact absurd h' (by decide)

theorem topRndInput_ne_rnd (parameter : PublicParameter) (seed : MasterSeed) (pos : TopRndPos)
    (request : SignRequest) : topRndInput parameter seed pos ≠ rndInput parameter seed request := by
  intro h
  rw [topRndInput_eq, rndInput_eq] at h
  have := hi_of_fields (prefix_inj h).2.1 (by simp only [topFlag]; omega) (by omega)
  simp only [topFlag] at this
  omega

/-! ## Seed hits -/

theorem seedHit_of_prefix {parameter : PublicParameter} {fields : TweakFields} {seed : MasterSeed}
    {rest : HashInput} :
    DerivationSeedHit (bytesLE 16 parameter ++ fieldBytes fields ++ (bytesLE 32 seed ++ rest)) seed := by
  simp [DerivationSeedHit, List.drop_append, List.take_append]

theorem seedHit_of_prefix' {parameter : PublicParameter} {fields : TweakFields} {seed : MasterSeed} :
    DerivationSeedHit (bytesLE 16 parameter ++ fieldBytes fields ++ bytesLE 32 seed) seed := by
  have := seedHit_of_prefix (parameter := parameter) (fields := fields) (seed := seed) (rest := [])
  rwa [List.append_nil] at this

theorem paramInput_seedHit (seed : MasterSeed) : DerivationSeedHit (paramInput seed) seed := by
  rw [paramInput_eq]
  exact seedHit_of_prefix'

theorem bottomInput_seedHit (parameter : PublicParameter) (seed : MasterSeed) (pos : BottomPos) :
    DerivationSeedHit (bottomInput parameter seed pos) seed := by
  rw [bottomInput_eq]
  exact seedHit_of_prefix'

theorem topInput_seedHit (parameter : PublicParameter) (seed : MasterSeed) (pos : TopOtsPos) :
    DerivationSeedHit (topInput parameter seed pos) seed := by
  rw [topInput_eq]
  exact seedHit_of_prefix'

theorem rndInput_seedHit (parameter : PublicParameter) (seed : MasterSeed) (request : SignRequest) :
    DerivationSeedHit (rndInput parameter seed request) seed := by
  rw [rndInput_eq]
  exact seedHit_of_prefix

theorem topRndInput_seedHit (parameter : PublicParameter) (seed : MasterSeed) (pos : TopRndPos) :
    DerivationSeedHit (topRndInput parameter seed pos) seed := by
  rw [topRndInput_eq]
  exact seedHit_of_prefix

end XmssSecurity.Bridge
