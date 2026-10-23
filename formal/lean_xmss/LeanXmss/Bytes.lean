import LeanXmss.Scheme

/-!
# Byte encodings and domain separation

An input determines its parameter, its address and its payload, and an address determines the call:
two hash calls of different kinds, or of the same kind at different places, never share an input.
-/

namespace LeanXmss

theorem bytesLE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by
  simp [bytesLE]

@[simp] theorem bytesLE_length_digest (x : Digest) : (bytesLE 16 x).length = 16 :=
  bytesLE_length 16 x

@[simp] theorem bytesLE_length_publicParameter (x : PublicParameter) :
    (bytesLE 16 x).length = 16 :=
  bytesLE_length 16 x

@[simp] theorem bytesLE_length_message (x : Message) : (bytesLE 32 x).length = 32 :=
  bytesLE_length 32 x

@[simp] theorem bytesLE_length_masterSeed (x : MasterSeed) : (bytesLE 32 x).length = 32 :=
  bytesLE_length 32 x

/-- A bit vector determines the natural it encodes, below the wrap. -/
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

/-- A concatenation determines its two halves. -/
theorem bitVec_append_inj {n m : Nat} {a a' : BitVec n} {b b' : BitVec m}
    (h : a ++ b = a' ++ b') : a = a' ∧ b = b' := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v : BitVec (n + m) => v.getLsbD (m + i)) h
    simpa [BitVec.getLsbD_append] using this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v : BitVec (n + m) => v.getLsbD i) h
    simpa [BitVec.getLsbD_append, hi] using this

/-- The 16 address bytes determine the type, the step and the two fields. -/
theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) : t1 = t2 := by
  obtain ⟨tag1, step1, hi1, lo1⟩ := t1
  obtain ⟨tag2, step2, hi2, lo2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, _⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, htag⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hlo, hhi⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hstep, htag⟩ := bitVec_append_inj (bytesLE_injective htag)
  simp only [bytesLE_injective hlo, bytesLE_injective hhi, hstep, htag]

/-- `P || A || payload` determines the parameter, the address and the payload. -/
theorem fieldInput_injective {fields fields' : TweakFields}
    {parameter parameter' : PublicParameter} {payload payload' : HashInput}
    (h : bytesLE 16 parameter ++ fieldBytes fields ++ payload =
      bytesLE 16 parameter' ++ fieldBytes fields' ++ payload') :
    fields = fields' ∧ parameter = parameter' ∧ payload = payload' := by
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length])
  obtain ⟨hparameter, hfields⟩ := List.append_inj hprefix (by simp)
  exact ⟨fieldBytes_injective hfields, bytesLE_injective hparameter, hpayload⟩

theorem tweakableInput_injective {parameter parameter' : PublicParameter}
    {domain domain' : HashDomain} {payload payload' : HashInput}
    (h : tweakableHashInput parameter domain payload =
      tweakableHashInput parameter' domain' payload') :
    hashDomainFields domain = hashDomainFields domain' ∧
      parameter = parameter' ∧ payload = payload' :=
  fieldInput_injective h

/-! ### The seed hash

Its input is 40 bytes, every other input at least 64: `P || A` then a 32-byte seed, or a payload that
is never 8 bytes (the scheme's payloads are at least 32). -/

theorem seedHashInput_length (keySeed : MasterSeed) : (seedHashInput keySeed).length = 40 := by
  simp [seedHashInput, seedTag, bytesLE_length]

theorem seedHashInput_injective : Function.Injective seedHashInput :=
  fun _ _ h => bytesLE_injective (List.append_cancel_left h)

theorem seedHashInput_ne_keygen (keySeed : MasterSeed) (parameter : PublicParameter)
    (domain : KeygenDomain) (seed : MasterSeed) :
    seedHashInput keySeed ≠ keygenHashInput parameter domain seed := by
  intro h
  have := congrArg List.length h
  simp [seedHashInput_length, keygenHashInput, fieldBytes, bytesLE_length] at this

theorem seedHashInput_ne_randomizer (keySeed : MasterSeed) (parameter : PublicParameter) (lay : Layer)
    (key : KeyIndex) (seed : MasterSeed) (message : HashInput) :
    seedHashInput keySeed ≠ randomizerHashInput parameter lay key seed message := by
  intro h
  have := congrArg List.length h
  simp [seedHashInput_length, randomizerHashInput, fieldBytes, bytesLE_length] at this
  omega

theorem seedHashInput_ne_tweakable (keySeed : MasterSeed) (parameter : PublicParameter)
    (domain : HashDomain) {payload : HashInput} (hpayload : payload.length ≠ 8) :
    seedHashInput keySeed ≠ tweakableHashInput parameter domain payload := by
  intro h
  have := congrArg List.length h
  simp [seedHashInput_length, tweakableHashInput, tweakBytes, fieldBytes, bytesLE_length] at this
  omega

/-! ### Address fields -/

theorem tweakFields_inj {tag tag' step step' hi hi' lo lo' : Nat}
    (htag : tag < 2 ^ 5) (htag' : tag' < 2 ^ 5) (hstep : step < 2 ^ 3) (hstep' : step' < 2 ^ 3)
    (hhi : hi < 2 ^ 24) (hhi' : hi' < 2 ^ 24) (hlo : lo < 2 ^ 32) (hlo' : lo' < 2 ^ 32)
    (h : tweakFields tag step hi lo = tweakFields tag' step' hi' lo') :
    tag = tag' ∧ step = step' ∧ hi = hi' ∧ lo = lo' := by
  simp only [tweakFields, TweakFields.mk.injEq] at h
  exact ⟨ofNat_inj_of_lt htag htag' h.1, ofNat_inj_of_lt hstep hstep' h.2.1,
    ofNat_inj_of_lt hhi hhi' h.2.2.1, ofNat_inj_of_lt hlo hlo' h.2.2.2⟩

theorem key_lt (key : KeyIndex) : key.val < 2 ^ 32 := by
  have := key.isLt; simp only [lifetime, numLayers, layerHeight] at this; omega

/-- `hi` determines the layer and the field below bit 23. -/
theorem layerHi_inj {lay lay' : Layer} {a a' : Nat} (ha : a < 2 ^ 23) (ha' : a' < 2 ^ 23)
    (h : layerHi lay a = layerHi lay' a') : lay = lay' ∧ a = a' := by
  have := lay.isLt; have := lay'.isLt
  simp only [layerHi, numLayers] at *
  refine ⟨Fin.ext ?_, ?_⟩ <;> omega

theorem layerHi_lt (lay : Layer) {a : Nat} (ha : a < 2 ^ 23) : layerHi lay a < 2 ^ 24 := by
  have := lay.isLt; simp only [layerHi, numLayers] at *; omega

/-- A domain is in range when its node coordinates are: a level at most 16 and an index below
`2^32`, as every honest node and every node the verifier hashes. -/
def HashDomain.InRange : HashDomain → Prop
  | .node _ level nodeIdx => level ≤ layerHeight ∧ nodeIdx < 2 ^ 32
  | _ => True

/-- The four address fields of a domain, as numbers. -/
def HashDomain.code : HashDomain → Nat × Nat × Nat × Nat
  | .chain lay key step => (1, step, layerHi lay 0, key)
  | .leaf lay key => (2, 0, layerHi lay 0, key)
  | .node lay level nodeIdx => (3, 0, layerHi lay level, nodeIdx)
  | .message lay key => (12, 0, layerHi lay 0, key)

theorem hashDomainFields_eq_code (d : HashDomain) :
    hashDomainFields d = tweakFields d.code.1 d.code.2.1 d.code.2.2.1 d.code.2.2.2 := by
  cases d <;> rfl

theorem code_lt {d : HashDomain} (hd : d.InRange) :
    d.code.1 < 2 ^ 5 ∧ d.code.2.1 < 2 ^ 3 ∧ d.code.2.2.1 < 2 ^ 24 ∧ d.code.2.2.2 < 2 ^ 32 := by
  cases d with
  | chain lay key step =>
      have := step.isLt; have := key_lt key
      simp only [HashDomain.code, chainLength, winternitzBits] at *
      exact ⟨by norm_num, by omega, layerHi_lt lay (by norm_num), this⟩
  | leaf lay key =>
      exact ⟨by simp [HashDomain.code], by simp [HashDomain.code], layerHi_lt lay (by norm_num), key_lt key⟩
  | node lay level nodeIdx =>
      simp only [HashDomain.InRange, layerHeight] at hd
      exact ⟨by simp [HashDomain.code], by simp [HashDomain.code], layerHi_lt lay (by omega), hd.2⟩
  | message lay key =>
      exact ⟨by simp [HashDomain.code], by simp [HashDomain.code], layerHi_lt lay (by norm_num), key_lt key⟩

/-- An address in range determines its domain. -/
theorem hashDomainFields_injective {d d' : HashDomain} (hd : d.InRange) (hd' : d'.InRange)
    (h : hashDomainFields d = hashDomainFields d') : d = d' := by
  rw [hashDomainFields_eq_code, hashDomainFields_eq_code] at h
  obtain ⟨t, s, hh, l⟩ := code_lt hd
  obtain ⟨t', s', hh', l'⟩ := code_lt hd'
  obtain ⟨ht, hs, hhi, hl⟩ := tweakFields_inj t t' s s' hh hh' l l' h
  cases d <;> cases d' <;>
    simp only [HashDomain.code, HashDomain.InRange, layerHeight] at ht hs hhi hl hd hd' <;>
    (try omega)
  · obtain ⟨hlay, -⟩ := layerHi_inj (by norm_num) (by norm_num) hhi
    subst hlay; congr 1 <;> apply Fin.ext <;> omega
  · obtain ⟨hlay, -⟩ := layerHi_inj (by norm_num) (by norm_num) hhi
    subst hlay; congr 1; apply Fin.ext; omega
  · obtain ⟨hlay, hlev⟩ := layerHi_inj (by omega) (by omega) hhi
    subst hlay; congr 1
  · obtain ⟨hlay, -⟩ := layerHi_inj (by norm_num) (by norm_num) hhi
    subst hlay; congr 1; apply Fin.ext; omega

end LeanXmss
