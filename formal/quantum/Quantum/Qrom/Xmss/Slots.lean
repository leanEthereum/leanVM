module

public import Quantum.Qrom.Xmss.Scheme
public import Quantum.Xmss.Keccak

@[expose] public section

/-!
# leanXMSS's hash calls as random-oracle inputs

Each input of the random function names at most one slot of leanXMSS (`Quantum.Xmss.Slot`: a
chain step, a leaf, a tree node, a message digest, a chain-start derivation, a randomizer base,
the public parameter, the scheme seed), read from its bytes as the QRPM proof reads it from a
sponge tail's first block, with the same address decoding (`slotOfAddress`, `fieldsSlot`):

* `slotOf x`: the slot of the input `x`, from its prefix, address and the payload's chain index
  (the scheme seed's derivation by its shape, 40 bytes starting with `leanXMSS`).
* `slotInput P s d`, `cell P s d`: the input the scheme hashes at slot `s` under the public
  parameter `P` with the payload data `d : Payload s`, and its code in `HashDomain`;
  `hashQ_slotInput`: the hash of `slotInput` is one query at `cell`.
* `slotOf_cell`: the cell of an addressable slot names that slot; `cell_injective`: distinct
  (slot, payload) pairs have distinct cells.
-/

open OracleComp OracleSpec
open HashSig HashSig.OverPermutation LeanXmss
open Quantum.Xmss (Slot fieldsSlot slotOfAddress slotOfAddress_self inputBit ofBits bitOf
  bitOf_eq_one_iff bitOf_injective getLsbD_ofBits payloadIndex inputBit_thInput_prefix
  inputBit_thInput_address inputBit_thInput_payload inputBit_addressBytes_lo
  inputBit_addressBytes_hi inputBit_addressBytes_stepTag inputBit_littleEndianBytes
  thInput_injective)

namespace Quantum.Qrom.Xmss

/-! ## The slot of an input -/

/-- Bits `a` to `a + n - 1` of a byte string, as a bit vector. -/
def sliceBits (l : HashInput) (a n : ℕ) : BitVec n :=
  ofBits fun j : Fin n ↦ inputBit l (a + j)

theorem sliceBits_eq {l : HashInput} {a n : ℕ} {v : BitVec n}
    (hv : ∀ j, j < n → inputBit l (a + j) = bitOf (v.getLsbD j)) : sliceBits l a n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [sliceBits, getLsbD_ofBits _ j hj]
  simp only [hv j hj, bitOf_eq_one_iff, Bool.decide_eq_true]

/-- The address fields of a tweakable-hash input, bytes `16` to `31`. -/
def fieldsOf (l : HashInput) : TweakFields :=
  ⟨sliceBits l 184 5, sliceBits l 189 3, sliceBits l 160 24, sliceBits l 128 32⟩

/-- The slot of a byte string: the scheme seed's derivation if it has its shape (40 bytes
starting with `leanXMSS`), else the slot its prefix (bytes `0` to `15`), address (bytes `16` to
`31`) and chain index (bytes `48` to `63`) name, the prefix `0` with type `5` being the public
parameter's derivation. -/
def slotOfInput (l : HashInput) : Option Slot :=
  if l.length = 40 ∧ l.take 8 = seedTag then some .seed
  else slotOfAddress (sliceBits l 0 128) (sliceBits l 0 128) (fieldsOf l) (sliceBits l 384 128)

/-- **The slot of a random-oracle input**: the slot of the byte string it encodes. -/
def slotOf (x : HashDomain) : Option Slot :=
  slotOfInput (decodeInput x)

/-- The slot of a tweakable-hash input is the one its prefix, address and payload name. -/
theorem slotOfInput_thInput (Q : PublicParameter) (fields : TweakFields) (payload : HashInput)
    (hp : payload.length ≠ 8) :
    slotOfInput (thInput Q fields payload) =
      slotOfAddress Q Q fields (payloadIndex payload) := by
  have hQ : sliceBits (thInput Q fields payload) 0 128 = Q := sliceBits_eq fun j hj ↦ by
    rw [zero_add, inputBit_thInput_prefix _ _ _ _ hj]
  have hlo : sliceBits (thInput Q fields payload) 128 32 = fields.lo := sliceBits_eq fun j hj ↦ by
    rw [inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_lo _ _ hj]
  have hhi : sliceBits (thInput Q fields payload) 160 24 = fields.hi := sliceBits_eq fun j hj ↦ by
    rw [show 160 + j = 128 + (32 + j) by omega, inputBit_thInput_address _ _ _ _ (by omega),
      inputBit_addressBytes_hi _ _ hj]
  have htag : sliceBits (thInput Q fields payload) 184 5 = fields.tag :=
    sliceBits_eq fun j hj ↦ by
      rw [show 184 + j = 128 + (56 + j) by omega, inputBit_thInput_address _ _ _ _ (by omega),
        inputBit_addressBytes_stepTag _ _ (by omega), BitVec.getLsbD_append, ite_eq_left hj]
  have hstep : sliceBits (thInput Q fields payload) 189 3 = fields.step :=
    sliceBits_eq fun j hj ↦ by
      rw [show 189 + j = 128 + (56 + (5 + j)) by omega,
        inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_stepTag _ _ (by omega),
        BitVec.getLsbD_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hidx : sliceBits (thInput Q fields payload) 384 128 = payloadIndex payload :=
    congrArg ofBits (funext fun j ↦ by
      rw [show 384 + (j : ℕ) = 256 + (128 + j) by omega, inputBit_thInput_payload])
  have hf : fieldsOf (thInput Q fields payload) = fields := by
    rw [fieldsOf, hlo, hhi, htag, hstep]
  have hne : ¬((thInput Q fields payload).length = 40 ∧
      (thInput Q fields payload).take 8 = seedTag) := by
    rintro ⟨hl, -⟩
    rw [length_thInput_eq] at hl
    omega
  rw [slotOfInput, ite_eq_right hne, hQ, hf, hidx]

/-- The slot `slotOfAddress P P` assigns to a `P`-prefixed input with a payload of at least 32
bytes, from the QRPM proof's slot of its sponge tail. -/
theorem slotOfAddress_of_slotOf {P : PublicParameter} {fields : TweakFields} {payload : HashInput}
    (hp : 32 ≤ payload.length) {s : Slot}
    (h : Quantum.Xmss.slotOf P (Quantum.Sponge.absorbTail (Equiv.refl (Quantum.Xmss.X ×
      Quantum.Xmss.Z))
      (Quantum.Xmss.blocks (thInput P fields payload))) = some s) :
    slotOfAddress P P fields (payloadIndex payload) = some s :=
  (Quantum.Xmss.slotOf_thInput _ P P fields payload hp).symm.trans h

/-! ## The cells -/

/-- A message the scheme digests: at most `maxLen - 64` bytes (32 at the bottom layer, 16 at the
top). -/
abbrev MsgBytes : Type := {message : HashInput // message.length ≤ maxLen - 64}

/-- The data of a slot's input beyond the slot and the public parameter: a chain step's value,
a leaf's chain ends, a node's children, a digest's message and randomizer, the scheme seed of a
derivation, the key's seed `S_0` of the scheme seed. -/
def Payload : Slot → Type
  | .chain .. => Digest
  | .leaf .. => ChainIndex → Digest
  | .node .. => Digest × Digest
  | .msg .. => MsgBytes × Randomizer
  | .prf .. => MasterSeed
  | .rnd .. => MasterSeed × MsgBytes
  | .param => MasterSeed
  | .seed => MasterSeed

/-- **The input leanXMSS hashes at slot `s`** under the public parameter `P`, with payload `d`. -/
def slotInput (P : PublicParameter) : (s : Slot) → Payload s → HashInput
  | .chain layer key step chain, value =>
      thInput P (hashDomainFields (.chain layer key step)) (Verification.chainPayload chain value)
  | .leaf layer key, endpoints => thInput P (hashDomainFields (.leaf layer key))
      (digestsPayload endpoints)
  | .node layer level nodeIndex, children =>
      thInput P (hashDomainFields (.node layer level nodeIndex))
        (nodePayload children.1 children.2)
  | .msg layer key, d => thInput P (hashDomainFields (.message layer key))
      (d.1.1 ++ littleEndianBytes 16 d.2)
  | .prf layer key pair, seed =>
      thInput P (keygenDomainFields (.oneTimeChainPair layer key pair)) (littleEndianBytes 32 seed)
  | .rnd layer key, d => thInput P (tweakFields 7 0 (layerHi layer 0) key)
      (littleEndianBytes 32 d.1 ++ d.2.1)
  | .param, seed => thInput 0 (keygenDomainFields .parameter) (littleEndianBytes 32 seed)
  | .seed, keySeed => seedTag ++ littleEndianBytes 32 keySeed

theorem length_slotInput (P : PublicParameter) :
    ∀ (s : Slot) (d : Payload s), (slotInput P s d).length ≤ maxLen
  | .chain .., _ => length_thInput_chain _ _ _ _
  | .leaf .., _ => length_thInput_leaf _ _ _
  | .node .., _ => length_thInput_node _ _ _ _
  | .msg .., d => length_thInput_message _ _ d.1.2 _
  | .prf .., _ => length_thInput_seed _ _ _
  | .rnd .., d => length_thInput_randomizer _ _ _ d.2.2
  | .param, _ => length_thInput_seed _ _ _
  | .seed, _ => length_seedInput _

/-- **The cell of slot `s`**: the code of its input. -/
def cell (P : PublicParameter) (s : Slot) (d : Payload s) : HashDomain :=
  (encodeInput (slotInput P s d)).getD 0

theorem encodeInput_slotInput (P : PublicParameter) (s : Slot) (d : Payload s) :
    encodeInput (slotInput P s d) = some (cell P s d) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp
    (isSome_encodeInput_iff.mpr (length_slotInput P s d))
  rw [cell, hx]
  rfl

theorem decodeInput_cell (P : PublicParameter) (s : Slot) (d : Payload s) :
    decodeInput (cell P s d) = slotInput P s d :=
  decodeInput_of_encodeInput_eq_some (encodeInput_slotInput P s d)

/-- The random-oracle hash of a slot's input is one query at its cell. -/
theorem hashQ_slotInput (P : PublicParameter) (s : Slot) (d : Payload s) :
    hashQ (slotInput P s d) = liftM (RomOracles.query (.inr (cell P s d))) :=
  hashQ_of_encodeInput_eq_some (encodeInput_slotInput P s d)

/-! ## Each cell names its slot -/

/-- The slots whose address fits its fields: a node's level below `2^23` and index below
`2^32` (every honest node), every other slot. -/
def Addressable : Slot → Prop
  | .node _ level nodeIndex => level < 2 ^ 23 ∧ nodeIndex < 2 ^ 32
  | _ => True

theorem slotOfInput_slotInput (P : PublicParameter) :
    ∀ (s : Slot), Addressable s → ∀ d : Payload s, slotOfInput (slotInput P s d) = some s
  | .chain layer key step chain, _, value => by
    have hl : (Verification.chainPayload chain value).length = 32 := by
      simp only [Verification.chainPayload, littleEndianBytes, List.length_append,
        List.length_ofFn]
    rw [slotInput, slotOfInput_thInput _ _ _ (by omega)]
    exact slotOfAddress_of_slotOf (by omega) (Quantum.Xmss.slotOf_chain _ P layer key step chain
      value)
  | .leaf layer key, _, endpoints => by
    have hl : (digestsPayload endpoints).length = 928 := length_digestsPayload endpoints
    rw [slotInput, slotOfInput_thInput _ _ _ (by omega)]
    exact slotOfAddress_of_slotOf (by omega) (Quantum.Xmss.slotOf_leaf _ P layer key endpoints)
  | .node layer level nodeIndex, hs, children => by
    have hl : (nodePayload children.1 children.2).length = 32 := by
      simp only [nodePayload, littleEndianBytes, List.length_append, List.length_ofFn]
    rw [slotInput, slotOfInput_thInput _ _ _ (by omega)]
    exact slotOfAddress_of_slotOf (by omega)
      (Quantum.Xmss.slotOf_node _ P layer level nodeIndex hs.1 hs.2 children.1 children.2)
  | .msg layer key, _, d => by
    have hl : (d.1.1 ++ littleEndianBytes 16 d.2).length = d.1.1.length + 16 := by
      simp only [littleEndianBytes, List.length_append, List.length_ofFn]
    rw [slotInput, slotOfInput_thInput _ _ _ (by omega),
      slotOfAddress_self _ _ _ (by show BitVec.ofNat 5 12 ≠ 5; decide)]
    simp [fieldsSlot, hashDomainFields, tweakFields,
      Quantum.Xmss.layerOf_layerHi layer 0 (by norm_num), Quantum.Xmss.keyOf_ofNat]
  | .prf layer key pair, _, seed => by
    have hl : (littleEndianBytes 32 seed).length = 32 := List.length_ofFn
    rw [slotInput, slotOfInput_thInput _ _ _ (by omega)]
    exact slotOfAddress_of_slotOf (by omega) (Quantum.Xmss.slotOf_prf _ P layer key pair seed)
  | .rnd layer key, _, d => by
    have hl : (littleEndianBytes 32 d.1 ++ d.2.1).length = 32 + d.2.1.length := by
      simp only [littleEndianBytes, List.length_append, List.length_ofFn]
    rw [slotInput, slotOfInput_thInput _ _ _ (by omega)]
    exact slotOfAddress_of_slotOf (by omega) (Quantum.Xmss.slotOf_rnd _ P layer key d.1 d.2.1)
  | .param, _, seed => by
    have hl : (littleEndianBytes 32 seed).length = 32 := List.length_ofFn
    rw [slotInput, slotOfInput_thInput _ _ _ (by omega)]
    exact slotOfAddress_of_slotOf (by omega) (Quantum.Xmss.slotOf_param _ 0 seed)
  | .seed, _, keySeed => by
    have hl : (seedTag ++ littleEndianBytes 32 keySeed).length = 40 := by
      simp only [seedTag, littleEndianBytes, List.length_append, List.length_ofFn,
        List.length_cons, List.length_nil]
    rw [slotInput, slotOfInput, ite_eq_left ⟨hl, List.take_left' rfl⟩]

/-- **The cell of an addressable slot names that slot.** -/
theorem slotOf_cell (P : PublicParameter) {s : Slot} (hs : Addressable s) (d : Payload s) :
    slotOf (cell P s d) = some s := by
  rw [slotOf, decodeInput_cell]
  exact slotOfInput_slotInput P s hs d

/-! ## Distinct cells -/

theorem littleEndianBytes_inj {n : ℕ} {v w : BitVec (8 * n)}
    (h : littleEndianBytes n v = littleEndianBytes n w) : v = w :=
  BitVec.eq_of_getLsbD_eq fun j _ ↦ bitOf_injective (by
    rw [← inputBit_littleEndianBytes, h, inputBit_littleEndianBytes])

theorem flatMap_littleEndianBytes_inj :
    ∀ {a b : List (BitVec (8 * 16))}, a.length = b.length →
      a.flatMap (littleEndianBytes 16) = b.flatMap (littleEndianBytes 16) → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h
      (by simp only [littleEndianBytes, List.length_ofFn])
    rw [littleEndianBytes_inj h1, flatMap_littleEndianBytes_inj (by simpa using hl) h2]

theorem digestsPayload_inj {n : ℕ} {E E' : Fin n → Digest}
    (h : digestsPayload E = digestsPayload E') : E = E' :=
  List.ofFn_injective (flatMap_littleEndianBytes_inj
    (by exact List.length_ofFn.trans List.length_ofFn.symm) h)

/-- A slot's input determines its payload. -/
theorem slotInput_injective (P : PublicParameter) :
    ∀ (s : Slot) (d d' : Payload s), slotInput P s d = slotInput P s d' → d = d'
  | .chain .., v, v', h => littleEndianBytes_inj (List.append_inj (thInput_injective P h).2
      (by simp only [littleEndianBytes, List.length_ofFn])).1
  | .leaf .., E, E', h => digestsPayload_inj (thInput_injective P h).2
  | .node .., c, c', h => by
    obtain ⟨h1, h2⟩ := List.append_inj (thInput_injective P h).2
      (by simp only [littleEndianBytes, List.length_ofFn])
    exact Prod.ext (littleEndianBytes_inj h1) (littleEndianBytes_inj h2)
  | .msg .., d, d', h => by
    obtain ⟨h1, h2⟩ := List.append_inj' (thInput_injective P h).2
      (by simp only [littleEndianBytes, List.length_ofFn])
    exact Prod.ext (Subtype.ext h1) (littleEndianBytes_inj h2)
  | .prf .., S, S', h => littleEndianBytes_inj (thInput_injective P h).2
  | .rnd .., d, d', h => by
    obtain ⟨h1, h2⟩ := List.append_inj (thInput_injective P h).2
      (by simp only [littleEndianBytes, List.length_ofFn])
    exact Prod.ext (littleEndianBytes_inj h1) (Subtype.ext h2)
  | .param, S, S', h => littleEndianBytes_inj (thInput_injective 0 h).2
  | .seed, S, S', h => littleEndianBytes_inj (List.append_cancel_left h)

/-- **Distinct cells**: under one public parameter, the cells of two addressable slots are equal
only for the same slot and payload. -/
theorem cell_injective (P : PublicParameter) {s s' : Slot} (hs : Addressable s)
    (hs' : Addressable s') {d : Payload s} {d' : Payload s'} (h : cell P s d = cell P s' d') :
    (⟨s, d⟩ : Σ s, Payload s) = ⟨s', d'⟩ := by
  have hss : some s = some s' :=
    (slotOf_cell P hs d).symm.trans ((congrArg slotOf h).trans (slotOf_cell P hs' d'))
  obtain rfl := Option.some.inj hss
  have hd : slotInput P s d = slotInput P s d' := by
    rw [← decodeInput_cell, h, decodeInput_cell]
  rw [slotInput_injective P s d d' hd]

end Quantum.Qrom.Xmss

end
