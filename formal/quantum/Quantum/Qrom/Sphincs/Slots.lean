module

public import Quantum.Qrom.Sphincs.Scheme
public import Quantum.Sphincs.Keccak

@[expose] public section

/-!
# leanSPHINCS's hash inputs, byte by byte

Every input leanSPHINCS hashes belongs to one `Slot` (the QRPM's, `Quantum.Sphincs.Slot`); here
the slot is read from the input's bytes, a point of the random function's domain `HashDomain`:

* `slotOfInput pk`, `slotOf pk`: an 84-byte input is an `H_msg` call when its bytes `16` to `47`
  are `PK.seed ‖ PK.root` (`hmsgSlotOf`); a 93-byte input is `PRF_msg`, a 44-byte one the key
  expansion; any other is read as `PK.seed ‖ ADRS ‖ M` (the address words, `slotOfWords`).
  One lemma per kind of honest input: `slotOfInput_addressedHashInput`,
  `slotOfInput_messageDigestInput`, `slotOfInput_prfMessageInput`,
  `slotOfInput_keyDerivationInput`.
* `cell key root s p`: the honest input of the slot `s`, carrying the payload `p : SlotPayload s`
  (the hashed values), under the key `key` and the root `root`. `slotOf_cell`: its slot is `s`;
  `cell_injective`: distinct in-range slots and payloads have distinct cells.
* The `H_msg` prefix parse: `hmsgCallOf` reads the call of an 84-byte input from its last four
  bytes, `withCall` replaces them; `hmsgRoute` is the involution of `HashDomain × Bool` pairing
  the input `p ‖ BE_32(1)` with the second slot of the cell `p ‖ BE_32(0)`, the regrouping of the
  two digest calls.
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open HashSig.OverPermutation (nodePayload keccakHash)
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput)
open Quantum.Xmss (inputBit inputBit_append_left inputBit_append_right inputBit_littleEndianBytes
  length_littleEndianBytes ofBits getLsbD_ofBits bitOf bitOf_injective)
open Quantum.Sphincs (Slot slotOfWords slotOfAddress callOf callOf_ofNat domainSlot DomainInRange
  slotOfAddress_hashDomainFields slotOfAddress_keygenDomainFields messageDigestInput
  prfMessageInput length_messageDigestInput length_prfMessageInput length_keyDerivationInput
  length_addressedHashInput length_digestsPayload length_bigEndianBytes inputBit_bigEndianBytes
  toNat_ofNat_of_lt word_lt littleEndianBytes_injective bigEndianBytes_injective
  addressedHashInput_injective messageDigestInput_injective prfMessageInput_injective
  keyDerivationInput_injective val_lt_two_pow)

namespace Quantum.Qrom.Sphincs

/-! ## Reading words from bytes -/

/-- Bytes `start` to `start + n - 1` of an input, read as one little-endian word. -/
def leAt (input : HashInput) (start n : ℕ) : BitVec (8 * n) :=
  ofBits fun j : Fin (8 * n) ↦ inputBit input (8 * start + j)

/-- Bytes `start` to `start + n - 1` of an input, read as one big-endian word. -/
def beAt (input : HashInput) (start n : ℕ) : BitVec (8 * n) :=
  ofBits fun j : Fin (8 * n) ↦ inputBit input (8 * (start + (n - 1 - j / 8)) + j % 8)

theorem leAt_of_prefix {input a : HashInput} {start n : ℕ} {v : BitVec (8 * n)}
    (h : a ++ littleEndianBytes n v <+: input) (ha : a.length = start) :
    leAt input start n = v := by
  obtain ⟨b, rfl⟩ := h
  subst ha
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [leAt, getLsbD_ofBits _ j hj, List.append_assoc, inputBit_append_right,
    inputBit_append_left _ _ _ (by rw [length_littleEndianBytes]; omega),
    inputBit_littleEndianBytes]
  simp

theorem beAt_of_prefix {input a : HashInput} {start n : ℕ} {v : BitVec (8 * n)}
    (h : a ++ bigEndianBytes n v <+: input) (ha : a.length = start) :
    beAt input start n = v := by
  obtain ⟨b, rfl⟩ := h
  subst ha
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [beAt, getLsbD_ofBits _ j hj, List.append_assoc,
    show 8 * (a.length + (n - 1 - j / 8)) + j % 8 = 8 * a.length + (8 * (n - 1 - j / 8) + j % 8)
      by omega, inputBit_append_right,
    inputBit_append_left _ _ _ (by rw [length_bigEndianBytes]; omega),
    inputBit_bigEndianBytes _ _ _ (by omega),
    show 8 * (n - 1 - (8 * (n - 1 - j / 8) + j % 8) / 8) + (8 * (n - 1 - j / 8) + j % 8) % 8 = j
      by omega]
  simp

/-- Bytes `start` to `start + 15` of an input, read as a little-endian digest. -/
def leDigest (input : HashInput) (start : ℕ) : Digest :=
  leAt input start 16

theorem leDigest_of_prefix {input a : HashInput} {start : ℕ} {v : Digest}
    (h : a ++ littleEndianBytes 16 v <+: input) (ha : a.length = start) :
    leDigest input start = v :=
  leAt_of_prefix h ha

/-! ## The slot of an input -/

/-- The `H_msg` slot of an 84-byte input for the key `pk`: bytes `16` to `47` must be
`PK.seed ‖ PK.root`; the randomizer is bytes `0` to `15`, the message bytes `48` to `79`, the call
the big-endian counter at bytes `80` to `83`. -/
def hmsgSlotOf (pk : PublicKey) (input : HashInput) : Option Slot :=
  if leAt input 16 16 = pk.publicSeed ∧ leDigest input 32 = pk.root then
    (callOf (beAt input 80 4)).map (.hmsg (leDigest input 0) (leAt input 48 32))
  else none

/-- **The slot of an input** for the key `pk`: by its length an `H_msg` call (84 bytes),
`PRF_msg` (93 bytes, its message the bytes `61` to `92`) or the key expansion (44 bytes, its
domain byte `43`); else, when its first 16 bytes are `PK.seed`, the slot its address words name
(bytes `16` to `47`, the zero word at `20` to `23` unread). -/
def slotOfInput (pk : PublicKey) (input : HashInput) : Option Slot :=
  if input.length = 84 then hmsgSlotOf pk input
  else if input.length = 93 then some (.prfMsg (leAt input 61 32))
  else if input.length = 44 then some (.expand (input.getD 43 0))
  else if leAt input 0 16 = pk.publicSeed then
    slotOfWords (beAt input 16 4).toNat (beAt input 24 8).toNat (beAt input 32 4).toNat
      (beAt input 36 4).toNat (beAt input 40 4).toNat (beAt input 44 4).toNat
  else none

/-- **The slot of a point of the domain**: the slot of the byte string it codes. -/
def slotOf (pk : PublicKey) (x : Qrom.HashDomain) : Option Slot :=
  slotOfInput pk (decodeInput x)

theorem slotOf_of_encodeInput_eq_some (pk : PublicKey) {input : HashInput} {x : Qrom.HashDomain}
    (h : encodeInput input = some x) : slotOf pk x = slotOfInput pk input := by
  rw [slotOf, decodeInput_of_encodeInput_eq_some h]

/-- The slot of an addressed input (a payload of neither 36 nor 45 bytes, so that the input has
none of the special lengths): the slot its address names, if its prefix is `PK.seed`. -/
theorem slotOfInput_addressedHashInput (pk : PublicKey) (Q : PublicParameter) (a : Address)
    (payload : HashInput) (h36 : payload.length ≠ 36) (h45 : payload.length ≠ 45) :
    slotOfInput pk (addressedHashInput Q a payload) =
      if Q = pk.publicSeed then slotOfAddress a else none := by
  have hl := length_addressedHashInput Q a payload
  have e : addressedHashInput Q a payload = littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++
      bigEndianBytes 4 0 ++ bigEndianBytes 8 a.tree ++
      bigEndianBytes 4 (BitVec.ofNat 32 a.addressType.word) ++ bigEndianBytes 4 a.keyPair ++
      bigEndianBytes 4 a.chainOrTreeHeight ++ bigEndianBytes 4 a.hashOrTreeIndex ++ payload := by
    simp [addressedHashInput, hasherInput, Address.toBytes]
  have hQ : leAt (addressedHashInput Q a payload) 0 16 = Q :=
    leAt_of_prefix (a := []) (by rw [e]; simp) rfl
  have hy : beAt (addressedHashInput Q a payload) 16 4 = a.layer :=
    beAt_of_prefix (a := littleEndianBytes 16 Q) (by rw [e]; simp) (length_littleEndianBytes _ _)
  have ht : beAt (addressedHashInput Q a payload) 24 8 = a.tree :=
    beAt_of_prefix (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0)
      (by rw [e]; simp) (by simp [length_littleEndianBytes, length_bigEndianBytes])
  have hw : beAt (addressedHashInput Q a payload) 32 4 = BitVec.ofNat 32 a.addressType.word :=
    beAt_of_prefix (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0 ++
      bigEndianBytes 8 a.tree) (by rw [e]; simp)
      (by simp [length_littleEndianBytes, length_bigEndianBytes])
  have hk : beAt (addressedHashInput Q a payload) 36 4 = a.keyPair :=
    beAt_of_prefix (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0 ++
      bigEndianBytes 8 a.tree ++ bigEndianBytes 4 (BitVec.ofNat 32 a.addressType.word))
      (by rw [e]; simp) (by simp [length_littleEndianBytes, length_bigEndianBytes])
  have hc : beAt (addressedHashInput Q a payload) 40 4 = a.chainOrTreeHeight :=
    beAt_of_prefix (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0 ++
      bigEndianBytes 8 a.tree ++ bigEndianBytes 4 (BitVec.ofNat 32 a.addressType.word) ++
      bigEndianBytes 4 a.keyPair) (by rw [e]; simp)
      (by simp [length_littleEndianBytes, length_bigEndianBytes])
  have hh : beAt (addressedHashInput Q a payload) 44 4 = a.hashOrTreeIndex :=
    beAt_of_prefix (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0 ++
      bigEndianBytes 8 a.tree ++ bigEndianBytes 4 (BitVec.ofNat 32 a.addressType.word) ++
      bigEndianBytes 4 a.keyPair ++ bigEndianBytes 4 a.chainOrTreeHeight) (by rw [e]; simp)
      (by simp [length_littleEndianBytes, length_bigEndianBytes])
  rw [slotOfInput, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), hQ,
    hy, ht, hw, hk, hc,
    hh, toNat_ofNat_of_lt (lt_of_lt_of_le (word_lt _) (by norm_num))]
  rfl

/-- A tweakable hash at an in-range domain under the key `pk` has the domain's slot. -/
theorem slotOfInput_tweakable (pk : PublicKey) (d : _root_.Sphincs.HashDomain)
    (hd : DomainInRange d) (payload : HashInput) (h36 : payload.length ≠ 36)
    (h45 : payload.length ≠ 45) :
    slotOfInput pk (addressedHashInput pk.publicSeed (hashDomainFields d) payload) =
      some (domainSlot d) := by
  rw [slotOfInput_addressedHashInput _ _ _ _ h36 h45, ite_eq_left rfl,
    slotOfAddress_hashDomainFields d hd]

/-- A secret, `PRF(PK.seed, SK.seed, ADRS)`, under the key `pk`. -/
theorem slotOfInput_prf (pk : PublicKey) (d : KeygenDomain) (secretSeed : MasterSeed) :
    slotOfInput pk (addressedHashInput pk.publicSeed (keygenDomainFields d)
      (littleEndianBytes 32 secretSeed)) = some (.prf d) := by
  rw [slotOfInput_addressedHashInput _ _ _ _ (by simp [length_littleEndianBytes])
    (by simp [length_littleEndianBytes]), ite_eq_left rfl, slotOfAddress_keygenDomainFields]

/-- **The slot of an `H_msg` call**: `hmsg R M i` when the call is under the key `pk`, whatever
the randomizer. -/
theorem slotOfInput_messageDigestInput (pk : PublicKey) (randomizer : Randomizer)
    (publicSeed : PublicParameter) (root : Digest) (message : Message) (call : DigestCall) :
    slotOfInput pk (messageDigestInput randomizer publicSeed root message call) =
      if publicSeed = pk.publicSeed ∧ root = pk.root then some (.hmsg randomizer message call)
      else none := by
  have hl := length_messageDigestInput randomizer publicSeed root message call
  have e : messageDigestInput randomizer publicSeed root message call =
      littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++
        littleEndianBytes 16 root ++ littleEndianBytes 32 message ++
        bigEndianBytes 4 (BitVec.ofNat 32 call.val) := rfl
  have hR : leDigest (messageDigestInput randomizer publicSeed root message call) 0 =
      randomizer := leDigest_of_prefix (a := []) (by rw [e]; simp) rfl
  have hQ : leAt (messageDigestInput randomizer publicSeed root message call) 16 16 =
      publicSeed := leAt_of_prefix (a := littleEndianBytes 16 randomizer) (by rw [e]; simp)
        (by simp [littleEndianBytes])
  have hr : leDigest (messageDigestInput randomizer publicSeed root message call) 32 = root :=
    leDigest_of_prefix (a := littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed)
      (by rw [e]; simp) (by simp [littleEndianBytes])
  have hM : leAt (messageDigestInput randomizer publicSeed root message call) 48 32 = message :=
    leAt_of_prefix (a := littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++
      littleEndianBytes 16 root) (by rw [e]; simp) (by simp [littleEndianBytes])
  have hc : beAt (messageDigestInput randomizer publicSeed root message call) 80 4 =
      BitVec.ofNat 32 call.val :=
    beAt_of_prefix (a := littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++
      littleEndianBytes 16 root ++ littleEndianBytes 32 message) (by rw [e])
      (by simp [littleEndianBytes])
  rw [slotOfInput, ite_eq_left hl, hmsgSlotOf, hQ, hr, hR, hM, hc, callOf_ofNat, Option.map_some]

/-- `PRF_msg` has the slot `prfMsg M`. -/
theorem slotOfInput_prfMessageInput (pk : PublicKey) (secretPrfKey : HashOutput)
    (optionalRandomness : Digest) (message : Message) :
    slotOfInput pk (prfMessageInput secretPrfKey optionalRandomness message) =
      some (.prfMsg message) := by
  have hl := length_prfMessageInput secretPrfKey optionalRandomness message
  have hM : leAt (prfMessageInput secretPrfKey optionalRandomness message) 61 32 = message :=
    leAt_of_prefix (a := littleEndianBytes 32 secretPrfKey ++
      littleEndianBytes 16 optionalRandomness ++ [0x00, UInt8.ofNat contextString.length] ++
      contextString) (by simp [prfMessageInput, framedMessage])
      (by simp [contextString, seedTag, littleEndianBytes])
  rw [slotOfInput, ite_eq_right (by omega), ite_eq_left hl, hM]

/-- The key expansion `H(leanSPHINCS ‖ SK.seed ‖ domain)` has the slot `expand domain`. -/
theorem slotOfInput_keyDerivationInput (pk : PublicKey) (secretSeed : MasterSeed)
    (domain : UInt8) :
    slotOfInput pk (keyDerivationInput secretSeed domain) = some (.expand domain) := by
  have hl := length_keyDerivationInput secretSeed domain
  have hpre : (seedTag ++ littleEndianBytes 32 secretSeed).length = 43 := by
    simp [seedTag, length_littleEndianBytes]
  have hd : (keyDerivationInput secretSeed domain).getD 43 0 = domain := by
    rw [keyDerivationInput, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      hpre]
    rfl
  rw [slotOfInput, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hl, hd]

/-! ## Honest inputs and their cells -/

/-- The values the honest input of a slot hashes: a chain value, the chain ends, the two
children, the encoded message and the counter, a FORS secret, the FORS roots; nothing for the
secrets, the digest calls, `PRF_msg` and the key expansion, whose inputs the key and the slot
fix. -/
def SlotPayload : Slot → Type
  | .chain .. => Digest
  | .leaf .. => ChainIndex → Digest
  | .node .. => Digest × Digest
  | .enc .. => Digest × EncodingCounter
  | .forsLeaf .. => Digest
  | .forsNode .. => Digest × Digest
  | .forsRoots _ => ForsTreeIndex → Digest
  | .prf _ => Unit
  | .hmsg .. => Unit
  | .prfMsg _ => Unit
  | .expand _ => Unit

/-- The slots the scheme uses: a hypertree node's height and index fit in a word, a FORS node has
height `1` to `a` and index below `2^(a - height)` (`DomainInRange`). -/
def SlotInRange : Slot → Prop
  | .node _ _ height nodeIndex => height < 2 ^ 32 ∧ nodeIndex < 2 ^ 32
  | .forsNode _ _ height node =>
      0 < height ∧ height ≤ forsTreeHeight ∧ node < 2 ^ (forsTreeHeight - height)
  | _ => True

/-- **The honest input of a slot**, under the expanded key `key` and the root `root`: the input
the scheme hashes at the slot `s` with the payload `p`. -/
def slotInput (key : ExpandedKey) (root : Digest) : (s : Slot) → SlotPayload s → HashInput
  | .chain layer tree leaf chainIndex step, value =>
      addressedHashInput key.publicSeed (hashDomainFields (.chain layer tree leaf chainIndex step))
        (littleEndianBytes 16 value)
  | .leaf layer tree leaf, endpoints =>
      addressedHashInput key.publicSeed (hashDomainFields (.leaf layer tree leaf))
        (digestsPayload endpoints)
  | .node layer tree height nodeIndex, children =>
      addressedHashInput key.publicSeed (hashDomainFields (.node layer tree height nodeIndex))
        (nodePayload children.1 children.2)
  | .enc layer tree leaf, trial =>
      addressedHashInput key.publicSeed (hashDomainFields (.encoding layer tree leaf))
        (littleEndianBytes 16 trial.1 ++ bigEndianBytes 4 trial.2)
  | .forsLeaf index forsTree forsLeaf, secret =>
      addressedHashInput key.publicSeed (hashDomainFields (.forsLeaf index forsTree forsLeaf))
        (littleEndianBytes 16 secret)
  | .forsNode index forsTree height node, children =>
      addressedHashInput key.publicSeed (hashDomainFields (.forsNode index forsTree height node))
        (nodePayload children.1 children.2)
  | .forsRoots index, roots =>
      addressedHashInput key.publicSeed (hashDomainFields (.forsRoots index)) (digestsPayload roots)
  | .prf domain, _ =>
      addressedHashInput key.publicSeed (keygenDomainFields domain)
        (littleEndianBytes 32 key.secretSeed)
  | .hmsg randomizer message call, _ =>
      messageDigestInput randomizer key.publicSeed root message call
  | .prfMsg message, _ => prfMessageInput key.secretPrfKey key.publicSeed message
  | .expand domain, _ => keyDerivationInput key.secretSeed domain

theorem length_slotInput_le (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    (slotInput key root s p).length ≤ maxLen := by
  cases s with
  | chain | forsLeaf | prf =>
    simp [slotInput, length_addressedHashInput, littleEndianBytes, maxLen]
  | node | forsNode =>
    simp [slotInput, length_addressedHashInput, nodePayload, littleEndianBytes, maxLen]
  | enc => simp [slotInput, length_addressedHashInput, littleEndianBytes, bigEndianBytes, maxLen]
  | leaf =>
    rw [slotInput, length_addressedHashInput, length_digestsPayload (n := chainCount) p]
    decide
  | forsRoots =>
    rw [slotInput, length_addressedHashInput, length_digestsPayload (n := forsTreeCount) p]
    decide
  | hmsg => rw [slotInput, length_messageDigestInput]; decide
  | prfMsg message =>
    rw [slotInput, length_prfMessageInput key.secretPrfKey key.publicSeed message]
    decide
  | expand => rw [slotInput, length_keyDerivationInput]; decide

/-- The code of a byte string of at most `maxLen` bytes: `encodeInput` without the option. -/
def codeOf (input : HashInput) (h : input.length ≤ maxLen) : Qrom.HashDomain :=
  (⟨input.length, Nat.lt_succ_of_le h⟩, fun i ↦ input.getD i 0)

theorem encodeInput_eq_codeOf {input : HashInput} (h : input.length ≤ maxLen) :
    encodeInput input = some (codeOf input h) :=
  encodeInput_of_length_le h

theorem decodeInput_codeOf {input : HashInput} (h : input.length ≤ maxLen) :
    decodeInput (codeOf input h) = input :=
  decodeInput_of_encodeInput_eq_some (encodeInput_eq_codeOf h)

theorem codeOf_congr {input input' : HashInput} (e : input = input')
    (h : input.length ≤ maxLen) (h' : input'.length ≤ maxLen) :
    codeOf input h = codeOf input' h' := by
  subst e
  rfl

/-- **The cell of a slot**: the code of its honest input. -/
def cell (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) : Qrom.HashDomain :=
  codeOf (slotInput key root s p) (length_slotInput_le key root s p)

theorem encodeInput_slotInput (key : ExpandedKey) (root : Digest) (s : Slot)
    (p : SlotPayload s) : encodeInput (slotInput key root s p) = some (cell key root s p) :=
  encodeInput_eq_codeOf (length_slotInput_le key root s p)

/-- **The slot of a cell** is its slot, under the key's public key. -/
theorem slotOf_cell (key : ExpandedKey) (root : Digest) {s : Slot} (hs : SlotInRange s)
    (p : SlotPayload s) : slotOf ⟨key.publicSeed, root⟩ (cell key root s p) = some s := by
  rw [slotOf_of_encodeInput_eq_some _ (encodeInput_slotInput key root s p)]
  cases s with
  | chain layer tree leaf chainIndex step =>
    exact slotOfInput_tweakable ⟨key.publicSeed, root⟩ (.chain layer tree leaf chainIndex step)
      trivial _ (by simp [littleEndianBytes]) (by simp [littleEndianBytes])
  | leaf layer tree leaf =>
    exact slotOfInput_tweakable ⟨key.publicSeed, root⟩ (.leaf layer tree leaf) trivial _
      (by rw [length_digestsPayload (n := chainCount) p]; decide)
      (by rw [length_digestsPayload (n := chainCount) p]; decide)
  | node layer tree height nodeIndex =>
    exact slotOfInput_tweakable ⟨key.publicSeed, root⟩ (.node layer tree height nodeIndex) hs _
      (by simp [nodePayload, littleEndianBytes]) (by simp [nodePayload, littleEndianBytes])
  | enc layer tree leaf =>
    exact slotOfInput_tweakable ⟨key.publicSeed, root⟩ (.encoding layer tree leaf) trivial _
      (by simp [littleEndianBytes, bigEndianBytes]) (by simp [littleEndianBytes, bigEndianBytes])
  | forsLeaf index forsTree forsLeaf =>
    exact slotOfInput_tweakable ⟨key.publicSeed, root⟩ (.forsLeaf index forsTree forsLeaf)
      trivial _ (by simp [littleEndianBytes]) (by simp [littleEndianBytes])
  | forsNode index forsTree height node =>
    exact slotOfInput_tweakable ⟨key.publicSeed, root⟩ (.forsNode index forsTree height node) hs _
      (by simp [nodePayload, littleEndianBytes]) (by simp [nodePayload, littleEndianBytes])
  | forsRoots index =>
    exact slotOfInput_tweakable ⟨key.publicSeed, root⟩ (.forsRoots index) trivial _
      (by rw [length_digestsPayload (n := forsTreeCount) p]; decide)
      (by rw [length_digestsPayload (n := forsTreeCount) p]; decide)
  | prf domain => exact slotOfInput_prf ⟨key.publicSeed, root⟩ domain key.secretSeed
  | hmsg randomizer message call =>
    rw [slotInput, slotOfInput_messageDigestInput, ite_eq_left ⟨rfl, rfl⟩]
  | prfMsg message => exact slotOfInput_prfMessageInput _ _ _ _
  | expand domain => exact slotOfInput_keyDerivationInput _ _ _

theorem digestsPayload_injective {n : ℕ} : Function.Injective (digestsPayload (n := n)) := by
  have h : ∀ l l' : List (BitVec (8 * 16)), l.length = l'.length →
      l.flatMap (littleEndianBytes 16) = l'.flatMap (littleEndianBytes 16) → l = l' := by
    intro l
    induction l with
    | nil => intro l' hl _; exact (List.eq_nil_of_length_eq_zero hl.symm).symm
    | cons a l ih =>
      intro l' hl he
      cases l' with
      | nil => simp at hl
      | cons a' l' =>
        rw [List.flatMap_cons, List.flatMap_cons] at he
        obtain ⟨h1, h2⟩ := List.append_inj he
          (by rw [length_littleEndianBytes, length_littleEndianBytes])
        rw [littleEndianBytes_injective 16 h1, ih l' (by simpa using hl) h2]
  intro f g hfg
  apply List.ofFn_injective
  exact h (List.ofFn f) (List.ofFn g) (List.length_ofFn.trans List.length_ofFn.symm) hfg

theorem nodePayload_injective {a b a' b' : Digest} (h : nodePayload a b = nodePayload a' b') :
    a = a' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := List.append_inj h
    (by simp [littleEndianBytes])
  exact ⟨littleEndianBytes_injective 16 h1, littleEndianBytes_injective 16 h2⟩

/-- At a fixed slot, the honest input determines the payload. -/
theorem slotInput_injective (key : ExpandedKey) (root : Digest) (s : Slot) :
    Function.Injective (slotInput key root s) := by
  intro p p' h
  cases s with
  | chain => exact littleEndianBytes_injective 16 (addressedHashInput_injective _ h).2
  | leaf => exact digestsPayload_injective (addressedHashInput_injective _ h).2
  | node =>
    obtain ⟨h1, h2⟩ := nodePayload_injective (addressedHashInput_injective _ h).2
    exact Prod.ext h1 h2
  | enc =>
    obtain ⟨h1, h2⟩ := List.append_inj (addressedHashInput_injective _ h).2
      (by simp [littleEndianBytes])
    exact Prod.ext (littleEndianBytes_injective 16 h1) (bigEndianBytes_injective 4 h2)
  | forsLeaf => exact littleEndianBytes_injective 16 (addressedHashInput_injective _ h).2
  | forsNode =>
    obtain ⟨h1, h2⟩ := nodePayload_injective (addressedHashInput_injective _ h).2
    exact Prod.ext h1 h2
  | forsRoots => exact digestsPayload_injective (addressedHashInput_injective _ h).2
  | prf => rfl
  | hmsg => rfl
  | prfMsg => rfl
  | expand => rfl

/-- **Distinct in-range slots and payloads have distinct cells.** -/
theorem cell_injective (key : ExpandedKey) (root : Digest) {s s' : Slot} (hs : SlotInRange s)
    (hs' : SlotInRange s') {p : SlotPayload s} {p' : SlotPayload s'}
    (h : cell key root s p = cell key root s' p') :
    (⟨s, p⟩ : Σ s, SlotPayload s) = ⟨s', p'⟩ := by
  have hss := slotOf_cell key root hs p
  rw [h, slotOf_cell key root hs' p'] at hss
  obtain rfl : s' = s := Option.some_injective _ hss
  have hi : slotInput key root _ p = slotInput key root _ p' :=
    encodeInput_injective (encodeInput_slotInput key root _ p)
      ((encodeInput_slotInput key root _ p').trans (congrArg some h.symm))
  obtain rfl := slotInput_injective key root _ hi
  rfl

/-- Cells of distinct in-range slots differ. -/
theorem slot_eq_of_cell_eq (key : ExpandedKey) (root : Digest) {s s' : Slot}
    (hs : SlotInRange s) (hs' : SlotInRange s') {p : SlotPayload s} {p' : SlotPayload s'}
    (h : cell key root s p = cell key root s' p') : s = s' :=
  congrArg Sigma.fst (cell_injective key root hs hs' h)

/-! ## The scheme's hash calls at their inputs -/

theorem messageDigestCall_eq {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput)
    (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest) (message : Message)
    (call : DigestCall) :
    LeanSphincsOver.messageDigestCall hash randomizer publicSeed root message call =
      hash (messageDigestInput randomizer publicSeed root message call) :=
  rfl

theorem prfMessage_eq {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput)
    (secretPrfKey : HashOutput) (optionalRandomness : Digest) (message : Message) :
    LeanSphincsOver.prfMessage hash secretPrfKey optionalRandomness message =
      hash (prfMessageInput secretPrfKey optionalRandomness message) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

/-! ## The `H_msg` prefix parse -/

/-- The counter of digest call `call`, `BE_32(call)`: the last four bytes of its input. -/
def callBytes (call : DigestCall) : HashInput :=
  bigEndianBytes 4 (BitVec.ofNat 32 call.val)

theorem length_callBytes (call : DigestCall) : (callBytes call).length = 4 :=
  length_bigEndianBytes _ _

theorem callBytes_injective : Function.Injective callBytes := by
  intro i i' h
  have hi := congrArg BitVec.toNat (bigEndianBytes_injective 4 h)
  rw [toNat_ofNat_of_lt (val_lt_two_pow i (by norm_num [digestCallCount])),
    toNat_ofNat_of_lt (val_lt_two_pow i' (by norm_num [digestCallCount]))] at hi
  exact Fin.ext hi

/-- The 80 bytes `R ‖ PK.seed ‖ PK.root ‖ M` both calls of `H_msg` share. -/
def hmsgPrefix (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest)
    (message : Message) : HashInput :=
  littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++ littleEndianBytes 16 root ++
    littleEndianBytes 32 message

theorem length_hmsgPrefix (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest)
    (message : Message) : (hmsgPrefix randomizer publicSeed root message).length = 80 := by
  simp [hmsgPrefix, littleEndianBytes]

theorem messageDigestInput_eq (randomizer : Randomizer) (publicSeed : PublicParameter)
    (root : Digest) (message : Message) (call : DigestCall) :
    messageDigestInput randomizer publicSeed root message call =
      hmsgPrefix randomizer publicSeed root message ++ callBytes call :=
  rfl

/-- **The `H_msg` parse**: the call an input names, when it has 84 bytes, the last four the
counter of a digest call. -/
def hmsgCallOf (input : HashInput) : Option DigestCall :=
  if input.length = 84 then
    if input.drop 80 = callBytes 0 then some 0
    else if input.drop 80 = callBytes 1 then some 1
    else none
  else none

theorem hmsgCallOf_eq_some_iff {input : HashInput} {call : DigestCall} :
    hmsgCallOf input = some call ↔ input.length = 84 ∧ input.drop 80 = callBytes call := by
  constructor
  · intro h
    unfold hmsgCallOf at h
    split_ifs at h with hl h0 h1 <;> cases h
    exacts [⟨hl, h0⟩, ⟨hl, h1⟩]
  · rintro ⟨hl, hd⟩
    have hv : call.val = 0 ∨ call.val = 1 := by
      have := call.isLt
      simp only [digestCallCount] at this
      omega
    rcases hv with hv | hv
    · obtain rfl : call = 0 := Fin.ext hv
      rw [hmsgCallOf, ite_eq_left hl, ite_eq_left hd]
    · obtain rfl : call = 1 := Fin.ext hv
      rw [hmsgCallOf, ite_eq_left hl,
        ite_eq_right fun h0 ↦ absurd (callBytes_injective (h0.symm.trans hd)) (by decide),
        ite_eq_left hd]

/-- The input with its last four bytes replaced by the counter of `call`. -/
def withCall (input : HashInput) (call : DigestCall) : HashInput :=
  input.take 80 ++ callBytes call

theorem length_withCall_le (input : HashInput) (call : DigestCall) :
    (withCall input call).length ≤ 84 := by
  rw [withCall, List.length_append, List.length_take, length_callBytes]
  omega

theorem withCall_withCall {input : HashInput} (h : 80 ≤ input.length) (call call' : DigestCall) :
    withCall (withCall input call) call' = withCall input call' := by
  unfold withCall
  rw [List.take_left' (List.length_take_of_le h)]

theorem withCall_of_hmsgCallOf {input : HashInput} {call : DigestCall}
    (h : hmsgCallOf input = some call) : withCall input call = input := by
  rw [withCall, ← (hmsgCallOf_eq_some_iff.mp h).2, List.take_append_drop]

theorem hmsgCallOf_withCall {input : HashInput} (h : 80 ≤ input.length) (call : DigestCall) :
    hmsgCallOf (withCall input call) = some call := by
  have ht : (input.take 80).length = 80 := List.length_take_of_le h
  exact hmsgCallOf_eq_some_iff.mpr
    ⟨by rw [withCall, List.length_append, ht, length_callBytes],
      by rw [withCall, List.drop_left' ht]⟩

theorem hmsgCallOf_messageDigestInput (randomizer : Randomizer) (publicSeed : PublicParameter)
    (root : Digest) (message : Message) (call : DigestCall) :
    hmsgCallOf (messageDigestInput randomizer publicSeed root message call) = some call :=
  hmsgCallOf_eq_some_iff.mpr ⟨length_messageDigestInput _ _ _ _ _,
    by rw [messageDigestInput_eq, List.drop_left' (length_hmsgPrefix _ _ _ _)]⟩

theorem withCall_messageDigestInput (randomizer : Randomizer) (publicSeed : PublicParameter)
    (root : Digest) (message : Message) (call call' : DigestCall) :
    withCall (messageDigestInput randomizer publicSeed root message call) call' =
      messageDigestInput randomizer publicSeed root message call' := by
  rw [withCall, messageDigestInput_eq, List.take_left' (length_hmsgPrefix _ _ _ _)]
  rfl

/-- The digest call a point of the domain names: that of the byte string it codes, when it is
that string's code (zero padding). -/
def hmsgCall (x : Qrom.HashDomain) : Option DigestCall :=
  if encodeInput (decodeInput x) = some x then hmsgCallOf (decodeInput x) else none

theorem hmsgCall_of_encodeInput_eq_some {input : HashInput} {x : Qrom.HashDomain}
    (h : encodeInput input = some x) : hmsgCall x = hmsgCallOf input := by
  rw [hmsgCall, decodeInput_of_encodeInput_eq_some h, ite_eq_left h]

theorem hmsgCall_eq_some_iff {x : Qrom.HashDomain} {call : DigestCall} :
    hmsgCall x = some call ↔
      encodeInput (decodeInput x) = some x ∧ hmsgCallOf (decodeInput x) = some call := by
  unfold hmsgCall
  by_cases hc : encodeInput (decodeInput x) = some x
  · rw [ite_eq_left hc]
    exact ⟨fun h ↦ ⟨hc, h⟩, And.right⟩
  · rw [ite_eq_right hc]
    exact ⟨(fun h ↦ by cases h), fun h ↦ absurd h.1 hc⟩

/-- The point coding the byte string of `x` with its call replaced by `call`. -/
def hmsgPartner (x : Qrom.HashDomain) (call : DigestCall) : Qrom.HashDomain :=
  codeOf (withCall (decodeInput x) call) ((length_withCall_le _ _).trans (by decide))

theorem hmsgPartner_of_encodeInput_eq_some {input : HashInput} {x y : Qrom.HashDomain}
    {call : DigestCall} (h : encodeInput input = some x)
    (h' : encodeInput (withCall input call) = some y) : hmsgPartner x call = y := by
  have e : withCall (decodeInput x) call = withCall input call := by
    rw [decodeInput_of_encodeInput_eq_some h]
  have hl : (withCall input call).length ≤ maxLen := (length_withCall_le _ _).trans (by decide)
  rw [hmsgPartner, codeOf_congr e _ hl]
  exact Option.some_injective _ ((encodeInput_eq_codeOf hl).symm.trans h')

theorem hmsgCall_hmsgPartner {x : Qrom.HashDomain} {call : DigestCall}
    (hx : hmsgCall x = some call) (call' : DigestCall) :
    hmsgCall (hmsgPartner x call') = some call' := by
  obtain ⟨-, hx⟩ := hmsgCall_eq_some_iff.mp hx
  have hl := (hmsgCallOf_eq_some_iff.mp hx).1
  rw [hmsgPartner, hmsgCall_of_encodeInput_eq_some (encodeInput_eq_codeOf _),
    hmsgCallOf_withCall (by omega)]

theorem hmsgPartner_hmsgPartner {x : Qrom.HashDomain} {call : DigestCall}
    (hx : hmsgCall x = some call) (call' : DigestCall) :
    hmsgPartner (hmsgPartner x call') call = x := by
  obtain ⟨hc, hx⟩ := hmsgCall_eq_some_iff.mp hx
  have hl := (hmsgCallOf_eq_some_iff.mp hx).1
  have e : withCall (decodeInput (hmsgPartner x call')) call = decodeInput x := by
    rw [hmsgPartner, decodeInput_codeOf, withCall_withCall (by omega), withCall_of_hmsgCallOf hx]
  have hd : (decodeInput x).length ≤ maxLen := by rw [hl]; decide
  rw [hmsgPartner, codeOf_congr e _ hd]
  exact Option.some_injective _ ((encodeInput_eq_codeOf hd).symm.trans hc)

/-- The routing of `H_msg` call 1 onto the cell of call 0: `(p ‖ BE_32(1), false)` and
`(p ‖ BE_32(0), true)` are exchanged, every other pair is fixed. -/
def hmsgRouteFun (p : Qrom.HashDomain × Bool) : Qrom.HashDomain × Bool :=
  if hmsgCall p.1 = some 1 ∧ p.2 = false then (hmsgPartner p.1 0, true)
  else if hmsgCall p.1 = some 0 ∧ p.2 = true then (hmsgPartner p.1 1, false)
  else p

theorem hmsgRouteFun_one {x : Qrom.HashDomain} (hx : hmsgCall x = some 1) :
    hmsgRouteFun (x, false) = (hmsgPartner x 0, true) := by
  show (if hmsgCall x = some 1 ∧ false = false then (hmsgPartner x 0, true)
    else if hmsgCall x = some 0 ∧ false = true then (hmsgPartner x 1, false) else (x, false)) = _
  exact ite_eq_left (show hmsgCall x = some 1 ∧ false = false from ⟨hx, rfl⟩)

theorem hmsgRouteFun_zero {x : Qrom.HashDomain} (hx : hmsgCall x = some 0) :
    hmsgRouteFun (x, true) = (hmsgPartner x 1, false) := by
  show (if hmsgCall x = some 1 ∧ true = false then (hmsgPartner x 0, true)
    else if hmsgCall x = some 0 ∧ true = true then (hmsgPartner x 1, false) else (x, true)) = _
  rw [ite_eq_right (show ¬(hmsgCall x = some 1 ∧ true = false) from fun h ↦ absurd h.2 (by decide)),
    ite_eq_left (show hmsgCall x = some 0 ∧ true = true from ⟨hx, rfl⟩)]

theorem hmsgRouteFun_of_not {x : Qrom.HashDomain} {b : Bool}
    (h1 : ¬(hmsgCall x = some 1 ∧ b = false)) (h0 : ¬(hmsgCall x = some 0 ∧ b = true)) :
    hmsgRouteFun (x, b) = (x, b) := by
  show (if hmsgCall x = some 1 ∧ b = false then (hmsgPartner x 0, true)
    else if hmsgCall x = some 0 ∧ b = true then (hmsgPartner x 1, false) else (x, b)) = _
  rw [ite_eq_right h1, ite_eq_right h0]

theorem hmsgRouteFun_involutive : Function.Involutive hmsgRouteFun := by
  rintro ⟨x, b⟩
  by_cases h1 : hmsgCall x = some 1 ∧ b = false
  · obtain ⟨hx, rfl⟩ := h1
    rw [hmsgRouteFun_one hx, hmsgRouteFun_zero (hmsgCall_hmsgPartner hx 0),
      hmsgPartner_hmsgPartner hx]
  · by_cases h0 : hmsgCall x = some 0 ∧ b = true
    · obtain ⟨hx, rfl⟩ := h0
      rw [hmsgRouteFun_zero hx, hmsgRouteFun_one (hmsgCall_hmsgPartner hx 1),
        hmsgPartner_hmsgPartner hx]
    · rw [hmsgRouteFun_of_not h1 h0, hmsgRouteFun_of_not h1 h0]

/-- **The `H_msg` regrouping permutation** of `HashDomain × Bool` (an involution): with
`Qrom.regroup`, the input `p ‖ BE_32(1)` is answered by the second component of the cell
`p ‖ BE_32(0)`, every other input by the first component of its own cell. -/
def hmsgRoute : Equiv.Perm (Qrom.HashDomain × Bool) :=
  Function.Involutive.toPerm hmsgRouteFun hmsgRouteFun_involutive

/-- Call 1 of `H_msg` goes to the second slot of the cell of call 0. -/
theorem hmsgRoute_messageDigestInput (randomizer : Randomizer) (publicSeed : PublicParameter)
    (root : Digest) (message : Message) {x₀ x₁ : Qrom.HashDomain}
    (h₀ : encodeInput (messageDigestInput randomizer publicSeed root message 0) = some x₀)
    (h₁ : encodeInput (messageDigestInput randomizer publicSeed root message 1) = some x₁) :
    hmsgRoute (x₁, false) = (x₀, true) := by
  have hx : hmsgCall x₁ = some 1 := by
    rw [hmsgCall_of_encodeInput_eq_some h₁, hmsgCallOf_messageDigestInput]
  show hmsgRouteFun (x₁, false) = (x₀, true)
  rw [hmsgRouteFun_one hx,
    hmsgPartner_of_encodeInput_eq_some h₁ (by rw [withCall_messageDigestInput]; exact h₀)]

/-- Every input but a call 1 of `H_msg` stays in the first slot of its own cell. -/
theorem hmsgRoute_of_ne {x : Qrom.HashDomain} (h : hmsgCall x ≠ some 1) :
    hmsgRoute (x, false) = (x, false) :=
  hmsgRouteFun_of_not (fun h1 ↦ h h1.1) (fun h0 ↦ absurd h0.2 (by decide))

end Quantum.Qrom.Sphincs

end
