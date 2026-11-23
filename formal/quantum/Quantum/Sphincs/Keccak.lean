module

public import Quantum.Xmss.Keccak
public import Statement.LeanSphincs

@[expose] public section

/-!
# leanSPHINCS's hash calls as sponge tails

leanSPHINCS hashes with the same Keccak-256 as leanXMSS, so `Quantum.Xmss.Keccak` gives the sponge
view (`keccakHash_eq_spongeHash`, `blocks`, `out256`); this file adds what is specific to
leanSPHINCS:

* `Slot`, `slotOf pk`: the hash call a Msponge tail belongs to. A one-block tail is first read by
  its padding (`PadShaped`): the 84-byte `H_msg` calls, the 93-byte `PRF_msg` and the 44-byte key
  expansion have lengths no addressed input has, so an `H_msg` input whose randomizer equals
  `PK.seed` never parses as an addressed input. Every other tail is read from its first block:
  `PK.seed`, then the address words (`slotOfWords`). The WOTS endpoint compression (8 blocks) and
  the FORS roots compression (4 blocks) are read the same way.
* `slotOf_addressedHashInput`, `slotOfAddress_hashDomainFields`,
  `slotOfAddress_keygenDomainFields`, `slotOf_messageDigestInput`, `slotOf_prfMessageInput`,
  `slotOf_keyDerivationInput` and one `slotOf_*` lemma per honest call; distinct in-range domains
  have distinct slots (`hashDomainFields_injOn`), and tails determine inputs
  (`absorbTail_blocks_addressedHashInput_injective`,
  `absorbTail_blocks_messageDigestInput_injective`, ...).
* The digest bits: call 0 of `H_msg` fixes the 240 FORS leaf bits (`leavesOf`) and the top 10
  index bits (`hiOf`), call 1 the low 16 index bits (`loOf`): `digestIndex_truncate`,
  `digestForsLeaves_truncate`. Fibers: `card_fiber_hiLeaves` (`2^6`), `card_fiber_loOf` (`2^240`),
  and over the rate, `card_fiber_out256` (`2^832`), `card_fiber_hiLeaves_out256` (`2^838`),
  `card_fiber_loOf_out256` (`2^1072`).
-/

open Finset Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput MasterSeed ChainStep
  chainLength digestBits littleEndianBytes truncateHash hasherInput digestsPayload)
open HashSig.OverPermutation (keccakHash nodePayload)
open Quantum.Xmss (X Z bitOf bitOf_injective bitOf_eq_one_iff bitOf_decide_eq_one ofBits
  getLsbD_ofBits inputBit blockOf blockOf_apply blocks blocks_injective firstBlock firstBlock_of_lt
  blockOf_firstBlock absorbTail_blocks inputBit_append_left inputBit_append_right
  inputBit_littleEndianBytes length_littleEndianBytes length_flatMap_littleEndianBytes rateSlice
  rateSlice_eq out256 bitsEquiv padBlock_getD)
open LeanVM.Protocol.KeccakHash (padBlock padFirst padLast)

namespace Quantum.Sphincs

/-! ## Bytes of a block -/

theorem length_bigEndianBytes (n : ℕ) (v : BitVec (8 * n)) : (bigEndianBytes n v).length = n :=
  List.length_ofFn

theorem inputBit_bigEndianBytes (n : ℕ) (v : BitVec (8 * n)) (j : ℕ) (hj : j < 8 * n) :
    inputBit (bigEndianBytes n v) j = bitOf (v.getLsbD (8 * (n - 1 - j / 8) + j % 8)) := by
  rw [inputBit, bigEndianBytes, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with h
  · simp [Nat.mod_lt j (show 8 > 0 by norm_num)]
  · omega

/-- Bytes `start` to `start + n - 1` of a block, read as one big-endian word. -/
def beSlice (x : X) (start n : ℕ) (h : start + n ≤ 136) : BitVec (8 * n) :=
  ofBits fun j : Fin (8 * n) ↦ x ⟨8 * (start + (n - 1 - j / 8)) + j % 8, by have := j.isLt; omega⟩

/-- The bits of bytes `b` of an input, when `a ++ b` starts it, are the first block's bits there. -/
theorem blockOf_firstBlock_of_prefix {input a b : List UInt8} (h : a ++ b <+: input) (j : ℕ)
    (hj : j < 8 * b.length) (hb : a.length + b.length ≤ 136) :
    blockOf (firstBlock input) ⟨8 * a.length + j, by omega⟩ = inputBit b j := by
  obtain ⟨c, rfl⟩ := h
  rw [blockOf_firstBlock _ _ (by simp only [List.length_append]; omega),
    inputBit_append_left _ _ _ (by simp only [List.length_append]; omega), inputBit_append_right]

theorem beSlice_firstBlock {input a : List UInt8} {start n : ℕ} {v : BitVec (8 * n)}
    (h : a ++ bigEndianBytes n v <+: input) (ha : a.length = start) (hn : start + n ≤ 136) :
    beSlice (blockOf (firstBlock input)) start n hn = v := by
  subst ha
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb := blockOf_firstBlock_of_prefix h (8 * (n - 1 - j / 8) + j % 8)
    (by rw [length_bigEndianBytes]; omega) (by rw [length_bigEndianBytes]; omega)
  rw [beSlice, getLsbD_ofBits _ j hj]
  simp only [show 8 * (a.length + (n - 1 - j / 8)) + j % 8 =
    8 * a.length + (8 * (n - 1 - j / 8) + j % 8) by omega, hb]
  rw [inputBit_bigEndianBytes _ _ _ (by omega),
    show 8 * (n - 1 - (8 * (n - 1 - j / 8) + j % 8) / 8) + (8 * (n - 1 - j / 8) + j % 8) % 8 = j
      by omega]
  simp

theorem rateSlice_firstBlock {input a : List UInt8} {s n : ℕ} {v : BitVec (8 * n)}
    (h : a ++ littleEndianBytes n v <+: input) (hs : 8 * a.length = s) (hn : s + 8 * n ≤ 1088) :
    rateSlice (blockOf (firstBlock input)) s (8 * n) hn = v := by
  subst hs
  apply rateSlice_eq
  intro j hj
  exact (blockOf_firstBlock_of_prefix h j (by rw [length_littleEndianBytes]; omega)
    (by rw [length_littleEndianBytes]; omega)).trans (inputBit_littleEndianBytes _ _ _)

/-! ## Padding -/

/-- A block's padding is that of an `L`-byte input: from bit `8 L` on, ones exactly at bits `8 L`
and `1087`. -/
def PadShaped (L : ℕ) (x : X) : Prop :=
  ∀ j : Fin 1088, 8 * L ≤ (j : ℕ) → x j = if (j : ℕ) = 8 * L ∨ (j : ℕ) = 1087 then 1 else 0

instance (L : ℕ) (x : X) : Decidable (PadShaped L x) := by
  unfold PadShaped
  infer_instance

private theorem pad_bit (L q r : ℕ) (hr : r < 8) :
    bitOf (((if L = q then padFirst else 0) ^^^ (if 135 = q then padLast else 0)).toBitVec.getLsbD
      r) = if 8 * q + r = 8 * L ∨ 8 * q + r = 1087 then 1 else 0 := by
  split_ifs with h1 h2 hc <;> interval_cases r <;> first | decide | omega

theorem padShaped_padBlock (input : HashInput) (h : input.length < 136) :
    PadShaped input.length (blockOf (padBlock input)) := by
  intro j hj
  rw [blockOf_apply, inputBit, padBlock_getD input h _ (by omega), ite_eq_right (by omega)]
  conv_rhs => rw [← Nat.div_add_mod (j : ℕ) 8]
  exact pad_bit _ _ _ (Nat.mod_lt _ (by norm_num))

/-- A block has at most one padding shape. -/
theorem padShaped_unique {L L' : ℕ} {x : X} (hL : L < 136) (hL' : L' < 136) (h : PadShaped L x)
    (h' : PadShaped L' x) : L = L' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have a := h ⟨8 * L', by omega⟩ (show 8 * L ≤ 8 * L' by omega)
    have b := h' ⟨8 * L', by omega⟩ le_rfl
    rw [ite_eq_right (by rw [Fin.val_mk]; omega)] at a
    rw [ite_eq_left (Or.inl rfl), a] at b
    exact absurd b (by decide)
  · have a := h' ⟨8 * L, by omega⟩ (show 8 * L' ≤ 8 * L by omega)
    have b := h ⟨8 * L, by omega⟩ le_rfl
    rw [ite_eq_right (by rw [Fin.val_mk]; omega)] at a
    rw [ite_eq_left (Or.inl rfl), a] at b
    exact absurd b (by decide)

theorem not_padShaped_padBlock (input : HashInput) (h : input.length < 136) {L : ℕ} (hL : L < 136)
    (hne : input.length ≠ L) : ¬PadShaped L (blockOf (padBlock input)) :=
  fun hs ↦ hne (padShaped_unique h hL (padShaped_padBlock input h) hs)

/-- An input shorter than a block has a one-block tail. -/
theorem absorbTail_blocks_of_lt (φ : Equiv.Perm (X × Z)) (input : HashInput)
    (h : input.length < 136) : absorbTail φ (blocks input) = [blockOf (padBlock input)] := by
  obtain ⟨rest, ht, hl⟩ := absorbTail_blocks φ input
  rw [ht, firstBlock_of_lt input h, List.eq_nil_of_length_eq_zero (by omega : rest.length = 0)]

/-! ## Slots -/

/-- The hash call a Msponge tail belongs to. -/
inductive Slot where
  /-- The step leaving position `step` of chain `chainIndex` of the one-time key
  `(layer, tree, leaf)`. -/
  | chain (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) (chainIndex : ChainIndex)
      (step : ChainStep)
  /-- The one-time key's leaf, the compression of its chain ends. -/
  | leaf (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
  /-- Node `nodeIndex` at height `height` of tree `tree` of layer `layer`. -/
  | node (layer : Layer) (tree : TreeIndex) (height nodeIndex : ℕ)
  /-- The WOTS+C encoding of the one-time key `(layer, tree, leaf)`. -/
  | enc (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
  /-- Leaf `forsLeaf` of FORS tree `forsTree` of instance `index`. -/
  | forsLeaf (index : Index) (forsTree : ForsTreeIndex) (forsLeaf : ForsLeafIndex)
  /-- Node `node` at height `height` (`1` to `a`) of FORS tree `forsTree` of instance `index`. -/
  | forsNode (index : Index) (forsTree : ForsTreeIndex) (height node : ℕ)
  /-- The FORS public key of instance `index`, the compression of its roots. -/
  | forsRoots (index : Index)
  /-- A secret: a WOTS chain start or a FORS leaf secret. -/
  | prf (domain : KeygenDomain)
  /-- Call `call` of `H_msg` at the randomizer `randomizer` and the message `message`. -/
  | hmsg (randomizer : Randomizer) (message : Message) (call : DigestCall)
  /-- `PRF_msg` of the message `message`. -/
  | prfMsg (message : Message)
  /-- The key expansion with the domain byte `domain`. -/
  | expand (domain : UInt8)
  deriving DecidableEq

/-- The FORS instance an address's tree and key-pair words name, `tree 2^8 + keyPair`. -/
def forsIndexOf (tree keyPair : ℕ) : Option Index :=
  if h : tree < 2 ^ 18 ∧ keyPair < 2 ^ 8 then
    some ⟨tree * 2 ^ 8 + keyPair, by show _ < 2 ^ 26; omega⟩
  else none

/-- The FORS slot of a `FORS_TREE` address of instance `index`: a leaf at height `0`, else a node;
the tree index is `κ 2^(a - height) + node`. -/
def forsTreeSlot (index : Index) (height treeIndex : ℕ) : Option Slot :=
  if h : height ≤ forsTreeHeight ∧ treeIndex / 2 ^ (forsTreeHeight - height) < forsTreeCount then
    some (if height = 0 then .forsLeaf index ⟨_, h.2⟩ (forsLeafOfNat treeIndex)
      else .forsNode index ⟨_, h.2⟩ height (treeIndex % 2 ^ (forsTreeHeight - height)))
  else none

/-- The slot an address's words name: layer, tree, type, key pair, chain or height, hash or tree
index. -/
def slotOfWords (layer tree type keyPair height index : ℕ) : Option Slot :=
  match type with
  | 0 => if h : layer < layerCount ∧ tree < 2 ^ indexBits ∧ keyPair < 2 ^ layerHeight topLayer ∧
        height < chainCount ∧ index < chainLength - 1 then
      some (.chain ⟨layer, h.1⟩ ⟨tree, h.2.1⟩ ⟨keyPair, h.2.2.1⟩ ⟨height, h.2.2.2.1⟩
        ⟨index, h.2.2.2.2⟩)
    else none
  | 1 => if h : layer < layerCount ∧ tree < 2 ^ indexBits ∧ keyPair < 2 ^ layerHeight topLayer then
      some (.leaf ⟨layer, h.1⟩ ⟨tree, h.2.1⟩ ⟨keyPair, h.2.2⟩)
    else none
  | 2 => if h : layer < layerCount ∧ tree < 2 ^ indexBits then
      some (.node ⟨layer, h.1⟩ ⟨tree, h.2⟩ height index)
    else none
  | 3 => (forsIndexOf tree keyPair).bind fun idx ↦ forsTreeSlot idx height index
  | 4 => (forsIndexOf tree keyPair).map .forsRoots
  | 5 => if h : layer < layerCount ∧ tree < 2 ^ indexBits ∧ keyPair < 2 ^ layerHeight topLayer ∧
        height < chainCount then
      some (.prf (.oneTimeChain ⟨layer, h.1⟩ ⟨tree, h.2.1⟩ ⟨keyPair, h.2.2.1⟩ ⟨height, h.2.2.2⟩))
    else none
  | 6 => (forsIndexOf tree keyPair).bind fun idx ↦
      if h : index / 2 ^ forsTreeHeight < forsTreeCount then
        some (.prf (.forsSecret idx ⟨_, h⟩ (forsLeafOfNat index)))
      else none
  | 7 => if h : layer < layerCount ∧ tree < 2 ^ indexBits ∧ keyPair < 2 ^ layerHeight topLayer then
      some (.enc ⟨layer, h.1⟩ ⟨tree, h.2.1⟩ ⟨keyPair, h.2.2⟩)
    else none
  | _ => none

/-- The slot an address names. -/
def slotOfAddress (a : Address) : Option Slot :=
  slotOfWords a.layer.toNat a.tree.toNat a.addressType.word a.keyPair.toNat
    a.chainOrTreeHeight.toNat a.hashOrTreeIndex.toNat

/-- The slot a first block names, for the key `pk`: its prefix must be `PK.seed` (bytes `0` to
`15`); then the address words (bytes `16` to `47`, the zero word at `20` to `23` unread). -/
def slotOfBlock (pk : PublicKey) (x : X) : Option Slot :=
  if rateSlice x 0 128 (Nat.le_of_ble_eq_true rfl) = pk.publicSeed then
    slotOfWords (beSlice x 16 4 (Nat.le_of_ble_eq_true rfl)).toNat
      (beSlice x 24 8 (Nat.le_of_ble_eq_true rfl)).toNat
      (beSlice x 32 4 (Nat.le_of_ble_eq_true rfl)).toNat
      (beSlice x 36 4 (Nat.le_of_ble_eq_true rfl)).toNat
      (beSlice x 40 4 (Nat.le_of_ble_eq_true rfl)).toNat
      (beSlice x 44 4 (Nat.le_of_ble_eq_true rfl)).toNat
  else none

/-- The digest call a counter word names. -/
def callOf (v : BitVec 32) : Option DigestCall :=
  if h : v.toNat < digestCallCount then some ⟨_, h⟩ else none

/-- The `H_msg` slot of an 84-byte block for the key `pk`: bytes `16` to `47` must be
`PK.seed ‖ PK.root`; the randomizer is bytes `0` to `15`, the message bytes `48` to `79`, the call
the big-endian counter at bytes `80` to `83`. -/
def hmsgSlot (pk : PublicKey) (x : X) : Option Slot :=
  if rateSlice x 128 128 (Nat.le_of_ble_eq_true rfl) = pk.publicSeed then
    if rateSlice x 256 digestBits (Nat.le_of_ble_eq_true rfl) = pk.root then
      (callOf (beSlice x 80 4 (Nat.le_of_ble_eq_true rfl))).map
        (.hmsg (rateSlice x 0 digestBits (Nat.le_of_ble_eq_true rfl))
          (rateSlice x 384 256 (Nat.le_of_ble_eq_true rfl)))
    else none
  else none

/-- The slot of a one-block tail: padded as an 84-byte input, an `H_msg` call (`hmsgSlot`); as a
93-byte input, `PRF_msg` (its message, bytes `61` to `92`); as a 44-byte input, the key expansion
(its domain byte `43`); else the slot its block names (`slotOfBlock`). -/
def slotOfOneBlock (pk : PublicKey) (x : X) : Option Slot :=
  if PadShaped 84 x then hmsgSlot pk x
  else if PadShaped 93 x then some (.prfMsg (rateSlice x 488 256 (Nat.le_of_ble_eq_true rfl)))
  else if PadShaped 44 x then
    some (.expand (UInt8.ofBitVec (rateSlice x 344 8 (Nat.le_of_ble_eq_true rfl))))
  else slotOfBlock pk x

/-- **The slot of a Msponge tail** for the key `pk`: a one-block tail by `slotOfOneBlock`, a longer
one by its first block. -/
def slotOf (pk : PublicKey) : List X → Option Slot
  | [] => none
  | [x] => slotOfOneBlock pk x
  | x :: _ :: _ => slotOfBlock pk x

theorem slotOf_singleton (pk : PublicKey) (x : X) : slotOf pk [x] = slotOfOneBlock pk x :=
  rfl

/-- A tail whose input has none of the three special lengths is read from its first block. -/
theorem slotOf_absorbTail (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (input : HashInput)
    (h84 : input.length ≠ 84) (h93 : input.length ≠ 93) (h44 : input.length ≠ 44) :
    slotOf pk (absorbTail φ (blocks input)) = slotOfBlock pk (blockOf (firstBlock input)) := by
  obtain ⟨rest, ht, hl⟩ := absorbTail_blocks φ input
  rw [ht]
  cases rest with
  | nil =>
    have h136 : input.length < 136 := by simp only [List.length_nil] at hl; omega
    rw [slotOf_singleton, firstBlock_of_lt input h136]
    unfold slotOfOneBlock
    rw [ite_eq_right (not_padShaped_padBlock input h136 (by norm_num) h84)]
    rw [ite_eq_right (not_padShaped_padBlock input h136 (by norm_num) h93)]
    rw [ite_eq_right (not_padShaped_padBlock input h136 (by norm_num) h44)]
  | cons y rest => rfl

/-! ### Addressed inputs -/

theorem length_toBytes (a : Address) : a.toBytes.length = 32 := by
  simp [Address.toBytes, length_bigEndianBytes]

theorem word_lt (t : AddressType) : t.word < 8 := by
  cases t <;> simp [AddressType.word]

theorem toNat_ofNat_of_lt {w n : ℕ} (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem slotOfBlock_addressedHashInput (pk : PublicKey) (Q : PublicParameter) (a : Address)
    (payload : HashInput) :
    slotOfBlock pk (blockOf (firstBlock (addressedHashInput Q a payload))) =
      if Q = pk.publicSeed then slotOfAddress a else none := by
  have e : addressedHashInput Q a payload = littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++
      bigEndianBytes 4 0 ++ bigEndianBytes 8 a.tree ++
      bigEndianBytes 4 (BitVec.ofNat 32 a.addressType.word) ++ bigEndianBytes 4 a.keyPair ++
      bigEndianBytes 4 a.chainOrTreeHeight ++ bigEndianBytes 4 a.hashOrTreeIndex ++ payload := by
    simp [addressedHashInput, hasherInput, Address.toBytes]
  have hQ : rateSlice (blockOf (firstBlock (addressedHashInput Q a payload))) 0 128 (by norm_num) =
      Q := rateSlice_firstBlock (a := []) (n := 16) (by rw [e]; simp) rfl (by norm_num)
  have hl : beSlice (blockOf (firstBlock (addressedHashInput Q a payload))) 16 4 (by norm_num) =
      a.layer := beSlice_firstBlock (a := littleEndianBytes 16 Q) (by rw [e]; simp)
        (length_littleEndianBytes _ _) (by norm_num)
  have ht : beSlice (blockOf (firstBlock (addressedHashInput Q a payload))) 24 8 (by norm_num) =
      a.tree := beSlice_firstBlock
        (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0)
        (by rw [e]; simp) (by simp [length_littleEndianBytes, length_bigEndianBytes]) (by norm_num)
  have hy : beSlice (blockOf (firstBlock (addressedHashInput Q a payload))) 32 4 (by norm_num) =
      BitVec.ofNat 32 a.addressType.word := beSlice_firstBlock
        (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0 ++
          bigEndianBytes 8 a.tree)
        (by rw [e]; simp) (by simp [length_littleEndianBytes, length_bigEndianBytes]) (by norm_num)
  have hk : beSlice (blockOf (firstBlock (addressedHashInput Q a payload))) 36 4 (by norm_num) =
      a.keyPair := beSlice_firstBlock
        (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0 ++
          bigEndianBytes 8 a.tree ++ bigEndianBytes 4 (BitVec.ofNat 32 a.addressType.word))
        (by rw [e]; simp) (by simp [length_littleEndianBytes, length_bigEndianBytes]) (by norm_num)
  have hc : beSlice (blockOf (firstBlock (addressedHashInput Q a payload))) 40 4 (by norm_num) =
      a.chainOrTreeHeight := beSlice_firstBlock
        (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0 ++
          bigEndianBytes 8 a.tree ++ bigEndianBytes 4 (BitVec.ofNat 32 a.addressType.word) ++
          bigEndianBytes 4 a.keyPair)
        (by rw [e]; simp) (by simp [length_littleEndianBytes, length_bigEndianBytes]) (by norm_num)
  have hh : beSlice (blockOf (firstBlock (addressedHashInput Q a payload))) 44 4 (by norm_num) =
      a.hashOrTreeIndex := beSlice_firstBlock
        (a := littleEndianBytes 16 Q ++ bigEndianBytes 4 a.layer ++ bigEndianBytes 4 0 ++
          bigEndianBytes 8 a.tree ++ bigEndianBytes 4 (BitVec.ofNat 32 a.addressType.word) ++
          bigEndianBytes 4 a.keyPair ++ bigEndianBytes 4 a.chainOrTreeHeight)
        (by rw [e]; simp) (by simp [length_littleEndianBytes, length_bigEndianBytes]) (by norm_num)
  rw [slotOfBlock, hQ, hl, ht, hy, hk, hc, hh,
    toNat_ofNat_of_lt (lt_of_lt_of_le (word_lt _) (by norm_num))]
  rfl

theorem length_addressedHashInput (Q : PublicParameter) (a : Address) (payload : HashInput) :
    (addressedHashInput Q a payload).length = 48 + payload.length := by
  simp [addressedHashInput, hasherInput, length_littleEndianBytes, length_toBytes]
  omega

/-- **The slot of an addressed input's tail** (a payload of neither 36 nor 45 bytes, so that the
input has none of the special lengths): the slot its address names, if its prefix is `PK.seed`. -/
theorem slotOf_addressedHashInput (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (Q : PublicParameter)
    (a : Address) (payload : HashInput) (h36 : payload.length ≠ 36) (h45 : payload.length ≠ 45) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput Q a payload))) =
      if Q = pk.publicSeed then slotOfAddress a else none := by
  have hl := length_addressedHashInput Q a payload
  rw [slotOf_absorbTail _ _ _ (by omega) (by omega) (by omega), slotOfBlock_addressedHashInput]

/-! ### The honest addresses -/

/-- The slot of a hash domain. -/
def domainSlot : HashDomain → Slot
  | .chain layer tree leaf chainIndex step => .chain layer tree leaf chainIndex step
  | .leaf layer tree leaf => .leaf layer tree leaf
  | .node layer tree height nodeIndex => .node layer tree height nodeIndex
  | .encoding layer tree leaf => .enc layer tree leaf
  | .forsLeaf index forsTree forsLeaf => .forsLeaf index forsTree forsLeaf
  | .forsNode index forsTree height node => .forsNode index forsTree height node
  | .forsRoots index => .forsRoots index

theorem domainSlot_injective : Function.Injective domainSlot := by
  intro d d' h
  cases d <;> cases d' <;> simp_all [domainSlot]

/-- The hash domains the scheme uses: a hypertree node's height and index fit in a word, a FORS
node has height `1` to `a` and index below `2^(a - height)`. -/
def DomainInRange : HashDomain → Prop
  | .node _ _ height nodeIndex => height < 2 ^ 32 ∧ nodeIndex < 2 ^ 32
  | .forsNode _ _ height node =>
      0 < height ∧ height ≤ forsTreeHeight ∧ node < 2 ^ (forsTreeHeight - height)
  | _ => True

theorem val_lt_two_pow {n : ℕ} (i : Fin n) {w : ℕ} (h : n ≤ 2 ^ w) : i.val < 2 ^ w :=
  lt_of_lt_of_le i.isLt h

theorem treeOfIndex_zero (index : Index) : (treeOfIndex 0 index).val = index.val / 2 ^ 8 := by
  simp [treeOfIndex, bitsBelowLayer, layerHeight]

theorem leafOfIndex_zero (index : Index) : (leafOfIndex 0 index).val = index.val % 2 ^ 8 := by
  simp [leafOfIndex, bitsBelowLayer, layerHeight]

theorem forsIndexOf_index (index : Index) :
    forsIndexOf (treeOfIndex 0 index).val (leafOfIndex 0 index).val = some index := by
  have hi : index.val < 2 ^ 26 := index.isLt
  rw [forsIndexOf, treeOfIndex_zero, leafOfIndex_zero, dite_eq_left ⟨by omega, by omega⟩]
  congr 1
  apply Fin.ext
  show index.val / 2 ^ 8 * 2 ^ 8 + index.val % 2 ^ 8 = index.val
  omega

theorem tree_lt (index : Index) : (treeOfIndex 0 index).val < 2 ^ 64 := by
  rw [treeOfIndex_zero]
  have hi : index.val < 2 ^ 26 := index.isLt
  omega

theorem leaf_lt (index : Index) : (leafOfIndex 0 index).val < 2 ^ 32 := by
  rw [leafOfIndex_zero]
  omega

/-- **The slot of each honest address.** -/
theorem slotOfAddress_hashDomainFields (d : HashDomain) (hd : DomainInRange d) :
    slotOfAddress (hashDomainFields d) = some (domainSlot d) := by
  have hl : ∀ l : Layer, l.val < 2 ^ 32 := fun l ↦ val_lt_two_pow l (by norm_num [layerCount])
  have ht : ∀ τ : TreeIndex, τ.val < 2 ^ 64 := fun τ ↦ val_lt_two_pow τ (by norm_num [indexBits])
  have he : ∀ e : TreeLeafIndex, e.val < 2 ^ 32 := fun e ↦
    val_lt_two_pow e (by norm_num [layerHeight, topLayer])
  cases d with
  | chain layer tree leaf chainIndex step =>
    have hc : chainIndex.val < 2 ^ 32 := val_lt_two_pow chainIndex (by norm_num [chainCount])
    have hs : step.val < 2 ^ 32 :=
      val_lt_two_pow step (by norm_num [chainLength, HashSig.winternitzBits])
    simp only [slotOfAddress, hashDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (hl layer), toNat_ofNat_of_lt (ht tree), toNat_ofNat_of_lt (he leaf),
      toNat_ofNat_of_lt hc, toNat_ofNat_of_lt hs, slotOfWords]
    rw [dite_eq_left ⟨layer.isLt, tree.isLt, leaf.isLt, chainIndex.isLt, step.isLt⟩]
    rfl
  | leaf layer tree leaf =>
    simp only [slotOfAddress, hashDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (hl layer), toNat_ofNat_of_lt (ht tree), toNat_ofNat_of_lt (he leaf),
      slotOfWords]
    rw [dite_eq_left ⟨layer.isLt, tree.isLt, leaf.isLt⟩]
    rfl
  | node layer tree height nodeIndex =>
    simp only [slotOfAddress, hashDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (hl layer), toNat_ofNat_of_lt (ht tree), toNat_ofNat_of_lt hd.1,
      toNat_ofNat_of_lt hd.2, slotOfWords]
    rw [dite_eq_left ⟨layer.isLt, tree.isLt⟩]
    rfl
  | encoding layer tree leaf =>
    simp only [slotOfAddress, hashDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (hl layer), toNat_ofNat_of_lt (ht tree), toNat_ofNat_of_lt (he leaf),
      slotOfWords]
    rw [dite_eq_left ⟨layer.isLt, tree.isLt, leaf.isLt⟩]
    rfl
  | forsLeaf index forsTree forsLeaf =>
    have hκ : forsTree.val < 24 := forsTree.isLt
    have hs : forsLeaf.val < 2 ^ 10 := forsLeaf.isLt
    have hti : forsTreeIndex forsTree 0 forsLeaf.val < 2 ^ 32 := by
      simp only [forsTreeIndex, forsTreeHeight]
      omega
    simp only [slotOfAddress, hashDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (tree_lt index), toNat_ofNat_of_lt (leaf_lt index),
      toNat_ofNat_of_lt hti, toNat_ofNat_of_lt (show 0 < 2 ^ 32 by norm_num), slotOfWords,
      forsIndexOf_index, Option.bind_some, forsTreeSlot]
    rw [dite_eq_left ⟨Nat.zero_le _,
        by simp only [forsTreeIndex, forsTreeHeight, forsTreeCount]; omega⟩,
      ite_eq_left trivial]
    congr 2
    · apply Fin.ext
      simp only [forsTreeIndex, forsTreeHeight]
      omega
    · apply Fin.ext
      simp only [forsLeafOfNat, forsTreeIndex, forsTreeHeight]
      omega
  | forsNode index forsTree height node =>
    obtain ⟨h0, h10, hn⟩ := hd
    have hκ : forsTree.val < 24 := forsTree.isLt
    have hP : 0 < 2 ^ (forsTreeHeight - height) := Nat.two_pow_pos _
    have hP' : 2 ^ (forsTreeHeight - height) ≤ 2 ^ 10 :=
      Nat.pow_le_pow_right (by norm_num) (by simp only [forsTreeHeight]; omega)
    have hti : forsTreeIndex forsTree height node < 2 ^ 32 := by
      simp only [forsTreeIndex]
      have : forsTree.val * 2 ^ (forsTreeHeight - height) ≤ 23 * 2 ^ 10 :=
        Nat.mul_le_mul (by omega) hP'
      omega
    have hz : height < 2 ^ 32 := by simp only [forsTreeHeight] at h10; omega
    have hdiv :
        forsTreeIndex forsTree height node / 2 ^ (forsTreeHeight - height) = forsTree.val := by
      rw [forsTreeIndex, Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt hn, Nat.add_zero]
    have hmod : forsTreeIndex forsTree height node % 2 ^ (forsTreeHeight - height) = node := by
      rw [forsTreeIndex, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hn]
    simp only [slotOfAddress, hashDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (tree_lt index), toNat_ofNat_of_lt (leaf_lt index),
      toNat_ofNat_of_lt hti, toNat_ofNat_of_lt hz, slotOfWords, forsIndexOf_index,
      Option.bind_some, forsTreeSlot]
    rw [dite_eq_left ⟨h10, by rw [hdiv]; exact forsTree.isLt⟩, ite_eq_right (by omega)]
    simp only [hdiv, hmod]
    rfl
  | forsRoots index =>
    simp only [slotOfAddress, hashDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (tree_lt index), toNat_ofNat_of_lt (leaf_lt index), slotOfWords,
      forsIndexOf_index, Option.map_some]
    rfl

/-- **The slot of each secret's address.** -/
theorem slotOfAddress_keygenDomainFields (d : KeygenDomain) :
    slotOfAddress (keygenDomainFields d) = some (.prf d) := by
  cases d with
  | oneTimeChain layer tree leaf chainIndex =>
    simp only [slotOfAddress, keygenDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (val_lt_two_pow layer (by norm_num [layerCount]) : layer.val < 2 ^ 32),
      toNat_ofNat_of_lt (val_lt_two_pow tree (by norm_num [indexBits]) : tree.val < 2 ^ 64),
      toNat_ofNat_of_lt (val_lt_two_pow leaf (by norm_num [layerHeight, topLayer]) :
        leaf.val < 2 ^ 32),
      toNat_ofNat_of_lt (val_lt_two_pow chainIndex (by norm_num [chainCount]) :
        chainIndex.val < 2 ^ 32), slotOfWords]
    rw [dite_eq_left ⟨layer.isLt, tree.isLt, leaf.isLt, chainIndex.isLt⟩]
  | forsSecret index forsTree forsLeaf =>
    have hκ : forsTree.val < 24 := forsTree.isLt
    have hs : forsLeaf.val < 2 ^ 10 := forsLeaf.isLt
    have hti : forsTreeIndex forsTree 0 forsLeaf.val < 2 ^ 32 := by
      simp only [forsTreeIndex, forsTreeHeight]
      omega
    simp only [slotOfAddress, keygenDomainFields, makeAddress, AddressType.word,
      toNat_ofNat_of_lt (tree_lt index), toNat_ofNat_of_lt (leaf_lt index),
      toNat_ofNat_of_lt hti, slotOfWords, forsIndexOf_index, Option.bind_some]
    rw [dite_eq_left (by simp only [forsTreeIndex, forsTreeHeight, forsTreeCount]; omega)]
    congr 3
    · apply Fin.ext
      simp only [forsTreeIndex, forsTreeHeight]
      omega
    · apply Fin.ext
      simp only [forsLeafOfNat, forsTreeIndex, forsTreeHeight]
      omega

/-- Distinct in-range hash domains have distinct addresses: one honest input per slot. -/
theorem hashDomainFields_injOn {d d' : HashDomain} (hd : DomainInRange d) (hd' : DomainInRange d')
    (h : hashDomainFields d = hashDomainFields d') : d = d' := by
  have := slotOfAddress_hashDomainFields d hd
  rw [h, slotOfAddress_hashDomainFields d' hd'] at this
  exact domainSlot_injective (Option.some_injective _ this).symm

theorem keygenDomainFields_injective : Function.Injective keygenDomainFields := by
  intro d d' h
  have := slotOfAddress_keygenDomainFields d
  rw [h, slotOfAddress_keygenDomainFields d'] at this
  exact (Slot.prf.inj (Option.some_injective _ this)).symm

theorem hashDomainFields_ne_keygenDomainFields {d : HashDomain} (hd : DomainInRange d)
    (k : KeygenDomain) : hashDomainFields d ≠ keygenDomainFields k := by
  intro h
  have := slotOfAddress_hashDomainFields d hd
  rw [h, slotOfAddress_keygenDomainFields k] at this
  cases d <;> simp [domainSlot] at this

/-! ### The slot of each honest call -/

/-- A tweakable hash at an in-range domain (`th`, payload of neither 36 nor 45 bytes). -/
theorem slotOf_tweakable (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (d : HashDomain)
    (hd : DomainInRange d) (payload : HashInput) (h36 : payload.length ≠ 36)
    (h45 : payload.length ≠ 45) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed (hashDomainFields d)
      payload))) = some (domainSlot d) := by
  rw [slotOf_addressedHashInput _ _ _ _ _ h36 h45, ite_eq_left rfl,
    slotOfAddress_hashDomainFields d hd]

theorem slotOf_chain (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) (step : ChainStep) (value : Digest) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed
      (hashDomainFields (.chain layer tree leaf chainIndex step)) (littleEndianBytes 16 value)))) =
      some (.chain layer tree leaf chainIndex step) :=
  slotOf_tweakable φ pk (.chain layer tree leaf chainIndex step) True.intro _
    (by simp [littleEndianBytes]) (by simp [littleEndianBytes])

theorem length_digestsPayload {n : ℕ} (digests : Fin n → Digest) :
    (digestsPayload digests).length = 16 * n :=
  (length_flatMap_littleEndianBytes (List.ofFn digests)).trans
    (congrArg (16 * ·) (List.length_ofFn (f := digests)))

/-- The WOTS endpoint compression, 1072 bytes (8 blocks): read from its first block. -/
theorem slotOf_leaf (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (endpoints : ChainIndex → Digest) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed
      (hashDomainFields (.leaf layer tree leaf)) (digestsPayload endpoints)))) =
      some (.leaf layer tree leaf) :=
  slotOf_tweakable φ pk (.leaf layer tree leaf) True.intro _
    (by rw [length_digestsPayload]; decide) (by rw [length_digestsPayload]; decide)

theorem slotOf_node (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (layer : Layer) (tree : TreeIndex)
    (height nodeIndex : ℕ) (hheight : height < 2 ^ 32) (hindex : nodeIndex < 2 ^ 32)
    (left right : Digest) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed
      (hashDomainFields (.node layer tree height nodeIndex)) (nodePayload left right)))) =
      some (.node layer tree height nodeIndex) :=
  slotOf_tweakable φ pk (.node layer tree height nodeIndex) (And.intro hheight hindex) _
    (by simp [nodePayload, littleEndianBytes]) (by simp [nodePayload, littleEndianBytes])

/-- A WOTS+C encoding trial `M ‖ BE_32(c)`, 68 bytes. -/
theorem slotOf_encoding (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (layer : Layer)
    (tree : TreeIndex) (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed
      (hashDomainFields (.encoding layer tree leaf))
      (littleEndianBytes 16 message ++ bigEndianBytes 4 counter)))) =
      some (.enc layer tree leaf) :=
  slotOf_tweakable φ pk (.encoding layer tree leaf) True.intro _
    (by simp [littleEndianBytes, bigEndianBytes]) (by simp [littleEndianBytes, bigEndianBytes])

theorem slotOf_forsLeaf (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (index : Index)
    (forsTree : ForsTreeIndex) (forsLeaf : ForsLeafIndex) (secret : Digest) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed
      (hashDomainFields (.forsLeaf index forsTree forsLeaf)) (littleEndianBytes 16 secret)))) =
      some (.forsLeaf index forsTree forsLeaf) :=
  slotOf_tweakable φ pk (.forsLeaf index forsTree forsLeaf) True.intro _
    (by simp [littleEndianBytes]) (by simp [littleEndianBytes])

theorem slotOf_forsNode (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (index : Index)
    (forsTree : ForsTreeIndex) (height node : ℕ) (h0 : 0 < height)
    (hheight : height ≤ forsTreeHeight) (hnode : node < 2 ^ (forsTreeHeight - height))
    (left right : Digest) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed
      (hashDomainFields (.forsNode index forsTree height node)) (nodePayload left right)))) =
      some (.forsNode index forsTree height node) :=
  slotOf_tweakable φ pk (.forsNode index forsTree height node)
    (And.intro h0 (And.intro hheight hnode)) _
    (by simp [nodePayload, littleEndianBytes]) (by simp [nodePayload, littleEndianBytes])

/-- The FORS roots compression, 432 bytes (4 blocks): read from its first block. -/
theorem slotOf_forsRoots (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (index : Index)
    (roots : ForsTreeIndex → Digest) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed
      (hashDomainFields (.forsRoots index)) (digestsPayload roots)))) =
      some (.forsRoots index) :=
  slotOf_tweakable φ pk (.forsRoots index) True.intro _
    (by rw [length_digestsPayload]; decide) (by rw [length_digestsPayload]; decide)

/-- A secret, `PRF(PK.seed, SK.seed, ADRS)`. -/
theorem slotOf_prf (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (d : KeygenDomain)
    (secretSeed : MasterSeed) :
    slotOf pk (absorbTail φ (blocks (addressedHashInput pk.publicSeed (keygenDomainFields d)
      (littleEndianBytes 32 secretSeed)))) = some (.prf d) := by
  rw [slotOf_addressedHashInput _ _ _ _ _ (by simp [littleEndianBytes])
    (by simp [littleEndianBytes]), ite_eq_left rfl, slotOfAddress_keygenDomainFields]

/-! ### `H_msg`, `PRF_msg` and the key expansion -/

/-- The input of `H_msg` call `call`: `R ‖ PK.seed ‖ PK.root ‖ M ‖ BE_32(call)`, 84 bytes. -/
def messageDigestInput (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest)
    (message : Message) (call : DigestCall) : HashInput :=
  littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++ littleEndianBytes 16 root ++
    littleEndianBytes 32 message ++ bigEndianBytes 4 (BitVec.ofNat 32 call.val)

theorem messageDigestCall_eq {m : Type → Type} [Monad m]
    (π : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (randomizer : Randomizer)
    (publicSeed : PublicParameter) (root : Digest) (message : Message) (call : DigestCall) :
    Verification.messageDigestCall π randomizer publicSeed root message call =
      keccakHash π (messageDigestInput randomizer publicSeed root message call) :=
  rfl

theorem length_messageDigestInput (randomizer : Randomizer) (publicSeed : PublicParameter)
    (root : Digest) (message : Message) (call : DigestCall) :
    (messageDigestInput randomizer publicSeed root message call).length = 84 := by
  simp [messageDigestInput, littleEndianBytes, bigEndianBytes]

theorem callOf_ofNat (call : DigestCall) : callOf (BitVec.ofNat 32 call.val) = some call := by
  have hc : call.val < 2 ^ 32 := val_lt_two_pow call (by norm_num [digestCallCount])
  rw [callOf, dite_eq_left (by rw [toNat_ofNat_of_lt hc]; exact call.isLt)]
  congr 1
  exact Fin.ext (toNat_ofNat_of_lt hc)

/-- **The slot of an `H_msg` call**: `hmsg R M i` when the call is under the key `pk`, whatever the
randomizer, including `R = PK.seed`. -/
theorem slotOf_messageDigestInput (φ : Equiv.Perm (X × Z)) (pk : PublicKey)
    (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest) (message : Message)
    (call : DigestCall) :
    slotOf pk (absorbTail φ (blocks (messageDigestInput randomizer publicSeed root message call))) =
      if publicSeed = pk.publicSeed ∧ root = pk.root then some (.hmsg randomizer message call)
      else none := by
  have hlen := length_messageDigestInput randomizer publicSeed root message call
  obtain ⟨input, hinput⟩ :
      ∃ input, messageDigestInput randomizer publicSeed root message call = input := ⟨_, rfl⟩
  rw [hinput] at hlen ⊢
  have h136 : input.length < 136 := by omega
  have hshape : PadShaped 84 (blockOf (padBlock input)) := by
    have := padShaped_padBlock input h136
    rwa [hlen] at this
  rw [absorbTail_blocks_of_lt φ _ h136, slotOf_singleton]
  unfold slotOfOneBlock
  rw [ite_eq_left hshape]
  unfold hmsgSlot
  rw [← firstBlock_of_lt _ h136]
  have hR : rateSlice (blockOf (firstBlock input)) 0 digestBits (Nat.le_of_ble_eq_true rfl) =
      randomizer :=
    rateSlice_firstBlock (a := []) (n := 16)
      (by rw [← hinput, messageDigestInput]; simp [List.append_assoc]) rfl (by norm_num)
  have hQ : rateSlice (blockOf (firstBlock input)) 128 128 (Nat.le_of_ble_eq_true rfl) =
      publicSeed :=
    rateSlice_firstBlock (a := littleEndianBytes 16 randomizer) (n := 16)
      (by rw [← hinput, messageDigestInput]; simp [List.append_assoc])
      (by simp [littleEndianBytes]) (by norm_num)
  have hr : rateSlice (blockOf (firstBlock input)) 256 digestBits (Nat.le_of_ble_eq_true rfl) =
      root :=
    rateSlice_firstBlock (a := littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed)
      (n := 16) (by rw [← hinput, messageDigestInput]; simp [List.append_assoc])
      (by simp [littleEndianBytes]) (by norm_num)
  have hM : rateSlice (blockOf (firstBlock input)) 384 256 (Nat.le_of_ble_eq_true rfl) =
      message :=
    rateSlice_firstBlock (a := littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++
      littleEndianBytes 16 root) (n := 32)
      (by rw [← hinput, messageDigestInput]; simp [List.append_assoc])
      (by simp [littleEndianBytes]) (by norm_num)
  have hc : beSlice (blockOf (firstBlock input)) 80 4 (Nat.le_of_ble_eq_true rfl) =
      BitVec.ofNat 32 call.val :=
    beSlice_firstBlock (a := littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++
      littleEndianBytes 16 root ++ littleEndianBytes 32 message)
      (by rw [← hinput, messageDigestInput])
      (by simp [littleEndianBytes]) (by norm_num)
  rw [hR, hQ, hr, hM, hc, callOf_ofNat, Option.map_some]
  by_cases h1 : publicSeed = pk.publicSeed <;> by_cases h2 : root = pk.root <;> simp [h1, h2]

/-- **An `H_msg` call under the key is an `hmsg` slot**, for every randomizer: in particular one
equal to `PK.seed` does not parse as an addressed input. -/
theorem slotOf_messageDigestInput_self (φ : Equiv.Perm (X × Z)) (pk : PublicKey)
    (randomizer : Randomizer) (message : Message) (call : DigestCall) :
    slotOf pk (absorbTail φ (blocks (messageDigestInput randomizer pk.publicSeed pk.root message
      call))) = some (.hmsg randomizer message call) := by
  rw [slotOf_messageDigestInput, ite_eq_left ⟨rfl, rfl⟩]

/-- The input of `PRF_msg`: `SK.prf ‖ opt_rand ‖ M'`, 93 bytes. -/
def prfMessageInput (secretPrfKey : HashOutput) (optionalRandomness : Digest) (message : Message) :
    HashInput :=
  littleEndianBytes 32 secretPrfKey ++ littleEndianBytes 16 optionalRandomness ++
    framedMessage message

theorem prfMessage_eq {m : Type → Type} [Monad m]
    (π : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (secretPrfKey : HashOutput)
    (optionalRandomness : Digest) (message : Message) :
    KeyGenerationAndSigning.prfMessage π secretPrfKey optionalRandomness message =
      keccakHash π (prfMessageInput secretPrfKey optionalRandomness message) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

theorem length_prfMessageInput (secretPrfKey : HashOutput) (optionalRandomness : Digest)
    (message : Message) :
    (prfMessageInput secretPrfKey optionalRandomness message).length = 93 := by
  simp [prfMessageInput, framedMessage, contextString, seedTag, littleEndianBytes]

/-- `PRF_msg` has the slot `prfMsg M`. -/
theorem slotOf_prfMessageInput (φ : Equiv.Perm (X × Z)) (pk : PublicKey) (secretPrfKey : HashOutput)
    (optionalRandomness : Digest) (message : Message) :
    slotOf pk (absorbTail φ (blocks (prfMessageInput secretPrfKey optionalRandomness message))) =
      some (.prfMsg message) := by
  have hlen := length_prfMessageInput secretPrfKey optionalRandomness message
  obtain ⟨input, hinput⟩ :
      ∃ input, prfMessageInput secretPrfKey optionalRandomness message = input := ⟨_, rfl⟩
  rw [hinput] at hlen ⊢
  have h136 : input.length < 136 := by omega
  have h84 : ¬PadShaped 84 (blockOf (padBlock input)) :=
    not_padShaped_padBlock _ h136 (by norm_num) (by omega)
  have hshape : PadShaped 93 (blockOf (padBlock input)) := by
    have := padShaped_padBlock input h136
    rwa [hlen] at this
  rw [absorbTail_blocks_of_lt φ _ h136, slotOf_singleton]
  unfold slotOfOneBlock
  rw [ite_eq_right h84, ite_eq_left hshape, ← firstBlock_of_lt _ h136]
  have hM : rateSlice (blockOf (firstBlock input)) 488 256 (by norm_num) = message :=
    rateSlice_firstBlock (a := littleEndianBytes 32 secretPrfKey ++
      littleEndianBytes 16 optionalRandomness ++ [0x00, UInt8.ofNat contextString.length] ++
      contextString) (n := 32) (by rw [← hinput, prfMessageInput, framedMessage]; simp)
      (by simp [contextString, seedTag, littleEndianBytes]) (by norm_num)
  rw [hM]

theorem length_keyDerivationInput (secretSeed : MasterSeed) (domain : UInt8) :
    (KeyGenerationAndSigning.keyDerivationInput secretSeed domain).length = 44 := by
  simp [KeyGenerationAndSigning.keyDerivationInput, seedTag, littleEndianBytes]

/-- The key expansion `H(leanSPHINCS ‖ SK.seed ‖ domain)` has the slot `expand domain`. -/
theorem slotOf_keyDerivationInput (φ : Equiv.Perm (X × Z)) (pk : PublicKey)
    (secretSeed : MasterSeed) (domain : UInt8) :
    slotOf pk (absorbTail φ (blocks (KeyGenerationAndSigning.keyDerivationInput secretSeed
      domain))) = some (.expand domain) := by
  have hlen := length_keyDerivationInput secretSeed domain
  obtain ⟨input, hinput⟩ :
      ∃ input, KeyGenerationAndSigning.keyDerivationInput secretSeed domain = input := ⟨_, rfl⟩
  rw [hinput] at hlen ⊢
  have h136 : input.length < 136 := by omega
  have h84 : ¬PadShaped 84 (blockOf (padBlock input)) :=
    not_padShaped_padBlock _ h136 (by norm_num) (by omega)
  have h93 : ¬PadShaped 93 (blockOf (padBlock input)) :=
    not_padShaped_padBlock _ h136 (by norm_num) (by omega)
  have hshape : PadShaped 44 (blockOf (padBlock input)) := by
    have := padShaped_padBlock input h136
    rwa [hlen] at this
  rw [absorbTail_blocks_of_lt φ _ h136, slotOf_singleton]
  unfold slotOfOneBlock
  rw [ite_eq_right h84, ite_eq_right h93, ite_eq_left hshape, ← firstBlock_of_lt _ h136]
  have hpre : (seedTag ++ littleEndianBytes 32 secretSeed).length = 43 := by
    simp [seedTag, littleEndianBytes]
  have hd : rateSlice (blockOf (firstBlock input)) 344 8 (by norm_num) = domain.toBitVec := by
    apply rateSlice_eq
    intro j hj
    have hb := blockOf_firstBlock_of_prefix (a := seedTag ++ littleEndianBytes 32 secretSeed)
      (b := [domain]) (input := input)
      (by rw [← hinput, KeyGenerationAndSigning.keyDerivationInput])
      j (by simp only [List.length_singleton]; omega)
      (by rw [hpre]; simp only [List.length_singleton]; omega)
    rw [show (⟨344 + j, by omega⟩ : Fin 1088) =
        ⟨8 * (seedTag ++ littleEndianBytes 32 secretSeed).length + j, by rw [hpre]; omega⟩ from
        Fin.ext (by simp only [hpre]), hb, inputBit, Nat.div_eq_of_lt hj,
      Nat.mod_eq_of_lt hj]
    rfl
  rw [hd]

/-! ## Tails determine inputs -/

theorem littleEndianBytes_injective (n : ℕ) : Function.Injective (littleEndianBytes n) := by
  intro v w h
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  have := congrArg (inputBit · j) h
  simp only [inputBit_littleEndianBytes] at this
  exact bitOf_injective this

theorem bigEndianBytes_injective (n : ℕ) : Function.Injective (bigEndianBytes n) := by
  intro v w h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (inputBit · (8 * (n - 1 - j / 8) + j % 8)) h
  rw [inputBit_bigEndianBytes _ _ _ (by omega), inputBit_bigEndianBytes _ _ _ (by omega),
    show 8 * (n - 1 - (8 * (n - 1 - j / 8) + j % 8) / 8) + (8 * (n - 1 - j / 8) + j % 8) % 8 = j
      by omega] at this
  exact bitOf_injective this

theorem word_injective : Function.Injective AddressType.word := by
  intro a b h
  cases a <;> cases b <;> first | rfl | simp [AddressType.word] at h

theorem toBytes_injective : Function.Injective Address.toBytes := by
  intro a b h
  simp only [Address.toBytes] at h
  obtain ⟨h, h6⟩ := List.append_inj h (by simp [length_bigEndianBytes])
  obtain ⟨h, h5⟩ := List.append_inj h (by simp [length_bigEndianBytes])
  obtain ⟨h, h4⟩ := List.append_inj h (by simp [length_bigEndianBytes])
  obtain ⟨h, h3⟩ := List.append_inj h (by simp [length_bigEndianBytes])
  obtain ⟨h, h2⟩ := List.append_inj h (by simp [length_bigEndianBytes])
  obtain ⟨h1, -⟩ := List.append_inj h (by simp [length_bigEndianBytes])
  have hw := congrArg BitVec.toNat (bigEndianBytes_injective 4 h3)
  rw [toNat_ofNat_of_lt (lt_of_lt_of_le (word_lt _) (by norm_num)),
    toNat_ofNat_of_lt (lt_of_lt_of_le (word_lt _) (by norm_num))] at hw
  cases a
  cases b
  simp only [Address.mk.injEq]
  exact ⟨bigEndianBytes_injective 4 h1, bigEndianBytes_injective 8 h2, word_injective hw,
    bigEndianBytes_injective 4 h4, bigEndianBytes_injective 4 h5, bigEndianBytes_injective 4 h6⟩

/-- The prefix fixed, an addressed input determines its address and payload. -/
theorem addressedHashInput_injective (Q : PublicParameter) {a a' : Address} {p p' : HashInput}
    (h : addressedHashInput Q a p = addressedHashInput Q a' p') : a = a' ∧ p = p' := by
  unfold addressedHashInput hasherInput at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [length_littleEndianBytes, length_toBytes])
  exact ⟨toBytes_injective (List.append_cancel_left h1), h2⟩

/-- **Tails determine addressed inputs**: the prefix fixed, the same Msponge tail means the same
address and payload. -/
theorem absorbTail_blocks_addressedHashInput_injective (φ : Equiv.Perm (X × Z))
    (Q : PublicParameter) {a a' : Address} {p p' : HashInput}
    (h : absorbTail φ (blocks (addressedHashInput Q a p)) =
      absorbTail φ (blocks (addressedHashInput Q a' p'))) : a = a' ∧ p = p' :=
  addressedHashInput_injective Q (blocks_injective (absorbTail_injective φ h))

theorem messageDigestInput_injective {R R' : Randomizer} {Q Q' : PublicParameter} {r r' : Digest}
    {M M' : Message} {i i' : DigestCall}
    (h : messageDigestInput R Q r M i = messageDigestInput R' Q' r' M' i') :
    R = R' ∧ Q = Q' ∧ r = r' ∧ M = M' ∧ i = i' := by
  unfold messageDigestInput at h
  obtain ⟨h, h5⟩ := List.append_inj h (by simp [littleEndianBytes])
  obtain ⟨h, h4⟩ := List.append_inj h (by simp [littleEndianBytes])
  obtain ⟨h, h3⟩ := List.append_inj h (by simp [littleEndianBytes])
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [littleEndianBytes])
  have hi := congrArg BitVec.toNat (bigEndianBytes_injective 4 h5)
  rw [toNat_ofNat_of_lt (val_lt_two_pow i (by norm_num [digestCallCount])),
    toNat_ofNat_of_lt (val_lt_two_pow i' (by norm_num [digestCallCount]))] at hi
  exact ⟨littleEndianBytes_injective 16 h1, littleEndianBytes_injective 16 h2,
    littleEndianBytes_injective 16 h3, littleEndianBytes_injective 32 h4, Fin.ext hi⟩

/-- **Tails determine `H_msg` inputs.** -/
theorem absorbTail_blocks_messageDigestInput_injective (φ : Equiv.Perm (X × Z))
    {R R' : Randomizer} {Q Q' : PublicParameter} {r r' : Digest} {M M' : Message}
    {i i' : DigestCall}
    (h : absorbTail φ (blocks (messageDigestInput R Q r M i)) =
      absorbTail φ (blocks (messageDigestInput R' Q' r' M' i'))) :
    R = R' ∧ Q = Q' ∧ r = r' ∧ M = M' ∧ i = i' :=
  messageDigestInput_injective (blocks_injective (absorbTail_injective φ h))

theorem prfMessageInput_injective {k k' : HashOutput} {o o' : Digest} {M M' : Message}
    (h : prfMessageInput k o M = prfMessageInput k' o' M') : k = k' ∧ o = o' ∧ M = M' := by
  unfold prfMessageInput framedMessage at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp [littleEndianBytes])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [littleEndianBytes])
  obtain ⟨-, h3⟩ := List.append_inj h3 rfl
  exact ⟨littleEndianBytes_injective 32 h1, littleEndianBytes_injective 16 h2,
    littleEndianBytes_injective 32 h3⟩

/-- **Tails determine `PRF_msg` inputs.** -/
theorem absorbTail_blocks_prfMessageInput_injective (φ : Equiv.Perm (X × Z)) {k k' : HashOutput}
    {o o' : Digest} {M M' : Message}
    (h : absorbTail φ (blocks (prfMessageInput k o M)) =
      absorbTail φ (blocks (prfMessageInput k' o' M'))) : k = k' ∧ o = o' ∧ M = M' :=
  prfMessageInput_injective (blocks_injective (absorbTail_injective φ h))

theorem keyDerivationInput_injective {s s' : MasterSeed} {d d' : UInt8}
    (h : KeyGenerationAndSigning.keyDerivationInput s d =
      KeyGenerationAndSigning.keyDerivationInput s' d') : s = s' ∧ d = d' := by
  unfold KeyGenerationAndSigning.keyDerivationInput at h
  obtain ⟨h, h2⟩ := List.append_inj h (by simp [length_littleEndianBytes])
  exact ⟨littleEndianBytes_injective 32 (List.append_cancel_left h), List.singleton_inj.mp h2⟩

/-- **Tails determine key-expansion inputs.** -/
theorem absorbTail_blocks_keyDerivationInput_injective (φ : Equiv.Perm (X × Z))
    {s s' : MasterSeed} {d d' : UInt8}
    (h : absorbTail φ (blocks (KeyGenerationAndSigning.keyDerivationInput s d)) =
      absorbTail φ (blocks (KeyGenerationAndSigning.keyDerivationInput s' d'))) :
    s = s' ∧ d = d' :=
  keyDerivationInput_injective (blocks_injective (absorbTail_injective φ h))

/-! ## The digest bits -/

/-- Byte `k` of a hash output (little-endian, byte `0` lowest). -/
def outputByte (y : HashOutput) (k : ℕ) : ℕ := y.toNat / 2 ^ (8 * k) % 2 ^ 8

theorem outputByte_lt (y : HashOutput) (k : ℕ) : outputByte y k < 256 :=
  Nat.mod_lt _ (by norm_num)

/-- The top 10 index bits, from call 0: the low 2 bits of byte 30, then byte 31. -/
def hiOf (y : HashOutput) : Fin (2 ^ 10) :=
  ⟨outputByte y 30 % 4 * 2 ^ 8 + outputByte y 31, by
    have := outputByte_lt y 31
    show _ < 1024
    omega⟩

/-- The low 16 index bits, from call 1: byte 0 (the low tree-index byte), then byte 1 (the bottom
leaf). -/
def loOf (y : HashOutput) : Fin (2 ^ 16) :=
  ⟨outputByte y 0 * 2 ^ 8 + outputByte y 1, by
    have := outputByte_lt y 0
    have := outputByte_lt y 1
    show _ < 65536
    omega⟩

/-- The FORS leaves, from call 0's first 30 bytes. -/
def leavesOf (y : HashOutput) : ForsTreeIndex → ForsLeafIndex :=
  digestForsLeaves (BitVec.ofNat (8 * digestByteCount) y.toNat)

/-- The index of the top bits `hi` and the low bits `lo`. -/
def joinIndex (hi : Fin (2 ^ 10)) (lo : Fin (2 ^ 16)) : Index :=
  ⟨hi.val * 2 ^ 16 + lo.val, by
    have h1 : hi.val < 1024 := hi.isLt
    have h2 : lo.val < 65536 := lo.isLt
    show _ < 67108864
    omega⟩

theorem messageDigestByte_eq (D : MessageDigest) (k : ℕ) :
    messageDigestByte D k = D.toNat / 2 ^ (8 * k) % 2 ^ 8 := by
  simp [messageDigestByte, Nat.shiftRight_eq_div_pow]

theorem messageDigestBit_eq (D : MessageDigest) (p : ℕ) :
    messageDigestBit D p = (D.toNat.testBit (7 - p % 8 + 8 * (p / 8))).toNat := by
  rw [messageDigestBit, messageDigestByte_eq, ← Nat.toNat_testBit, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, decide_eq_true (by omega : 7 - p % 8 < 8), Bool.true_and]

theorem messageDigestByte_lt (D : MessageDigest) (k : ℕ) : messageDigestByte D k < 256 := by
  rw [messageDigestByte_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem digestValue_eq (d : DigestCall → HashOutput) :
    digestValue d = 2 ^ 256 * (d 1).toNat + (d 0).toNat := by
  unfold digestValue
  change ∑ call : Fin 2, (d call).toNat * 2 ^ (256 * call.val) = _
  rw [Fin.sum_univ_two]
  show (d 0).toNat * 2 ^ (256 * 0) + (d 1).toNat * 2 ^ (256 * 1) = _
  ring

theorem toNat_truncateMessageDigest (d : DigestCall → HashOutput) :
    (truncateMessageDigest d).toNat =
      (2 ^ 256 * (d 1).toNat + (d 0).toNat) % 2 ^ (8 * digestByteCount) := by
  rw [truncateMessageDigest, BitVec.toNat_ofNat, digestValue_eq]

theorem lt_digestBitCount {i : ℕ} (hi : i < 272) : i < 8 * digestByteCount := by
  simp only [digestByteCount]
  omega

theorem testBit_truncate_lo (d : DigestCall → HashOutput) (i : ℕ) (hi : i < 256) :
    (truncateMessageDigest d).toNat.testBit i = (d 0).toNat.testBit i := by
  rw [toNat_truncateMessageDigest, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_mul_add _ (d 0).isLt, ite_eq_left hi,
    decide_eq_true (lt_digestBitCount (by omega)), Bool.true_and]

theorem testBit_truncate_hi (d : DigestCall → HashOutput) (i : ℕ) (hi : i < 16) :
    (truncateMessageDigest d).toNat.testBit (i + 256) = (d 1).toNat.testBit i := by
  rw [toNat_truncateMessageDigest, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_mul_add _ (d 0).isLt, ite_eq_right (by omega),
    decide_eq_true (lt_digestBitCount (by omega)), Bool.true_and, Nat.add_sub_cancel]

theorem div_mod_congr {x y s s' m : ℕ} (h : ∀ j < m, x.testBit (j + s) = y.testBit (j + s')) :
    x / 2 ^ s % 2 ^ m = y / 2 ^ s' % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hj : j < m
  · rw [h j hj]
  · simp [hj]

theorem messageDigestByte_truncate_lo (d : DigestCall → HashOutput) (k : ℕ) (hk : k < 32) :
    messageDigestByte (truncateMessageDigest d) k = outputByte (d 0) k := by
  rw [messageDigestByte_eq, outputByte]
  exact div_mod_congr fun j hj ↦ testBit_truncate_lo d _ (by omega)

theorem messageDigestByte_truncate_hi (d : DigestCall → HashOutput) (k : ℕ) (hk : 32 ≤ k)
    (hk' : k < 34) : messageDigestByte (truncateMessageDigest d) k = outputByte (d 1) (k - 32) := by
  rw [messageDigestByte_eq, outputByte]
  refine div_mod_congr fun j hj ↦ ?_
  rw [show j + 8 * k = (j + 8 * (k - 32)) + 256 by omega]
  exact testBit_truncate_hi d _ (by omega)

theorem digestIndex_val (D : MessageDigest) :
    (digestIndex D).val = (65536 * messageDigestByte D 30 + 256 * messageDigestByte D 31 +
      messageDigestByte D 32) % 2 ^ 18 * 2 ^ 8 + messageDigestByte D 33 := by
  have := messageDigestByte_lt D 33
  simp only [digestIndex, messageDigestBigEndian, forsMessageByteCount, treeIndexByteCount,
    leafIndexByteCount, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reduceAdd]
  omega

/-- **The index of a digest**: the top 10 bits from call 0, the low 16 from call 1. -/
theorem digestIndex_truncate (d : DigestCall → HashOutput) :
    digestIndex (truncateMessageDigest d) = joinIndex (hiOf (d 0)) (loOf (d 1)) := by
  apply Fin.ext
  rw [digestIndex_val, messageDigestByte_truncate_lo d 30 (by norm_num),
    messageDigestByte_truncate_lo d 31 (by norm_num),
    messageDigestByte_truncate_hi d 32 le_rfl (by norm_num),
    messageDigestByte_truncate_hi d 33 (by norm_num) (by norm_num)]
  have h0 := outputByte_lt (d 0) 30
  have h1 := outputByte_lt (d 0) 31
  have h2 := outputByte_lt (d 1) 0
  have h3 := outputByte_lt (d 1) 1
  simp only [joinIndex, hiOf, loOf, Nat.reduceSub]
  omega

/-- `m` bits `c 0, ..., c (m - 1)`, most significant first. -/
def bitFold (c : ℕ → ℕ) (m : ℕ) : ℕ :=
  (List.range m).foldl (fun v j ↦ 2 * v + c j) 0

theorem bitFold_succ (c : ℕ → ℕ) (m : ℕ) : bitFold c (m + 1) = 2 * bitFold c m + c m := by
  simp [bitFold, List.range_succ, List.foldl_append]

theorem bitFold_congr {c c' : ℕ → ℕ} : ∀ m, (∀ j < m, c j = c' j) → bitFold c m = bitFold c' m
  | 0, _ => rfl
  | m + 1, h => by
    rw [bitFold_succ, bitFold_succ, bitFold_congr m fun j hj ↦ h j (by omega), h m (by omega)]

theorem bitFold_lt {c : ℕ → ℕ} (hc : ∀ j, c j < 2) : ∀ m, bitFold c m < 2 ^ m
  | 0 => by simp [bitFold]
  | m + 1 => by
    rw [bitFold_succ, Nat.pow_succ]
    have := bitFold_lt hc m
    have := hc m
    omega

theorem bitFold_bit {c : ℕ → ℕ} (hc : ∀ j, c j < 2) :
    ∀ m j, j < m → bitFold c m / 2 ^ (m - 1 - j) % 2 = c j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, j, h => by
    rw [bitFold_succ]
    have hcm := hc m
    by_cases hj : j = m
    · subst hj
      rw [show j + 1 - 1 - j = 0 by omega, Nat.pow_zero, Nat.div_one]
      omega
    · rw [show m + 1 - 1 - j = (m - 1 - j) + 1 by omega, Nat.pow_succ', ← Nat.div_div_eq_div_mul,
        show (2 * bitFold c m + c m) / 2 = bitFold c m by omega]
      exact bitFold_bit hc m j (by omega)

/-- Bit `j` of FORS leaf `κ` of a hash output read as call 0, most significant first. -/
def leafBit (y : HashOutput) (κ j : ℕ) : ℕ :=
  messageDigestBit (BitVec.ofNat (8 * digestByteCount) y.toNat) (forsTreeHeight * κ + j)

theorem leafBit_eq (y : HashOutput) (κ j : ℕ) :
    leafBit y κ j = (y.toNat.testBit (7 - (10 * κ + j) % 8 + 8 * ((10 * κ + j) / 8))).toNat := by
  rw [leafBit, messageDigestBit_eq, toNat_ofNat_of_lt (lt_of_lt_of_le y.isLt
    (Nat.pow_le_pow_right (by norm_num) (by norm_num [digestByteCount])))]
  rfl

theorem leafBit_lt (y : HashOutput) (κ j : ℕ) : leafBit y κ j < 2 := by
  rw [leafBit_eq]
  exact Bool.toNat_lt _

theorem leavesOf_val (y : HashOutput) (κ : ForsTreeIndex) :
    (leavesOf y κ).val = bitFold (leafBit y κ.val) forsTreeHeight :=
  Nat.mod_eq_of_lt (bitFold_lt (leafBit_lt y κ.val) _)

/-- **The FORS leaves of a digest** are call 0's. -/
theorem digestForsLeaves_truncate (d : DigestCall → HashOutput) :
    digestForsLeaves (truncateMessageDigest d) = leavesOf (d 0) := by
  funext κ
  apply Fin.ext
  rw [leavesOf_val]
  have hκ : κ.val < 24 := κ.isLt
  have hfold : bitFold (fun j ↦ messageDigestBit (truncateMessageDigest d)
      (forsTreeHeight * κ.val + j)) forsTreeHeight = bitFold (leafBit (d 0) κ.val) forsTreeHeight :=
    bitFold_congr _ fun j hj ↦ by
      have hj' : j < 10 := hj
      rw [messageDigestBit_eq, leafBit_eq, testBit_truncate_lo d _ (by
        simp only [forsTreeHeight]
        omega)]
      rfl
  rw [← hfold]
  exact Nat.mod_eq_of_lt (bitFold_lt (fun j ↦ by rw [messageDigestBit_eq]; exact Bool.toNat_lt _) _)

/-! ### Fibers -/

theorem bool_toNat_inj {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Call 0's first 240 bits are its leaves'. -/
theorem testBit_eq_of_leavesOf_eq {y y' : HashOutput} (h : leavesOf y = leavesOf y') (i : ℕ)
    (hi : i < 240) : y.toNat.testBit i = y'.toNat.testBit i := by
  obtain ⟨κ, j, hκ, hj, hp⟩ : ∃ κ j, κ < 24 ∧ j < 10 ∧
      7 - (10 * κ + j) % 8 + 8 * ((10 * κ + j) / 8) = i :=
    ⟨(8 * (i / 8) + (7 - i % 8)) / 10, (8 * (i / 8) + (7 - i % 8)) % 10, by omega, by omega,
      by omega⟩
  have hv := congrArg (fun f ↦ (f ⟨κ, hκ⟩ : ForsLeafIndex).val) h
  simp only [leavesOf_val] at hv
  have hb : bitFold (leafBit y κ) forsTreeHeight / 2 ^ (forsTreeHeight - 1 - j) % 2 =
      bitFold (leafBit y' κ) forsTreeHeight / 2 ^ (forsTreeHeight - 1 - j) % 2 := by
    rw [hv]
  rw [bitFold_bit (leafBit_lt y κ) forsTreeHeight j hj,
    bitFold_bit (leafBit_lt y' κ) forsTreeHeight j hj, leafBit_eq, leafBit_eq, hp] at hb
  exact bool_toNat_inj hb

/-- A hash output as its digest view `(hiOf, leavesOf)` and the 6 bits call 0 does not use (the high
bits of byte 30). -/
def hiLeavesSplit (y : HashOutput) :
    (Fin (2 ^ 10) × (ForsTreeIndex → ForsLeafIndex)) × Fin (2 ^ 6) :=
  ((hiOf y, leavesOf y), ⟨outputByte y 30 / 4, by
    have := outputByte_lt y 30
    show _ < 64
    omega⟩)

theorem div_two_pow_248 (n : ℕ) : n / 2 ^ 248 = n / 2 ^ 240 / 256 := by
  rw [Nat.div_div_eq_div_mul, show (2 : ℕ) ^ 248 = 2 ^ 240 * 256 by norm_num]

theorem div_two_pow_240_lt (y : HashOutput) : y.toNat / 2 ^ 240 < 65536 :=
  Nat.div_lt_of_lt_mul (lt_of_lt_of_le y.isLt (by norm_num))

theorem hiLeavesSplit_injective : Function.Injective hiLeavesSplit := by
  intro y y' h
  have hhi : y.toNat / 2 ^ 240 % 256 % 4 * 256 + y.toNat / 2 ^ 248 % 256 =
      y'.toNat / 2 ^ 240 % 256 % 4 * 256 + y'.toNat / 2 ^ 248 % 256 :=
    congrArg Fin.val (congrArg (fun p ↦ p.1.1) h)
  have hleaves : leavesOf y = leavesOf y' := congrArg (fun p ↦ p.1.2) h
  have hrest : y.toNat / 2 ^ 240 % 256 / 4 = y'.toNat / 2 ^ 240 % 256 / 4 :=
    congrArg (fun p ↦ p.2.val) h
  have hhigh : y.toNat / 2 ^ 240 = y'.toNat / 2 ^ 240 := by
    have b := div_two_pow_240_lt y
    have b' := div_two_pow_240_lt y'
    rw [div_two_pow_248, div_two_pow_248] at hhi
    generalize y.toNat / 2 ^ 240 = A at hhi hrest b
    generalize y'.toNat / 2 ^ 240 = A' at hhi hrest b'
    omega
  have hlow : y.toNat % 2 ^ 240 = y'.toNat % 2 ^ 240 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < 240
    · rw [testBit_eq_of_leavesOf_eq hleaves i hi]
    · simp [hi]
  apply BitVec.eq_of_toNat_eq
  rw [← Nat.mod_add_div y.toNat (2 ^ 240), ← Nat.mod_add_div y'.toNat (2 ^ 240), hlow, hhigh]

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := by
  rw [Fintype.card_congr (bitsEquiv 256)]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem hiLeavesSplit_bijective : Function.Bijective hiLeavesSplit := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hiLeavesSplit_injective, ?_⟩
  rw [card_hashOutput]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, forsTreeCount, forsTreeHeight]
  norm_num

theorem card_filter_fst {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (v : A) :
    #(univ.filter fun p : A × B ↦ p.1 = v) = Fintype.card B := by
  rw [show (univ.filter fun p : A × B ↦ p.1 = v) = {v} ×ˢ univ by
      ext p
      simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, and_true],
    card_product, card_singleton, one_mul, card_univ]

/-- **Each digest view of call 0 has `2^6` preimages.** -/
theorem card_fiber_hiLeaves (v : Fin (2 ^ 10) × (ForsTreeIndex → ForsLeafIndex)) :
    #(univ.filter fun y : HashOutput ↦ (hiOf y, leavesOf y) = v) = 2 ^ 6 := by
  rw [card_equiv (Equiv.ofBijective _ hiLeavesSplit_bijective)
      (t := univ.filter fun p : (Fin (2 ^ 10) × (ForsTreeIndex → ForsLeafIndex)) × Fin (2 ^ 6) ↦
        p.1 = v) fun y ↦ by simp [hiLeavesSplit],
    card_filter_fst, Fintype.card_fin]

/-- A hash output as its low index bits `loOf` and the 240 bits from byte 2 on. -/
def loSplit (y : HashOutput) : Fin (2 ^ 16) × Fin (2 ^ 240) :=
  (loOf y, ⟨y.toNat / 2 ^ 16, by
    have := y.isLt
    omega⟩)

theorem loSplit_bijective : Function.Bijective loSplit := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun y y' h ↦ ?_, ?_⟩
  · simp only [loSplit, loOf, outputByte, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨hlo, hrest⟩ := h
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one] at hlo
    omega
  · rw [card_hashOutput]
    simp only [Fintype.card_prod, Fintype.card_fin]
    norm_num

/-- **Each low index of call 1 has `2^240` preimages.** -/
theorem card_fiber_loOf (lo : Fin (2 ^ 16)) :
    #(univ.filter fun y : HashOutput ↦ loOf y = lo) = 2 ^ 240 := by
  rw [card_equiv (Equiv.ofBijective _ loSplit_bijective)
      (t := univ.filter fun p : Fin (2 ^ 16) × Fin (2 ^ 240) ↦ p.1 = lo) fun y ↦ by
        simp [loSplit],
    card_filter_fst, Fintype.card_fin]

/-- A rate as its hash output and its remaining 832 bits. -/
def outSplit : X ≃ HashOutput × (Fin 832 → ZMod 2) :=
  (Fin.appendEquiv (α := ZMod 2) 256 832).symm.trans
    ((bitsEquiv 256).symm.prodCongr (Equiv.refl _))

theorem outSplit_fst (x : X) : (outSplit x).1 = out256 x :=
  rfl

/-- A property of the hash output holds on `2^832` rates per output. -/
theorem card_filter_out256 (P : HashOutput → Prop) [DecidablePred P] :
    #(univ.filter fun x : X ↦ P (out256 x)) = #(univ.filter P) * 2 ^ 832 := by
  rw [card_equiv outSplit (t := (univ.filter P) ×ˢ (univ : Finset (Fin 832 → ZMod 2))) fun x ↦ by
      simp only [mem_filter, mem_univ, true_and, mem_product, and_true, outSplit_fst],
    card_product, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- Each hash output has `2^832` preimages under `out256`. -/
theorem card_fiber_out256 (y : HashOutput) :
    #(univ.filter fun x : X ↦ out256 x = y) = 2 ^ 832 := by
  rw [card_filter_out256 (· = y), filter_eq' univ y, ite_eq_left (mem_univ y), card_singleton,
    Nat.one_mul]

/-- **The rates of a call-0 digest view**: `2^838` each. -/
theorem card_fiber_hiLeaves_out256 (v : Fin (2 ^ 10) × (ForsTreeIndex → ForsLeafIndex)) :
    #(univ.filter fun x : X ↦ (hiOf (out256 x), leavesOf (out256 x)) = v) = 2 ^ 838 := by
  rw [card_filter_out256 (fun y ↦ (hiOf y, leavesOf y) = v), card_fiber_hiLeaves, ← pow_add]

/-- **The rates of a call-1 low index**: `2^1072` each. -/
theorem card_fiber_loOf_out256 (lo : Fin (2 ^ 16)) :
    #(univ.filter fun x : X ↦ loOf (out256 x) = lo) = 2 ^ 1072 := by
  rw [card_filter_out256 (fun y ↦ loOf y = lo), card_fiber_loOf, ← pow_add]

end Quantum.Sphincs

end
