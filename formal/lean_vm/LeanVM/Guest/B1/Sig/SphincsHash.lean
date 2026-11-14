/-
  LeanVM.Guest.B1.Sig.SphincsHash

  leanSPHINCS's addressed hash (the statement's, over Keccak-f[1600] in `Id`) as a function of the
  guest's cells (`crates/signatures/src/lean_sphincs/hash.rs:28-93`,
  `lean_ethereum.py:501-519, 3707-3712, 4057-4068`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssScheme
public import LeanVM.Guest.B1.Sig.WotsSound
public import LeanVM.Guest.B1.Sig.SphincsAdrs

/-!
# leanSPHINCS's hash over cells

The statement's addressed hash (`Sphincs.Verification.addressedHash`) is
`Trunc_16(H(PK.seed ‖ ADRS ‖ M))` (`th`, `hash.rs:85-88`), the address 32 bytes of big-endian
words (`Address.toBytes`, `as_bytes`, `hash.rs:75-77`). The guest hashes cells, 16 little-endian
bytes each, and holds the address as two (`adrsCell0`, `adrsCell1`, `lean_ethereum.py:501-513`):

* `bigEndianBytes_four`, `bigEndianBytes_eight`: a big-endian word's bytes are the little-endian
  bytes of its byte reversal, `beWordAt 0`;
* `adrs_toBytes_cells`: the address's bytes are its two cells' (no bound on the fields: both sides
  read them modulo `2^32`, the tree modulo `2^64`);
* `addressedHash_cells`: the hash of the bytes of cells is the first cell of the `hcell` of
  `PK.seed`, the two address cells and the cells; `addressedHash_digest`, `addressedHash_node`,
  `addressedHash_digests` for a payload of one, two, or a vector of digests that are cells' values;
* `addressedHash_encoding`: the encoding's 68 bytes, `PK.seed ‖ ADRS ‖ M ‖ BE_32(c)` (`encoder`,
  `wots.rs:68-73`), are the first 68 bytes of the cells `[P, A0, A1] ++ M ++ [counter]`, the
  counter cell holding `BE_32(c)` in its low four bytes: the number `beWordAt 0 c`, `c`'s bytes
  reversed. The guest builds that number from four hinted bytes, the first lowest
  (`sp_from_bytes`, `lean_ethereum.py:3925-3936`; `sp_layer`, `lean_ethereum.py:4127-4136`), so
  the hinted bytes are `BE_32(c)` in order;
* `adrsCell1_add_words23`, `adrsCell1_add_word0`, `adrsCell1_add_step`, `adrsCell1_add_type`: the
  guest's constants added to an `A1` cell (field addition is XOR, the bits disjoint) set its words:
  a chain step's `i·2^88 + s·2^120` (`walk`, `lean_ethereum.py:3735-3761`), a type's `t·2^24`;
* `hashDomainCells`, `hashDomain_cells`, `tweakableHash_sphincsCells`: each hash domain's two
  address cells (`hashDomainFields`, `wots.rs:41-73`, `scheme.rs:252-260`, `fors.rs:27-59`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open HashSig HashSig.OverPermutation

@[expose] public section

/-! ## Big-endian words as little-endian bytes -/

@[simp] theorem length_bigEndianBytes (k : Nat) (v : BitVec (8 * k)) :
    (Sphincs.bigEndianBytes k v).length = k := by
  simp [Sphincs.bigEndianBytes]

theorem toNat_getElem_bigEndianBytes (k : Nat) (v : BitVec (8 * k)) (i : Nat)
    (h : i < (Sphincs.bigEndianBytes k v).length) :
    (Sphincs.bigEndianBytes k v)[i].toNat = v.toNat / 2 ^ (8 * (k - 1 - i)) % 256 := by
  simp [Sphincs.bigEndianBytes, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem beWordAt_eq (k w : Nat) : beWordAt k w = 2 ^ (32 * k) * beWordAt 0 w := by
  simp [beWordAt]

/-- A word's byte reversal is a 32-bit number. -/
theorem beWordAt_zero_lt (w : Nat) : beWordAt 0 w < 2 ^ 32 := by
  simp only [beWordAt]
  omega

/-- A byte of a number below `2^b` is the number's. -/
theorem modDiv (w b j : Nat) (hj : 8 * j + 8 ≤ b) :
    w % 2 ^ b / 2 ^ (8 * j) % 256 = w / 2 ^ (8 * j) % 256 := by
  rw [show (2 : Nat) ^ b = 2 ^ (8 * j) * (256 * 2 ^ (b - 8 * j - 8)) by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_add, ← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

/-- Byte `i` of a word's byte reversal is the word's byte `3 - i`. -/
theorem beDigit (w i : Nat) (hi : i < 4) :
    w / 2 ^ (8 * (4 - 1 - i)) % 256 = beWordAt 0 w / 256 ^ i % 256 := by
  have h0 : w / 2 ^ 24 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have h1 : w / 2 ^ 16 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have h2 : w / 2 ^ 8 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have h3 : w % 256 < 256 := Nat.mod_lt _ (by norm_num)
  interval_cases i <;>
  · simp only [Nat.reduceSub, Nat.reduceMul, pow_zero, Nat.div_one, one_mul, beWordAt]
    generalize w / 2 ^ 24 % 256 = a at *
    generalize w / 2 ^ 16 % 256 = b at *
    generalize w / 2 ^ 8 % 256 = c at *
    generalize w % 256 = d at *
    simp only [Nat.reducePow]
    omega

/-- **A big-endian 32-bit word's bytes** are the little-endian bytes of its byte reversal. -/
theorem bigEndianBytes_four (w : Nat) :
    Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 w) = leBytes (beWordAt 0 w) 4 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [length_leBytes] at h2
  apply UInt8.toNat_inj.mp
  rw [toNat_getElem_bigEndianBytes, getElem_leBytes, toNat_uint8_ofNat]
  simp only [BitVec.toNat_ofNat]
  rw [modDiv w 32 (4 - 1 - i) (by omega), beDigit w i h2]

/-- **A big-endian 64-bit word's bytes**: its high word's, then its low word's. -/
theorem bigEndianBytes_eight (w : Nat) :
    Sphincs.bigEndianBytes 8 (BitVec.ofNat 64 w) =
      Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 (w / 2 ^ 32)) ++
        Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 w) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_append, length_bigEndianBytes] at h2
  apply UInt8.toNat_inj.mp
  rw [toNat_getElem_bigEndianBytes]
  by_cases hi : i < 4
  · rw [List.getElem_append_left (by simpa using hi), toNat_getElem_bigEndianBytes]
    simp only [BitVec.toNat_ofNat]
    rw [modDiv w 64 (8 - 1 - i) (by omega), modDiv (w / 2 ^ 32) 32 (4 - 1 - i) (by omega),
      Nat.div_div_eq_div_mul, ← pow_add, show 32 + 8 * (4 - 1 - i) = 8 * (8 - 1 - i) by omega]
  · rw [List.getElem_append_right (by simpa using hi), toNat_getElem_bigEndianBytes]
    simp only [BitVec.toNat_ofNat, length_bigEndianBytes]
    rw [modDiv w 64 (8 - 1 - i) (by omega), modDiv w 32 (4 - 1 - (i - 4)) (by omega),
      show 8 * (4 - 1 - (i - 4)) = 8 * (8 - 1 - i) by omega]

/-- Four words in the four slots of a cell: their byte reversals, in order. -/
theorem leBytes_beWords (a b c d : Nat) :
    leBytes (beWordAt 0 a + beWordAt 1 b + beWordAt 2 c + beWordAt 3 d) 16 =
      leBytes (beWordAt 0 a) 4 ++ leBytes (beWordAt 0 b) 4 ++ leBytes (beWordAt 0 c) 4 ++
        leBytes (beWordAt 0 d) 4 := by
  have ha := beWordAt_zero_lt a
  have hb := beWordAt_zero_lt b
  have hc := beWordAt_zero_lt c
  rw [beWordAt_eq 1, beWordAt_eq 2, beWordAt_eq 3,
    show beWordAt 0 a + 2 ^ (32 * 1) * beWordAt 0 b + 2 ^ (32 * 2) * beWordAt 0 c +
        2 ^ (32 * 3) * beWordAt 0 d =
      beWordAt 0 a + 256 ^ 4 * (beWordAt 0 b + 256 ^ 4 * (beWordAt 0 c + 256 ^ 4 * beWordAt 0 d))
      by ring,
    show 16 = 4 + (4 + (4 + 4)) from rfl,
    leBytes_add_mul _ _ _ _ (by norm_num; omega), leBytes_add_mul _ _ _ _ (by norm_num; omega),
    leBytes_add_mul _ _ _ _ (by norm_num; omega)]
  simp only [List.append_assoc]

/-- The bytes of a cell of four words. -/
theorem cellBytes_beWords (a b c d : Nat) :
    cellBytes (cellOf128 (BitVec.ofNat 128 (beWordAt 0 a + beWordAt 1 b + beWordAt 2 c +
        beWordAt 3 d))) =
      leBytes (beWordAt 0 a) 4 ++ leBytes (beWordAt 0 b) 4 ++ leBytes (beWordAt 0 c) 4 ++
        leBytes (beWordAt 0 d) 4 := by
  rw [cellBytes_eq_leBytes, cellNat_cellOf128, BitVec.toNat_ofNat,
    show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num, leBytes_mod, leBytes_beWords]

/-! ## The address as two cells -/

/-- **The address's bytes are its two cells'.** -/
theorem adrs_toBytes_cells (layer tree : Nat) (ty : Sphincs.AddressType) (kp w2 w3 : Nat) :
    (Sphincs.makeAddress layer tree ty kp w2 w3).toBytes =
      cellBytes (adrsCell0 layer tree) ++ cellBytes (adrsCell1 ty.word kp w2 w3) := by
  have e0 : adrsCell0 layer tree = cellOf128 (BitVec.ofNat 128 (beWordAt 0 layer + beWordAt 1 0 +
      beWordAt 2 (tree / 2 ^ 32) + beWordAt 3 tree)) := by
    simp [adrsCell0, beWordAt]
  rw [e0, adrsCell1, cellBytes_beWords, cellBytes_beWords]
  simp only [Sphincs.Address.toBytes, Sphincs.makeAddress]
  rw [bigEndianBytes_eight, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl]
  simp only [bigEndianBytes_four]
  simp only [List.append_assoc]

/-! ## The addressed hash of cells -/

/-- **An addressed hash of cells**: at an address whose bytes are the cells `a0`, `a1`, the hash
of the bytes of cells is the first cell of the `hcell` of `PK.seed`, the address and the cells. -/
theorem addressedHash_of_cells {pp a0 a1 : E} {address : Sphincs.Address}
    (ha : address.toBytes = cellBytes a0 ++ cellBytes a1) (vs : List E) :
    Sphincs.Verification.addressedHash (m := Id) keccakF1600 (cellVal pp) address
        (vs.flatMap cellBytes) = cellVal (hcell ([pp, a0, a1] ++ vs)).1 := by
  show truncateHash (keccakHash (m := Id) keccakF1600
    (Sphincs.addressedHashInput (cellVal pp) address (vs.flatMap cellBytes))) = _
  rw [keccakHash_keccakF1600, truncateHash_keccakBits, Sphincs.addressedHashInput, hasherInput,
    bytesLE_cellVal, ha]
  simp only [hcell, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]
  rfl

/-- **The addressed hash of cells at `makeAddress`.** -/
theorem addressedHash_cells (pp : E) (layer tree : Nat) (ty : Sphincs.AddressType)
    (kp w2 w3 : Nat) (vs : List E) :
    Sphincs.Verification.addressedHash (m := Id) keccakF1600 (cellVal pp)
        (Sphincs.makeAddress layer tree ty kp w2 w3) (vs.flatMap cellBytes) =
      cellVal (hcell ([pp, adrsCell0 layer tree, adrsCell1 ty.word kp w2 w3] ++ vs)).1 :=
  addressedHash_of_cells (adrs_toBytes_cells layer tree ty kp w2 w3) vs

/-! ## Payloads of digests -/

/-- One digest that is a cell's value. -/
theorem digest_cells (x : E) : littleEndianBytes 16 (cellVal x) = [x].flatMap cellBytes := by
  simp [bytesLE_cellVal]

/-- Two digests that are cells' values, a node's children. -/
theorem nodePayload_cellVal (l r : E) :
    nodePayload (cellVal l) (cellVal r) = [l, r].flatMap cellBytes := by
  simp [nodePayload, bytesLE_cellVal]

/-- The bytes of digests that are cells' values. -/
theorem flatMap_bytes_cellVal (l : List E) :
    (l.map cellVal).flatMap (littleEndianBytes 16) = l.flatMap cellBytes := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.flatMap_cons, bytesLE_cellVal, ih]

/-- A vector of digests that are cells' values. -/
theorem digestsPayload_cells {n : Nat} (c : Fin n → E) :
    digestsPayload (fun i => cellVal (c i)) = (List.ofFn c).flatMap cellBytes := by
  have e : (List.ofFn fun i => (cellVal (c i) : HashSig.Digest)) = (List.ofFn c).map cellVal :=
    (List.map_ofFn (f := c) (g := cellVal)).symm
  exact (congrArg (fun l => List.flatMap (littleEndianBytes 16) l) e).trans (flatMap_bytes_cellVal _)

theorem addressedHash_digest (pp x : E) (layer tree : Nat) (ty : Sphincs.AddressType)
    (kp w2 w3 : Nat) :
    Sphincs.Verification.addressedHash (m := Id) keccakF1600 (cellVal pp)
        (Sphincs.makeAddress layer tree ty kp w2 w3) (littleEndianBytes 16 (cellVal x)) =
      cellVal (hcell [pp, adrsCell0 layer tree, adrsCell1 ty.word kp w2 w3, x]).1 := by
  rw [digest_cells, addressedHash_cells]
  rfl

theorem addressedHash_node (pp l r : E) (layer tree : Nat) (ty : Sphincs.AddressType)
    (kp w2 w3 : Nat) :
    Sphincs.Verification.addressedHash (m := Id) keccakF1600 (cellVal pp)
        (Sphincs.makeAddress layer tree ty kp w2 w3) (nodePayload (cellVal l) (cellVal r)) =
      cellVal (hcell [pp, adrsCell0 layer tree, adrsCell1 ty.word kp w2 w3, l, r]).1 := by
  rw [nodePayload_cellVal, addressedHash_cells]
  rfl

theorem addressedHash_digests (pp : E) (layer tree : Nat) (ty : Sphincs.AddressType)
    (kp w2 w3 : Nat) {n : Nat} (c : Fin n → E) :
    Sphincs.Verification.addressedHash (m := Id) keccakF1600 (cellVal pp)
        (Sphincs.makeAddress layer tree ty kp w2 w3) (digestsPayload fun i => cellVal (c i)) =
      cellVal (hcell ([pp, adrsCell0 layer tree, adrsCell1 ty.word kp w2 w3] ++ List.ofFn c)).1 := by
  rw [digestsPayload_cells, addressedHash_cells]

/-! ## The encoding: digests and a counter -/

/-- **The counter's bytes**: `BE_32(c)` is the first four bytes of the cell of `c`'s byte
reversal. -/
theorem bigEndianBytes_counter (ctr : Sphincs.EncodingCounter) :
    Sphincs.bigEndianBytes 4 ctr = (cellBytes (eOfNat (beWordAt 0 ctr.toNat))).take 4 := by
  have e : ctr = BitVec.ofNat 32 ctr.toNat :=
    BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt ctr.isLt).symm
  rw [cellBytes_eOfNat (lt_of_lt_of_le (beWordAt_zero_lt _) (by norm_num)),
    ← leBytes_append _ 4 12, List.take_left' (by simp)]
  conv_lhs => rw [e]
  exact bigEndianBytes_four _

theorem length_flatMap_cellBytes : ∀ cs : List E, (cs.flatMap cellBytes).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
      simp only [List.flatMap_cons, List.length_append, length_cellBytes,
        length_flatMap_cellBytes cs, List.length_cons]
      ring

/-- Cells cut `k ≤ 16` bytes into the last. -/
theorem take_cellsBytes_append (cs : List E) (x : E) (k : Nat) (hk : k ≤ 16) :
    (cellsBytes (cs ++ [x])).take (16 * cs.length + k) =
      cs.flatMap cellBytes ++ (cellBytes x).take k := by
  have hl := length_flatMap_cellBytes cs
  rw [cellsBytes_eq_flatMap, List.flatMap_append, List.take_append,
    List.take_of_length_le (by omega), hl, show 16 * cs.length + k - 16 * cs.length = k by omega]
  simp

/-- **The encoding's hash over cells**: `PK.seed ‖ ADRS ‖ M ‖ BE_32(c)`, `M` the bytes of the cells
`vs`, is the hash of the first `16 (|vs| + 3) + 4` bytes of `PK.seed`, the address cells, `vs` and
the counter's cell, which holds `c`'s byte reversal. -/
theorem addressedHash_encoding (pp : E) (layer tree : Nat) (ty : Sphincs.AddressType)
    (kp w2 w3 : Nat) (vs : List E) (ctr : Sphincs.EncodingCounter) :
    Sphincs.Verification.addressedHash (m := Id) keccakF1600 (cellVal pp)
        (Sphincs.makeAddress layer tree ty kp w2 w3)
        (vs.flatMap cellBytes ++ Sphincs.bigEndianBytes 4 ctr) =
      cellVal (digestHalves (keccak256 ((cellsBytes ([pp, adrsCell0 layer tree,
        adrsCell1 ty.word kp w2 w3] ++ vs ++ [eOfNat (beWordAt 0 ctr.toNat)])).take
          (16 * (vs.length + 3) + 4)))).1 := by
  show truncateHash (keccakHash (m := Id) keccakF1600 (Sphincs.addressedHashInput (cellVal pp)
    (Sphincs.makeAddress layer tree ty kp w2 w3) (vs.flatMap cellBytes ++
      Sphincs.bigEndianBytes 4 ctr))) = _
  rw [keccakHash_keccakF1600, truncateHash_keccakBits,
    show 16 * (vs.length + 3) + 4 =
      16 * ([pp, adrsCell0 layer tree, adrsCell1 ty.word kp w2 w3] ++ vs).length + 4 by
      simp only [List.length_append, List.length_cons, List.length_nil]; ring,
    take_cellsBytes_append _ _ 4 (by norm_num), Sphincs.addressedHashInput, hasherInput,
    bytesLE_cellVal, adrs_toBytes_cells, bigEndianBytes_counter]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]
  rfl

/-- The encoding's hash of one digest, the message a layer signs, and the counter: the guest's
`KECCAK` of `[P, A0, A1 + WOTS_ENC, M, counter]` cut at 68 bytes. -/
theorem addressedHash_encodingDigest (pp m : E) (layer tree : Nat) (ty : Sphincs.AddressType)
    (kp w2 w3 : Nat) (ctr : Sphincs.EncodingCounter) :
    Sphincs.Verification.addressedHash (m := Id) keccakF1600 (cellVal pp)
        (Sphincs.makeAddress layer tree ty kp w2 w3)
        (littleEndianBytes 16 (cellVal m) ++ Sphincs.bigEndianBytes 4 ctr) =
      cellVal (digestHalves (keccak256 ((cellsBytes [pp, adrsCell0 layer tree,
        adrsCell1 ty.word kp w2 w3, m, eOfNat (beWordAt 0 ctr.toNat)]).take 68))).1 := by
  rw [digest_cells, addressedHash_encoding]
  rfl

/-- The bytes of cells ending in the counter's cell are zero past its four bytes (what the guest's
`KECCAK` of `len = 16 |cs| + 4` needs, `kMsg_sound`). -/
theorem cellsBytes_counterCell_zero (cs : List E) (ctr : Nat) :
    ∀ j, 16 * cs.length + 4 ≤ j → (cellsBytes (cs ++ [eOfNat (beWordAt 0 ctr)])).getD j 0 = 0 := by
  intro j hj
  have hN := beWordAt_zero_lt ctr
  have hl := length_flatMap_cellBytes cs
  rw [cellsBytes_eq_flatMap, List.flatMap_append, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [cellBytes_eOfNat (by omega)]
  by_cases h16 : j - 16 * cs.length < 16
  · rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some, getElem_leBytes]
    have : beWordAt 0 ctr / 256 ^ (j - 16 * cs.length) = 0 := Nat.div_eq_of_lt (by
      calc beWordAt 0 ctr < 2 ^ 32 := hN
        _ ≤ 256 ^ 4 := by norm_num
        _ ≤ 256 ^ (j - 16 * cs.length) := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [this]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-! ## Constants added to an address cell -/

/-- A cell is the 128-bit word of its number. -/
theorem cellOf128_eq_eOfNat128 {n : Nat} (h : n < 2 ^ 128) :
    cellOf128 (BitVec.ofNat 128 n) = eOfNat128 n := by
  simp only [cellOf128, eOfNat128]
  congr 1
  · apply BF64.toBitVec_injective
    simp only [K.ofBits, BF64.toBitVec_ofBitVec]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat]
  · apply BF64.toBitVec_injective
    simp only [K.ofBits, BF64.toBitVec_ofBitVec]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt h]

theorem beWordAt_of_zero (k : Nat) : beWordAt k 0 = 0 := by simp [beWordAt]

/-- The number `adrsCell1 type keyPair word2 word3` holds. -/
def adrsNat1 (type keyPair word2 word3 : Nat) : Nat :=
  beWordAt 0 type + beWordAt 1 keyPair + beWordAt 2 word2 + beWordAt 3 word3

theorem adrsNat1_lt (type keyPair word2 word3 : Nat) : adrsNat1 type keyPair word2 word3 < 2 ^ 128 := by
  have h0 := beWordAt_zero_lt type
  have h1 := beWordAt_zero_lt keyPair
  have h2 := beWordAt_zero_lt word2
  have h3 := beWordAt_zero_lt word3
  simp only [adrsNat1, beWordAt_eq 1 keyPair, beWordAt_eq 2 word2, beWordAt_eq 3 word3,
    Nat.reduceMul, Nat.reducePow] at h0 h1 h2 h3 ⊢
  omega

/-- The second address cell is the 128-bit word of its number. -/
theorem adrsCell1_eq (type keyPair word2 word3 : Nat) :
    adrsCell1 type keyPair word2 word3 = eOfNat128 (adrsNat1 type keyPair word2 word3) :=
  cellOf128_eq_eOfNat128 (adrsNat1_lt type keyPair word2 word3)

/-- **Words 2 and 3 added to an address cell whose words 2 and 3 are zero** (field addition is
XOR, and the bits are disjoint). -/
theorem adrsCell1_add_words23 (type keyPair word2 word3 : Nat) :
    adrsCell1 type keyPair 0 0 + lit (beWordAt 2 word2 + beWordAt 3 word3) =
      adrsCell1 type keyPair word2 word3 := by
  have h0 := beWordAt_zero_lt type
  have h1 := beWordAt_zero_lt keyPair
  have h2 := beWordAt_zero_lt word2
  have h3 := beWordAt_zero_lt word3
  have hc : beWordAt 2 word2 + beWordAt 3 word3 =
      2 ^ 64 * (beWordAt 0 word2 + 2 ^ 32 * beWordAt 0 word3) := by
    rw [beWordAt_eq 2, beWordAt_eq 3]; ring
  have hN : adrsNat1 type keyPair 0 0 = beWordAt 0 type + 2 ^ 32 * beWordAt 0 keyPair := by
    simp only [adrsNat1, beWordAt_of_zero, beWordAt_eq 1 keyPair]; ring
  have hlo : adrsNat1 type keyPair 0 0 < 2 ^ 64 := by rw [hN]; omega
  rw [adrsCell1_eq, adrsCell1_eq, lit_eq (beWordAt 2 word2 + beWordAt 3 word3) (by rw [hc]; omega),
    ← eOfNat128_xor, hc, Nat.xor_comm, two_pow_mul_xor hlo, hN]
  congr 1
  simp only [adrsNat1, beWordAt_eq 1 keyPair, beWordAt_eq 2 word2, beWordAt_eq 3 word3]
  ring

/-- **The type word added to an address cell of type zero.** -/
theorem adrsCell1_add_word0 (type keyPair word2 word3 : Nat) :
    adrsCell1 0 keyPair word2 word3 + lit (beWordAt 0 type) = adrsCell1 type keyPair word2 word3 := by
  have hr := beWordAt_zero_lt type
  have hN : adrsNat1 0 keyPair word2 word3 = 2 ^ 32 * (beWordAt 0 keyPair +
      2 ^ 32 * beWordAt 0 word2 + 2 ^ 64 * beWordAt 0 word3) := by
    simp only [adrsNat1, beWordAt_of_zero, beWordAt_eq 1 keyPair, beWordAt_eq 2 word2,
      beWordAt_eq 3 word3]
    ring
  rw [adrsCell1_eq, adrsCell1_eq, lit_eq (beWordAt 0 type) (by omega), ← eOfNat128_xor, hN,
    two_pow_mul_xor hr]
  congr 1
  simp only [adrsNat1, beWordAt_eq 1 keyPair, beWordAt_eq 2 word2, beWordAt_eq 3 word3]
  ring

/-- A byte in word slot `0` of a cell: its low byte at bit `24`. -/
theorem beWordAt_zero_of_lt {t : Nat} (h : t < 256) : beWordAt 0 t = t * 2 ^ 24 := by
  simp only [beWordAt, Nat.reduceMul, Nat.reducePow]
  omega

/-- A byte in word slot `2`: at bit `88`. -/
theorem beWordAt_two_of_lt {i : Nat} (h : i < 256) : beWordAt 2 i = i * 2 ^ 88 := by
  simp only [beWordAt, Nat.reduceMul, Nat.reducePow]
  omega

/-- A byte in word slot `3`: at bit `120`. -/
theorem beWordAt_three_of_lt {s : Nat} (h : s < 256) : beWordAt 3 s = s * 2 ^ 120 := by
  simp only [beWordAt, Nat.reduceMul, Nat.reducePow]
  omega

/-- Two bytes in word slot `3`: the low at bit `120`, the high at bit `112`. -/
theorem beWordAt_three_of_lt_pow16 {j : Nat} (h : j < 2 ^ 16) :
    beWordAt 3 j = j % 256 * 2 ^ 120 + j / 256 * 2 ^ 112 := by
  simp only [beWordAt, Nat.reduceMul, Nat.reducePow] at h ⊢
  omega

/-- A literal below `2^64` is a word. -/
theorem lit_of_lt {c : Nat} (h : c < 2 ^ 64) : lit c = word c 0 := by
  rw [lit, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, Nat.zero_mod]

/-- **A chain step's constant** (`spStepC i s = i·2^88 + s·2^120`, `walk`,
`lean_ethereum.py:3735-3761`) added to the key's address cell: chain `i`, step `s`. -/
theorem adrsCell1_add_step {type keyPair i s : Nat} (hi : i < 256) (hs : s < 256) :
    adrsCell1 type keyPair 0 0 + lit (i * 2 ^ 88 + s * 2 ^ 120) = adrsCell1 type keyPair i s := by
  rw [← beWordAt_two_of_lt hi, ← beWordAt_three_of_lt hs]
  exact adrsCell1_add_words23 type keyPair i s

/-- **A type constant** (`t·2^24`, as `SP_WOTS_PK` and the others) added to an address cell of type
zero. -/
theorem adrsCell1_add_type {t keyPair word2 word3 : Nat} (ht : t < 256) :
    adrsCell1 0 keyPair word2 word3 + word (t * 2 ^ 24) 0 = adrsCell1 t keyPair word2 word3 := by
  rw [← lit_of_lt (c := t * 2 ^ 24) (by omega), ← beWordAt_zero_of_lt ht]
  exact adrsCell1_add_word0 t keyPair word2 word3

/-! ## The hash domains' address cells -/

/-- **Each hash domain's two address cells** (`hashDomainFields`): a chain step type `WOTS_HASH`
(`0`), the leaf `WOTS_PK` (`1`), a node `TREE` (`2`, key pair `0`), the encoding `WOTS_ENC` (`7`),
FORS leaves and nodes `FORS_TREE` (`3`) at the bottom key `K_0(idx)`, their height and
`forsTreeIndex`, the FORS roots `FORS_ROOTS` (`4`). -/
def hashDomainCells : Sphincs.HashDomain → E × E
  | .chain layer tree leaf chainIndex step =>
      (adrsCell0 layer.val tree.val, adrsCell1 0 leaf.val chainIndex.val step.val)
  | .leaf layer tree leaf => (adrsCell0 layer.val tree.val, adrsCell1 1 leaf.val 0 0)
  | .node layer tree height nodeIndex =>
      (adrsCell0 layer.val tree.val, adrsCell1 2 0 height nodeIndex)
  | .encoding layer tree leaf => (adrsCell0 layer.val tree.val, adrsCell1 7 leaf.val 0 0)
  | .forsLeaf index forsTree forsLeaf =>
      (adrsCell0 0 (Sphincs.treeOfIndex 0 index).val,
        adrsCell1 3 (Sphincs.leafOfIndex 0 index).val 0
          (Sphincs.forsTreeIndex forsTree 0 forsLeaf.val))
  | .forsNode index forsTree height node =>
      (adrsCell0 0 (Sphincs.treeOfIndex 0 index).val,
        adrsCell1 3 (Sphincs.leafOfIndex 0 index).val height
          (Sphincs.forsTreeIndex forsTree height node))
  | .forsRoots index =>
      (adrsCell0 0 (Sphincs.treeOfIndex 0 index).val,
        adrsCell1 4 (Sphincs.leafOfIndex 0 index).val 0 0)

/-- **A hash domain's address bytes are its two cells'.** -/
theorem hashDomain_cells (d : Sphincs.HashDomain) :
    (Sphincs.hashDomainFields d).toBytes =
      cellBytes (hashDomainCells d).1 ++ cellBytes (hashDomainCells d).2 := by
  cases d <;> exact adrs_toBytes_cells _ _ _ _ _ _

/-- **The tweakable hash of cells at a hash domain.** -/
theorem tweakableHash_sphincsCells (pp : E) (d : Sphincs.HashDomain) (vs : List E) :
    Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp) d (vs.flatMap cellBytes) =
      cellVal (hcell ([pp, (hashDomainCells d).1, (hashDomainCells d).2] ++ vs)).1 :=
  addressedHash_of_cells (hashDomain_cells d) vs

end
end LeanVM.Guest.B1.Sig
