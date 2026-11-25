module

public import Native.Xmss.Model
public import Native.Xmss.Layout
public import Native.Bytes

/-!
# The model is leanXMSS verification

`verifyW_encode`: the word-level model `verifyW` on the input words of a public key, a message and
a signature (`encode`) is `LeanXmss.verifyWithKeccak`. Every spec hash `Th(P, A, M)` is `hashW` of
the words of `P`, the address and the payload (`th_eq`), a digest being two words (`toDigest`); then
each step of `LeanXmss.Verification` is the model's: the message digest (`messageDigest_eq`), the
digits and the codeword check (`codewordW_iff`), the chains (`chainWalk_eq`), the leaf
(`leafHash_eq`), the fold up the tree (`treeFold_eq`), a layer (`layerRoot_eq`) and the two layers.
-/

@[expose] public section

namespace Native.XmssVerifier

open LeanXmss HashSig HashSig.OverPermutation Keccak LeanVM.Protocol.KeccakHash
open LeanXmss.Verification
open LeanVM.Semantics (keccakF1600)

/-! ## Bytes and words -/

/-- The `n` little-endian bytes of `x`. -/
def bytes (x n : Nat) : List UInt8 := (List.range n).map fun i ↦ UInt8.ofNat (x / 256 ^ i)

/-- `littleEndianBytes` as `bytes`. -/
theorem littleEndianBytes_eq_bytes (n : Nat) (v : BitVec (8 * n)) :
    littleEndianBytes n v = bytes v.toNat n := by
  apply List.ext_getElem (by simp [littleEndianBytes, bytes])
  intro i h1 h2
  simp only [littleEndianBytes, bytes, List.getElem_ofFn, List.getElem_map, List.getElem_range]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    pow_mul]
  rfl

/-- A word's bytes as `bytes`. -/
theorem wordBytes_eq_bytes (w : UInt64) : wordBytes w = bytes w.toNat 8 := by
  apply List.ext_getElem (by simp [wordBytes, bytes])
  intro i h1 h2
  have hi : i < 8 := by simpa [bytes] using h2
  simp only [wordBytes, bytes, List.getElem_map, List.getElem_range]
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, show 8 * i % 2 ^ 64 % 64 = 8 * i by omega,
    pow_mul]
  rfl

/-- The first `a + b` bytes are the first `a`, then `b` bytes of `x / 256^a`. -/
theorem bytes_add (x a b : Nat) : bytes x (a + b) = bytes x a ++ bytes (x / 256 ^ a) b := by
  simp only [bytes, List.range_add, List.map_append, List.map_map, Function.comp_def, pow_add,
    Nat.div_div_eq_div_mul]

/-- The first `n` bytes depend only on `x % 256^n`. -/
theorem bytes_congr {x y n : Nat} (h : x % 256 ^ n = y % 256 ^ n) : bytes x n = bytes y n := by
  refine List.map_congr_left fun i hi ↦ UInt8.toNat_inj.mp ?_
  rw [List.mem_range] at hi
  have key : ∀ z, z / 256 ^ i % 2 ^ 8 = z % 256 ^ n / 256 ^ i % 256 := fun z ↦ by
    rw [show 256 ^ n = 256 ^ i * 256 ^ (n - i) by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (by omega))]
    rfl
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', key x, key y, h]

/-- `wordsBytes` of an append. -/
theorem wordsBytes_append (a b : List UInt64) :
    wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b :=
  List.flatMap_append

/-- An `or` of disjoint words is their sum. -/
theorem toNat_or_of_dvd {a b : UInt64} (n : Nat) (ha : 2 ^ n ∣ a.toNat) (hb : b.toNat < 2 ^ n) :
    (a ||| b).toNat = a.toNat + b.toNat := by
  obtain ⟨q, hq⟩ := ha
  rw [UInt64.toNat_or, hq, mul_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hb]

/-- The address word of layer `l`, key `e` and type byte `b`, as a number. -/
theorem tweakW_toNat {l e b : UInt64} (hl : l.toNat ≤ 1) (he : e.toNat < 2 ^ 32)
    (hb : b.toNat < 256) :
    (tweakW l e b).toNat = e.toNat + 2 ^ 55 * l.toNat + 2 ^ 56 * b.toNat := by
  have h55 : (l <<< 55).toNat = 2 ^ 55 * l.toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    omega
  have h56 : (b <<< 56).toNat = 2 ^ 56 * b.toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    omega
  have h1 : ((l <<< 55) ||| e).toNat = 2 ^ 55 * l.toNat + e.toNat := by
    rw [toNat_or_of_dvd 55 (by rw [h55]; exact Dvd.intro _ rfl) (by omega), h55]
  rw [tweakW, UInt64.or_comm, toNat_or_of_dvd 56 (by rw [h56]; exact Dvd.intro _ rfl) (by omega),
    h1, h56]
  omega

/-- The address word of a node, as a number. -/
theorem nodeTweakW_toNat {l j k : UInt64} (hl : l.toNat ≤ 1) (hj : j.toNat < 2 ^ 23)
    (hk : k.toNat < 2 ^ 32) :
    (nodeTweakW l j k).toNat = k.toNat + 2 ^ 32 * (j.toNat + 2 ^ 23 * l.toNat) + 2 ^ 56 * 3 := by
  have h23 : (l <<< 23).toNat = 2 ^ 23 * l.toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    omega
  have hhi : ((l <<< 23) + j).toNat = j.toNat + 2 ^ 23 * l.toNat := by
    rw [UInt64.toNat_add, h23]; omega
  have h32 : (((l <<< 23) + j) <<< 32).toNat = 2 ^ 32 * (j.toNat + 2 ^ 23 * l.toNat) := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, hhi]
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    omega
  have h56 : ((3 : UInt64) <<< 56).toNat = 2 ^ 56 * 3 := by decide
  have h1 : ((((l <<< 23) + j) <<< 32) ||| k).toNat =
      2 ^ 32 * (j.toNat + 2 ^ 23 * l.toNat) + k.toNat := by
    rw [toNat_or_of_dvd 32 (by rw [h32]; exact Dvd.intro _ rfl) hk, h32]
  rw [nodeTweakW, UInt64.or_comm,
    toNat_or_of_dvd 56 (by rw [h56]; exact Dvd.intro _ rfl) (by omega), h1, h56]
  omega

/-! ## Digests as words -/

/-- The digest of two words, low first. -/
def toDigest (v : W2) : Digest := ofWords v.1 v.2

/-- A digest is the digest of its words. -/
theorem toDigest_words (d : Digest) : toDigest (digestLo d, digestHi d) = d := ofWords_digest d

theorem digestLo_toDigest (v : W2) : digestLo (toDigest v) = v.1 := digestLo_ofWords _ _

theorem digestHi_toDigest (v : W2) : digestHi (toDigest v) = v.2 := digestHi_ofWords _ _

/-- The number of two words. -/
theorem toNat_ofWords (lo hi : UInt64) : (ofWords lo hi).toNat = lo.toNat + 2 ^ 64 * hi.toNat := by
  have := lo.toNat_lt
  have := hi.toNat_lt
  rw [ofWords, BitVec.toNat_ofNat]
  omega

/-- A digest's bytes are its words'. -/
theorem littleEndianBytes_digest (d : Digest) :
    littleEndianBytes 16 d = wordsBytes [digestLo d, digestHi d] :=
  littleEndianBytes_16 d

/-- The bytes of the digest of two words are theirs. -/
theorem littleEndianBytes_toDigest (v : W2) :
    littleEndianBytes 16 (toDigest v) = wordsBytes [v.1, v.2] := by
  rw [littleEndianBytes_digest, digestLo_toDigest, digestHi_toDigest]

/-- Comparing a digest with the root is comparing its words. -/
theorem decide_toDigest_eq (v : W2) (d : Digest) :
    decide (toDigest v = d) = (v == (digestLo d, digestHi d)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  constructor
  · rintro rfl
    rw [digestLo_toDigest, digestHi_toDigest]
  · intro h
    rw [h, toDigest_words]

/-! ## Digits and codewords -/

/-- `digitW D i` is digit `i` of the digest `D`. -/
theorem digitW_toNat (D : W2) {i : Nat} (hi : i < 64) :
    (digitW D i).toNat = (ofWords D.1 D.2).toNat / 2 ^ (2 * i) % 4 := by
  have h1 := D.1.toNat_lt
  rw [digitW, UInt64.toNat_and, show (3 : UInt64).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, toNat_ofWords, shiftW]
  split
  · rw [UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow,
      show 2 * i % 2 ^ 64 % 64 = 2 * i by omega]
    have h : 2 ^ 64 = 2 ^ (2 * i) * (4 * 2 ^ (62 - 2 * i)) := by
      rw [show (4 : Nat) = 2 ^ 2 from rfl, ← pow_add, ← pow_add]; congr 1; omega
    rw [h, mul_assoc, Nat.add_mul_div_left _ _ (by positivity), mul_assoc,
      Nat.add_mul_mod_self_left]
  · rw [UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow,
      show 2 * (i - 32) % 2 ^ 64 % 64 = 2 * (i - 32) by omega,
      show 2 * i = 64 + 2 * (i - 32) by omega, pow_add, ← Nat.div_div_eq_div_mul,
      show (D.1.toNat + 2 ^ 64 * D.2.toNat) / 2 ^ 64 = D.2.toNat by omega]

/-- A digit is at most `3`. -/
theorem digitW_le (D : W2) (i : Nat) : (digitW D i).toNat ≤ 3 := by
  rw [digitW, UInt64.toNat_and]
  exact Nat.and_le_right

/-- `digestDigits` is `digitW`. -/
theorem digestDigits_toDigest (D : W2) {n : Nat} (hn : n ≤ 64) (i : Fin n) :
    (digestDigits (toDigest D) i).val = (digitW D i).toNat := by
  unfold digestDigits
  rw [BitVec.val_toFin]
  show ((ofWords D.1 D.2).extractLsb' (2 * i) 2).toNat = _
  rw [BitVec.extractLsb'_toNat, digitW_toNat D (by omega), Nat.shiftRight_eq_div_pow]

/-- The first `n` digits' sum does not overflow. -/
theorem digitSumW_toNat (D : W2) : ∀ n, n ≤ 58 →
    (digitSumW D n).toNat = ∑ i ∈ Finset.range n, (digitW D i).toNat ∧
      ∑ i ∈ Finset.range n, (digitW D i).toNat ≤ 3 * n
  | 0, _ => by simp [digitSumW]
  | n + 1, hn => by
    obtain ⟨ih, hb⟩ := digitSumW_toNat D n (by omega)
    have h3 : (digitW D n).toNat ≤ 3 := by
      rw [digitW, UInt64.toNat_and]; exact Nat.and_le_right
    rw [digitSumW, UInt64.toNat_add, ih, Finset.sum_range_succ]
    omega

/-- **`codewordW` is `Codeword.Valid`.** -/
theorem codewordW_iff (D : W2) : codewordW D = true ↔ Codeword.Valid (toDigest D) := by
  obtain ⟨hs, -⟩ := digitSumW_toNat D 58 le_rfl
  have hsum : Codeword.sum (digestDigits (toDigest D)) =
      ∑ i ∈ Finset.range 58, (digitW D i).toNat := by
    rw [Codeword.sum]
    simp only [digestDigits_toDigest D (n := chainCount) (by decide)]
    exact Fin.sum_univ_eq_sum_range (fun i ↦ (digitW D i).toNat) 58
  have h1 := D.1.toNat_lt
  unfold Codeword.Valid
  rw [hsum, ← hs]
  show _ ↔ (ofWords D.1 D.2).toNat / 2 ^ 116 = 0 ∧ (digitSumW D 58).toNat = 106
  rw [toNat_ofWords, codewordW, Bool.and_eq_true, beq_iff_eq,
    beq_iff_eq, ← UInt64.toNat_inj, ← UInt64.toNat_inj, UInt64.toNat_shiftRight]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  omega

/-! ## Hash inputs as words -/

/-- **`Th` over Keccak-f[1600] is `hashW`** of `P`, the address words `w, 0` and the payload's
words. -/
theorem th_eq (P : PublicParameter) (fields : TweakFields) (payload : HashInput) {w : UInt64}
    {ws : List UInt64} (ha : addressBytes fields = wordsBytes [w, 0])
    (hp : payload = wordsBytes ws) :
    Id.run (th (m := Id) keccakF1600 P fields payload) =
      toDigest (hashW ([digestLo P, digestHi P, w, 0] ++ ws)) := by
  have hi : thInput P fields payload = wordsBytes ([digestLo P, digestHi P, w, 0] ++ ws) := by
    rw [thInput, hasherInput, ha, hp, littleEndianBytes_16, ← wordsBytes_append,
      ← wordsBytes_append]
    rfl
  rw [th, Id.run_bind, Id.run_pure, hi, truncate_keccakHash]
  rfl

/-- The 16 address bytes are the bytes of the words `w, 0`. -/
theorem addressBytes_tweakFields (tag step hi lo : Nat) {w : UInt64}
    (hw : w.toNat = lo % 2 ^ 32 + 2 ^ 32 * (hi % 2 ^ 24) + 2 ^ 56 * (tag % 32 + 32 * (step % 8))) :
    addressBytes (tweakFields tag step hi lo) = wordsBytes [w, 0] := by
  have hb : (BitVec.ofNat 3 step ++ BitVec.ofNat 5 tag).toNat = tag % 32 + 32 * (step % 8) := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have h1 : bytes w.toNat 4 = bytes (lo % 2 ^ 32) 4 := bytes_congr (by omega)
  have h2 : bytes (w.toNat / 256 ^ 4) 3 = bytes (hi % 2 ^ 24) 3 := bytes_congr (by omega)
  have h3 : bytes (w.toNat / 256 ^ 4 / 256 ^ 3) 1 = bytes (tag % 32 + 32 * (step % 8)) 1 :=
    bytes_congr (by omega)
  simp only [addressBytes, tweakFields, littleEndianBytes_eq_bytes, hb, BitVec.toNat_ofNat,
    wordsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, wordBytes_eq_bytes,
    UInt64.toNat_zero, Nat.reduceMul]
  rw [show bytes w.toNat 8 = bytes w.toNat (4 + (3 + 1)) from rfl, bytes_add, bytes_add, h1, h2,
    h3]
  simp only [List.append_assoc]
  rfl

/-- Two layers. -/
theorem layer_lt (layer : Layer) : layer.val < 2 := layer.isLt

/-- Key indices are below `2^32`. -/
theorem key_lt (key : KeyIndex) : key.val < 2 ^ 32 := key.isLt

/-- The address of a chain, leaf or message hash of key `e` on layer `l`. -/
theorem addressBytes_tweakW (layer : Layer) (key : KeyIndex) {l e b : UInt64}
    (hl : l.toNat = layer.val) (he : e.toNat = key.val) {tag step : Nat} (htag : tag < 32)
    (hstep : step < 8) (hb : b.toNat = tag + 32 * step) :
    addressBytes (tweakFields tag step (layerHi layer 0) key.val) =
      wordsBytes [tweakW l e b, 0] := by
  have := layer_lt layer
  have := key_lt key
  refine addressBytes_tweakFields _ _ _ _ ?_
  rw [tweakW_toNat (by omega) (by omega) (by omega), layerHi]
  omega

/-- The address of the node at `level`, index `idx`, of layer `l`. -/
theorem addressBytes_nodeTweakW (layer : Layer) {l j k : UInt64} (hl : l.toNat = layer.val)
    {level idx : Nat} (hj : j.toNat = level) (hlevel : level < 2 ^ 23) (hk : k.toNat = idx)
    (hidx : idx < 2 ^ 32) :
    addressBytes (tweakFields 3 0 (layerHi layer level) idx) =
      wordsBytes [nodeTweakW l j k, 0] := by
  have := layer_lt layer
  refine addressBytes_tweakFields _ _ _ _ ?_
  rw [nodeTweakW_toNat (by omega) (by omega) (by omega), layerHi]
  omega

/-- A chain step's payload as words. -/
theorem chainPayload_eq (i : ChainIndex) (v : W2) :
    chainPayload i (toDigest v) = wordsBytes [v.1, v.2, i.val.toUInt64, 0] := by
  have hi : i.val < 58 := i.isLt
  have hlo : digestLo (BitVec.ofNat 128 i.val) = i.val.toUInt64 := by
    rw [digestLo, BitVec.toNat_ofNat, Nat.toUInt64_eq, Nat.mod_eq_of_lt (by omega)]
  have hhi : digestHi (BitVec.ofNat 128 i.val) = 0 := by
    rw [digestHi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    rfl
  unfold chainPayload
  rw [littleEndianBytes_toDigest, littleEndianBytes_16, hlo, hhi, ← wordsBytes_append]
  rfl

/-- A node's payload as words. -/
theorem nodePayload_eq (a b : Digest) :
    nodePayload a b = wordsBytes [digestLo a, digestHi a, digestLo b, digestHi b] := by
  rw [nodePayload, littleEndianBytes_digest, littleEndianBytes_digest, ← wordsBytes_append]
  rfl

/-- A leaf's payload as words. -/
theorem digestsPayload_eq {n : Nat} (g : Nat → W2) :
    digestsPayload (fun i : Fin n ↦ toDigest (g i)) = wordsBytes (pairWords n g) := by
  have h : List.ofFn (fun i : Fin n ↦ toDigest (g i)) = (List.range n).map fun i ↦ toDigest (g i) :=
    List.ext_getElem (by simp) fun i _ _ ↦ by simp
  unfold digestsPayload
  rw [h, pairWords, wordsBytes, List.flatMap_assoc]
  exact (List.flatMap_map _ _ _).trans
    (List.flatMap_congr fun i _ ↦ littleEndianBytes_toDigest _)

/-! ## The input words -/

/-- Chain `i`'s words of a layer's signature. -/
theorem layerWord_chain (ls : LayerSignature) {i : Nat} (hi : i < chainCount) :
    layerWord ls (2 + 2 * i) = digestLo (ls.chainValues ⟨i, hi⟩) ∧
      layerWord ls (3 + 2 * i) = digestHi (ls.chainValues ⟨i, hi⟩) := by
  unfold chainCount at hi
  constructor
  · rw [layerWord, ite_eq_right (by omega), dite_eq_left (by omega)]
    unfold digestWord
    rw [ite_eq_left (by omega)]
    congr 2; ext; simp only; omega
  · rw [layerWord, ite_eq_right (by omega), dite_eq_left (by omega)]
    unfold digestWord
    rw [ite_eq_right (by omega)]
    congr 2; ext; simp only; omega

/-- The path's words at level `j` of a layer's signature. -/
theorem layerWord_path (ls : LayerSignature) {j : Nat} (hj : j < layerHeight) :
    layerWord ls (118 + 2 * j) = digestLo (ls.authenticationPath ⟨j, hj⟩) ∧
      layerWord ls (119 + 2 * j) = digestHi (ls.authenticationPath ⟨j, hj⟩) := by
  unfold layerHeight at hj
  constructor
  · rw [layerWord, ite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
    unfold digestWord
    rw [ite_eq_left (by omega)]
    congr 2; ext; simp only; omega
  · rw [layerWord, ite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
    unfold digestWord
    rw [ite_eq_right (by omega)]
    congr 2; ext; simp only; omega

/-- Words `0 .. 8` of the input. -/
theorem encode_head (pk : PublicKey) (message : Message) (sig : Signature) :
    (encode pk message sig 0, encode pk message sig 1) = (digestLo pk.root, digestHi pk.root) ∧
    (encode pk message sig 2, encode pk message sig 3) =
      (digestLo pk.parameter, digestHi pk.parameter) ∧
    [encode pk message sig 4, encode pk message sig 5, encode pk message sig 6,
      encode pk message sig 7] = (List.range 4).map (word256 message) ∧
    encode pk message sig 8 = sig.leafIndex.val.toUInt64 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Word `9 + 150 n + k` of the input is word `k` of layer `n`'s signature. -/
theorem encode_layer (pk : PublicKey) (message : Message) (sig : Signature) {n k : Nat}
    (hn : n < 2) (hk : k < 150) :
    encode pk message sig (9 + 150 * n + k) = layerWord (sig.layers ⟨n, hn⟩) k := by
  unfold encode
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), dite_eq_left (by unfold layerWords; omega)]
  simp only [layerWords]
  congr 2
  · ext; simp only; omega
  · omega

/-- The key of layer `n` is the leaf index shifted right by `16 n`. -/
theorem keyIndex_eq (sig : Signature) (n : Nat) (hn : n < 2) :
    (sig.leafIndex.val.toUInt64 >>> (16 * n).toUInt64).toNat =
      (keyIndexOnLayer sig.leafIndex ⟨n, hn⟩).val := by
  have h : sig.leafIndex.val < 2 ^ 32 := sig.leafIndex.isLt
  rw [UInt64.toNat_shiftRight, Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  rfl

/-! ## The steps of verification -/

/-- `sequenceFin` in `Id` runs each computation. -/
theorem sequenceFin_id {α : Type} : ∀ {n : Nat} (f : Fin n → Id α),
    Id.run (sequenceFin f) = fun i ↦ Id.run (f i)
  | 0, _ => funext fun i ↦ i.elim0
  | n + 1, f => by
    funext i
    have ih := sequenceFin_id fun j : Fin n ↦ f j.succ
    simp only [sequenceFin, Id.run_bind, Id.run_pure] at ih ⊢
    cases i using Fin.cases with
    | zero => rfl
    | succ j => exact congrFun ih j

/-- **A chain walk is `walkW`.** -/
theorem chainWalk_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) (i : ChainIndex)
    {Pw : W2} (hP : Pw = (digestLo P, digestHi P)) {l e : UInt64} (hl : l.toNat = layer.val)
    (he : e.toNat = key.val) (d : Nat) :
    ∀ k, d + k ≤ 3 → ∀ v : W2,
      Id.run (chainWalk (m := Id) keccakF1600 P layer key i d k (toDigest v)) =
        toDigest (walkW (chainStepW Pw l e i.val.toUInt64) d k v)
  | 0, _, _ => rfl
  | k + 1, hk, v => by
    have ih := chainWalk_eq P layer key i hP hl he d k (by omega) v
    unfold chainWalk at ih ⊢
    rw [walkChain, Id.run_bind, ih, dite_eq_left (by unfold chainLength winternitzBits; omega)]
    simp only [walkW]
    subst hP
    refine (th_eq _ _ _ (addressBytes_tweakW layer key hl he (by decide)
      (show d + k < 8 by omega) ?_) (chainPayload_eq _ _)).trans rfl
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat',
      Nat.shiftLeft_eq]
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    omega

/-- **The message digest is `msgDigestW`.** -/
theorem messageDigest_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) {Pw : W2}
    (hP : Pw = (digestLo P, digestHi P)) {l e : UInt64} (hl : l.toNat = layer.val)
    (he : e.toNat = key.val) (msg : List UInt64) (R : Randomizer) {Rw : W2}
    (hR : Rw = (digestLo R, digestHi R)) :
    Id.run (messageDigest (m := Id) keccakF1600 P layer key (wordsBytes msg) R) =
      toDigest (msgDigestW Pw l e msg Rw) := by
  subst hP hR
  refine (th_eq (w := tweakW l e 12) (ws := msg ++ [digestLo R, digestHi R]) _ _ _
    (addressBytes_tweakW layer key hl he (by decide) (by decide) rfl) ?_).trans ?_
  · rw [littleEndianBytes_digest, ← wordsBytes_append]
  · simp only [msgDigestW, List.append_assoc]

/-- **The leaf is `leafW`.** -/
theorem leafHash_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) {Pw : W2}
    (hP : Pw = (digestLo P, digestHi P)) {l e : UInt64} (hl : l.toNat = layer.val)
    (he : e.toNat = key.val) (ends : Nat → W2) :
    Id.run (leafHash (m := Id) keccakF1600 P layer key fun i ↦ toDigest (ends i.val)) =
      toDigest (leafW Pw l e ends) := by
  subst hP
  exact (th_eq _ _ _ (addressBytes_tweakW layer key hl he (by decide) (by decide) rfl)
    (digestsPayload_eq ends)).trans rfl

/-- The node's side: bit `j` of the key. -/
theorem testBit_iff {e : UInt64} {key j : Nat} (he : e.toNat = key) (hj : j < 64) :
    (e >>> j.toUInt64 &&& 1 = 0) ↔ key.testBit j = false := by
  rw [← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt hj, he,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  simp only [UInt64.reduceToNat, Nat.and_one_is_mod, decide_eq_false_iff_not]
  omega

/-- **The fold up the tree is `foldW`.** -/
theorem treeFold_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) {Pw : W2}
    (hP : Pw = (digestLo P, digestHi P)) {l e : UInt64} (hl : l.toNat = layer.val)
    (he : e.toNat = key.val) (ls : LayerSignature) (path : Nat → W2)
    (hpath : ∀ j (h : j < layerHeight),
      path j = (digestLo (ls.authenticationPath ⟨j, h⟩), digestHi (ls.authenticationPath ⟨j, h⟩))) :
    ∀ j, j ≤ 16 → ∀ v : W2,
      Id.run (treeFold (m := Id) keccakF1600 P layer key ls.authenticationPath j (toDigest v)) =
        toDigest (foldW Pw l e path j v)
  | 0, _, _ => rfl
  | j + 1, hj, v => by
    have ih := treeFold_eq P layer key hP hl he ls path hpath j (by omega) v
    unfold treeFold at ih ⊢
    have hjh : j < layerHeight := by unfold layerHeight; omega
    rw [foldPath, Id.run_bind, ih, dite_eq_left hjh]
    simp only [foldW, nodeW]
    have := key_lt key
    have hk : ((e >>> j.toUInt64) >>> (1 : UInt64)).toNat = key.val / 2 ^ (j + 1) := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega : j < 64), he,
        Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, pow_succ]
      rfl
    have ha := addressBytes_nodeTweakW layer hl (j := (j + 1).toUInt64)
      (k := (e >>> j.toUInt64) >>> 1) (level := j + 1) (idx := key.val / 2 ^ (j + 1))
      (by rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega) (by omega) hk
      (lt_of_le_of_lt (Nat.div_le_self _ _) this)
    subst hP
    rw [hpath j hjh]
    cases hb : key.val.testBit j
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_left ((testBit_iff he (by omega)).mpr hb)]
      exact (th_eq _ _ _ ha ((nodePayload_eq _ _).trans
        (by rw [digestLo_toDigest, digestHi_toDigest]))).trans rfl
    · rw [ite_eq_left (rfl : true = true),
        ite_eq_right fun h ↦ absurd ((testBit_iff he (by omega)).mp h) (by rw [hb]; decide)]
      exact (th_eq _ _ _ ha ((nodePayload_eq _ _).trans
        (by rw [digestLo_toDigest, digestHi_toDigest]))).trans rfl

/-- **The one-time leaf is `leafW` of the chain ends, if the digest is a codeword.** -/
theorem otsLeaf_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) {Pw : W2}
    (hP : Pw = (digestLo P, digestHi P)) {l e : UInt64} (hl : l.toNat = layer.val)
    (he : e.toNat = key.val) (msg : List UInt64) (ls : LayerSignature) (sw : Nat → UInt64)
    (hsw : ∀ k < 150, sw k = layerWord ls k) :
    Id.run (otsLeaf (m := Id) keccakF1600 P layer key (wordsBytes msg) ls.randomizer
        ls.chainValues) =
      if codewordW (msgDigestW Pw l e msg (sw 0, sw 1)) then
        some (toDigest (leafW Pw l e fun i ↦
          chainEndW Pw l e (msgDigestW Pw l e msg (sw 0, sw 1)) i (sw (2 + 2 * i), sw (3 + 2 * i))))
      else none := by
  have hR : (sw 0, sw 1) = (digestLo ls.randomizer, digestHi ls.randomizer) := by
    rw [hsw 0 (by omega), hsw 1 (by omega)]
    rfl
  unfold otsLeaf
  rw [Id.run_bind, messageDigest_eq P layer key hP hl he msg _ hR]
  generalize msgDigestW Pw l e msg (sw 0, sw 1) = D
  unfold Codeword.decode
  by_cases hc : codewordW D = true
  · rw [ite_eq_left ((codewordW_iff D).mp hc), ite_eq_left hc]
    dsimp only
    rw [Id.run_bind, sequenceFin_id, Id.run_bind, Id.run_pure]
    refine congrArg some (Eq.trans (congrArg (fun f ↦ Id.run (leafHash (m := Id) keccakF1600 P
      layer key f)) (funext fun i ↦ ?_)) (leafHash_eq P layer key hP hl he _))
    have hi : i.val < chainCount := i.isLt
    have hv : ls.chainValues i = toDigest (sw (2 + 2 * i.val), sw (3 + 2 * i.val)) := by
      rw [hsw _ (by unfold chainCount at hi; omega), hsw _ (by unfold chainCount at hi; omega),
        (layerWord_chain ls hi).1, (layerWord_chain ls hi).2, toDigest_words]
    have hd := digestDigits_toDigest D (n := chainCount) (by decide) i
    have hd3 := digitW_le D i
    unfold recoverChain
    rw [hd, hv]
    exact chainWalk_eq P layer key i hP hl he _ _ (by unfold chainLength winternitzBits; omega) _
  · rw [ite_eq_right (mt (codewordW_iff D).mpr hc), ite_eq_right hc]
    rfl

/-- **A layer's root is `layerW`'s, if its digest is a codeword.** -/
theorem layerRoot_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) {Pw : W2}
    (hP : Pw = (digestLo P, digestHi P)) {l e : UInt64} (hl : l.toNat = layer.val)
    (he : e.toNat = key.val) {message : HashInput} {msg : List UInt64}
    (hm : message = wordsBytes msg) (ls : LayerSignature) (sw : Nat → UInt64)
    (hsw : ∀ k < 150, sw k = layerWord ls k) :
    Id.run (layerRoot (m := Id) keccakF1600 P layer key message ls) =
      if (layerW Pw l e msg sw).1 then some (toDigest (layerW Pw l e msg sw).2) else none := by
  subst hm
  unfold layerRoot
  rw [Id.run_bind, otsLeaf_eq P layer key hP hl he msg ls sw hsw]
  have hpath : ∀ j (h : j < layerHeight), (sw (118 + 2 * j), sw (119 + 2 * j)) =
      (digestLo (ls.authenticationPath ⟨j, h⟩), digestHi (ls.authenticationPath ⟨j, h⟩)) :=
    fun j h ↦ by
      have : j < 16 := h
      rw [hsw _ (by omega), hsw _ (by omega), (layerWord_path ls h).1, (layerWord_path ls h).2]
  simp only [layerW]
  by_cases hc : codewordW (msgDigestW Pw l e msg (sw 0, sw 1)) = true
  · simp only [hc, ↓reduceIte]
    rw [Id.run_bind, treeFold_eq P layer key hP hl he ls _ hpath layerHeight (by decide),
      Id.run_pure]
    rfl
  · simp only [hc]
    rfl

/-! ## Verification -/

/-- **The model is leanXMSS verification**: `verifyW` on the input words of a public key, a message
and a signature is `LeanXmss.verifyWithKeccak`. -/
theorem verifyW_encode (pk : PublicKey) (msg : Message) (sig : Signature) :
    verifyW (encode pk msg sig) = verifyWithKeccak pk msg sig := by
  obtain ⟨h01, h23, h47, h8⟩ := encode_head pk msg sig
  have hsw := fun n hn k (hk : k < 150) ↦ encode_layer pk msg sig (n := n) hn hk
  unfold verifyWithKeccak Verification.verify verifyW
  generalize encode pk msg sig = inp at *
  rw [Id.run_bind, layerRoot_eq pk.parameter bottomLayer _ h23 (l := (0 : Nat).toUInt64) rfl
    (h8 ▸ keyIndex_eq sig 0 (by decide)) ((littleEndianBytes_32 msg).trans (congrArg _ h47.symm))
    (sig.layers bottomLayer) _ fun k hk ↦ hsw 0 (by decide) k hk]
  simp only [afterLayers, ite_true, one_ne_zero, ite_false, Bool.true_and]
  generalize layerW (inp 2, inp 3) (Nat.toUInt64 0) (inp 8 >>> (16 * 0).toUInt64)
    [inp 4, inp 5, inp 6, inp 7] (fun k ↦ inp (9 + 150 * 0 + k)) = r0
  obtain ⟨c0, R0⟩ := r0
  cases c0
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  simp only [↓reduceIte, Bool.true_and]
  rw [Id.run_bind, layerRoot_eq pk.parameter topLayer _ h23 (l := (1 : Nat).toUInt64) rfl
    (h8 ▸ keyIndex_eq sig 1 (by decide)) (littleEndianBytes_toDigest R0) (sig.layers topLayer) _
    fun k hk ↦ hsw 1 (by decide) k hk]
  generalize layerW (inp 2, inp 3) (Nat.toUInt64 1) (inp 8 >>> (16 * 1).toUInt64) [R0.1, R0.2]
    (fun k ↦ inp (9 + 150 * 1 + k)) = r1
  obtain ⟨c1, R1⟩ := r1
  cases c1
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  simp only [↓reduceIte, Bool.true_and, Id.run_pure]
  rw [decide_toDigest_eq, h01]

end Native.XmssVerifier
