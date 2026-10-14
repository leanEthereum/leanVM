import EthCryptographySpecs.Xmss
import LeanVMCircuits.Xmss.Words
import LeanVMCircuits.Xmss.Blake2s

/-!
# leanXMSS verification over words is the specification's

`Words.verify` of a public parameter, a root, a message, an epoch below `2 ^ 32` and a signature, all words, is the
vendored specification's `EthCryptographySpecs.Xmss.verify` on their little-endian bytes (`verify_eq`). Every hash is
`tweakHash_eq`: the specification's tweak is the words `tweak0`/`tweak1`, and its BLAKE2s is `hashWords`
(`Xmss.Blake2s`). The encoding reads the same digits and spare bits (`wotsEncode_eq`), the chains and the leaf hash
the same payloads (`chain_eq`, `leaf_eq`), and the Merkle climb picks sides by the same epoch bits (`computeRoot_eq`).
Decoding words to bytes is onto (`signature_onto`, `publicKey_onto`, `message_onto`, `epoch_onto`), so the bridge
covers every specification input.

This file imports the vendored specification, so it is not a module.
-/

namespace LeanVMCircuits.Xmss.Spec

open EthCryptographySpecs.Xmss LeanVMCircuits.Rec
open LeanVMCircuits.Xmss.Words (Dig Sig)

/-! ## Decoding words to bytes -/

/-- A digest from its two words. -/
def dig (d : Dig) : Digest := wordsVec _ [d.1, d.2]

/-- A public parameter from its two words. -/
def param (d : Dig) : PublicParam := wordsVec _ [d.1, d.2]

/-- A message from its four words. -/
def message (m : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) : Message :=
  wordsVec _ [m.1, m.2.1, m.2.2.1, m.2.2.2]

/-- A randomness from its three words. -/
def randomness (r : BitVec 64 × BitVec 64 × BitVec 64) : Randomness := wordsVec _ [r.1, r.2.1, r.2.2]

/-- A public key from its parameter's and its root's words. -/
def pk (pp root : Dig) : PublicKey := ⟨dig root, param pp⟩

/-- A signature from its words. -/
def signature (sig : Sig) : Signature :=
  ⟨Vector.ofFn (n := Constants.V) fun i => dig (sig.tips i), randomness sig.rho,
    Vector.ofFn (n := Constants.LOG_LIFETIME) fun l => dig (sig.path l)⟩

theorem packBytes_wordsVec (n : ℕ) (ws : List (BitVec 64)) (h : n = 8 * ws.length) :
    packBytes (wordsVec n ws) = wordsBytes ws := by
  subst h
  apply ByteArray.ext
  simp [packBytes, wordsVec, wordsBytes]

theorem packBytes_dig (d : Dig) : packBytes (dig d) = wordsBytes [d.1, d.2] := packBytes_wordsVec _ _ rfl
theorem packBytes_param (d : Dig) : packBytes (param d) = wordsBytes [d.1, d.2] := packBytes_wordsVec _ _ rfl

theorem wordsBytes_append (a b : List (BitVec 64)) : wordsBytes a ++ wordsBytes b = wordsBytes (a ++ b) := by
  apply ByteArray.ext
  rw [ByteArray.data_append]
  apply Array.ext
  · simp [wordsBytes]; omega
  · intro k h1 h2
    simp only [wordsBytes, Array.getElem_append, Array.getElem_ofFn, Array.size_ofFn]
    split
    · simp only [byteAt, wordAt, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · simp only [byteAt, wordAt, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      have e1 : (k - 8 * a.length) / 8 = k / 8 - a.length := by omega
      have e2 : (k - 8 * a.length) % 8 = k % 8 := by omega
      rw [e1, e2]

theorem wordsBytes_nil : wordsBytes [] = ByteArray.empty := by
  apply ByteArray.ext
  simp [wordsBytes]

theorem wordBytes_eq (x : UInt32) :
    Blake2s.Internal.wordBytes x = Vector.ofFn fun p : Fin 4 => byteOf x.toBitVec p.val := by
  apply Vector.ext
  intro p hp
  simp only [Blake2s.Internal.wordBytes, Vector.getElem_ofFn]
  exact shift_toUInt8 _ _ hp

theorem tweak_bytes (ty : TweakType) (sub idx : UInt32) :
    packBytes (makeTweak ty sub idx) =
      wordsBytes [Words.tweak0 ty.toByte.toNat sub.toNat, Words.tweak1 idx.toNat] := by
  apply ByteArray.ext
  apply Array.ext
  · simp [packBytes, wordsBytes]; rfl
  · intro k h1 h2
    have hk : k < 16 := by simpa [wordsBytes] using h2
    have hty := ty.toByte.toNat_lt
    have hs := sub.toNat_lt
    have hi := idx.toNat_lt
    simp only [packBytes, makeTweak, wordBytes_eq, Vector.toArray_append, Vector.toArray_ofFn, wordsBytes,
      Array.getElem_ofFn]
    apply UInt8.toNat_inj.mp
    simp only [byteAt]
    rw [byteOf_toNat]
    interval_cases k <;>
      simp [Array.getElem_append, byteOf_toNat, wordAt, Words.tweak0, Words.tweak1, Circuit.tweak0,
        PROTOCOL_DOMAIN_SEP] <;> omega

theorem tweakHash_eq (ty : TweakType) (sub idx : UInt32) (pp : Dig) (payload : List (BitVec 64)) :
    tweakHash (param pp) ty sub idx (wordsBytes payload) =
      dig (Words.th ty.toByte.toNat sub.toNat idx.toNat pp payload) := by
  simp only [tweakHash, tweakHashFull, tweakInput, tweak_bytes, packBytes_param, wordsBytes_append, hash_wordsBytes,
    Words.th, List.cons_append, List.nil_append]
  generalize digest (hashWords (Words.tweak0 ty.toByte.toNat sub.toNat :: Words.tweak1 idx.toNat :: pp.1 :: pp.2 ::
    payload)) = D
  apply Vector.toArray_inj.mp
  apply Array.ext
  · simp [dig, wordsVec, Constants.DIGEST_LEN]
  · intro k h1 h2
    have hk : k < 16 := by simpa [dig, wordsVec, Constants.DIGEST_LEN] using h2
    simp [dig, wordsVec, byteAt, wordAt, List.getD_eq_getElem?_getD]
    rcases (by omega : k / 8 = 0 ∨ k / 8 = 1) with e | e <;> simp [e]

/-! ## The encoding -/

theorem packBytes_message (m : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    packBytes (message m) = wordsBytes [m.1, m.2.1, m.2.2.1, m.2.2.2] := packBytes_wordsVec _ _ rfl

theorem packBytes_randomness (r : BitVec 64 × BitVec 64 × BitVec 64) :
    packBytes (randomness r) = wordsBytes [r.1, r.2.1, r.2.2] := packBytes_wordsVec _ _ rfl

/-- The specification reads digest half `h` as the word `h` of the pair. -/
theorem digestWord_dig (D : Dig) (h : Fin 2) :
    Internal.digestWord (dig D) h = UInt64.ofBitVec (if h.val = 0 then D.1 else D.2) := by
  fin_cases h
  · rw [← or64_bytes]
    simp [Internal.digestWord, or64, dig, wordsVec, byteAt, wordAt]
  · rw [← or64_bytes]
    simp [Internal.digestWord, or64, dig, wordsVec, byteAt, wordAt]

theorem digit_eq (w : BitVec 64) (r : ℕ) (hr : r < 21) :
    (Internal.digit (UInt64.ofBitVec w) r).val = Words.digit w r := by
  have h3 : (3 * UInt64.ofNat r).toNat % 64 = 3 * r := by
    simp [UInt64.toNat_mul, UInt64.toNat_ofNat]
  simp only [Internal.digit, Words.digit, Constants.CHAIN_LENGTH, Constants.W, UInt64.toNat_shiftRight, h3,
    Nat.shiftRight_eq_div_pow]
  rfl

theorem digits_eq (D : Dig) : (Internal.digits (dig D)).toList.map Fin.val = Words.digits D := by
  apply List.ext_getElem
  · simp only [List.length_map, Vector.length_toList, Words.digits, List.length_range]
    rfl
  · intro i h1 h2
    have hi : i < 42 := by simpa [Words.digits] using h2
    simp only [List.getElem_map, Vector.getElem_toList, Internal.digits, Vector.getElem_ofFn, Words.digits,
      List.getElem_range, digestWord_dig, Constants.V]
    rw [digit_eq _ _ (by omega)]
    by_cases hlt : i < 21
    · simp [hlt, show i / 21 = 0 by omega]
    · simp [hlt, show i / 21 ≠ 0 by omega]

theorem top_bit (x : BitVec 64) : (UInt64.ofBitVec x >>> 63 == 0) = !x.getLsbD 63 := by
  have h1 : x.getLsbD 63 = decide (2 ^ 63 ≤ x.toNat) := by
    rw [show (63 : ℕ) = 64 - 1 from rfl, ← BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_decide]
  have h2 : (UInt64.ofBitVec x >>> 63).toNat = x.toNat / 2 ^ 63 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  rw [h1]
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have : (UInt64.ofBitVec x >>> 63) ≠ 0 := by
      intro e
      rw [e] at h2
      simp at h2
      omega
    rw [decide_eq_true h, beq_eq_false_iff_ne.mpr this]
    rfl
  · have : (UInt64.ofBitVec x >>> 63) = 0 := by
      apply UInt64.toNat_inj.mp
      rw [h2]
      simp
      omega
    rw [decide_eq_false h, this]
    rfl

theorem padded_eq (D : Dig) : Internal.padded (dig D) = (!D.1.getLsbD 63 && !D.2.getLsbD 63) := by
  simp only [Internal.padded, digestWord_dig]
  simp [top_bit]

theorem foldl_val {n : ℕ} (l : List (Fin n)) (a : ℕ) :
    l.foldl (fun s d => s + d.val) a = a + (l.map Fin.val).sum := by
  induction l generalizing a with
  | nil => simp
  | cons d l ih => simp [ih, Nat.add_assoc]

theorem onTarget_eq (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V) :
    Internal.onTarget x = ((x.toList.map Fin.val).sum == 195) := by
  simp only [Internal.onTarget, ← Vector.foldl_toList, foldl_val, Constants.TARGET_SUM, Nat.zero_add]

theorem encodingPayload_eq (msg : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (rho : BitVec 64 × BitVec 64 × BitVec 64) :
    encodingPayload (message msg) (randomness rho) =
      wordsBytes [msg.1, msg.2.1, msg.2.2.1, msg.2.2.2, rho.1, rho.2.1, rho.2.2, 0] := by
  have hz : ByteArray.mk (Array.replicate 8 0) = wordsBytes [0] := by
    apply ByteArray.ext
    apply Array.ext
    · simp [wordsBytes]
    · intro k h1 h2
      have hk : k < 8 := by simpa using h1
      simp only [wordsBytes, Array.getElem_ofFn, Array.getElem_replicate]
      apply UInt8.toNat_inj.mp
      simp [byteAt, wordAt, byteOf_toNat, Nat.div_eq_of_lt hk]
  simp only [encodingPayload, packBytes_message, packBytes_randomness, hz, wordsBytes_append]
  rfl

theorem toNat_ofNat_lt (n : ℕ) (h : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n := by
  simp [UInt32.toNat_ofNat]
  omega

/-- The specification's encoding is the words' encoding, as digit values. -/
theorem wotsEncode_eq (pp : Dig) (msg : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
    (rho : BitVec 64 × BitVec 64 × BitVec 64) (epoch : ℕ) (he : epoch < 2 ^ 32) :
    (wotsEncode (param pp) (message msg) (randomness rho) (UInt32.ofNat epoch)).map (fun x => x.toList.map Fin.val) =
      Words.encode pp msg rho epoch := by
  simp only [wotsEncode, encodingPayload_eq, tweakHash_eq, toNat_ofNat_lt _ he, padded_eq, onTarget_eq, digits_eq]
  have h4 : TweakType.encoding.toByte.toNat = 4 := rfl
  have h0 : (0 : UInt32).toNat = 0 := rfl
  rw [h4, h0]
  unfold Words.encode
  generalize Words.th 4 0 epoch pp [msg.1, msg.2.1, msg.2.2.1, msg.2.2.2, rho.1, rho.2.1, rho.2.2, 0] = D
  by_cases h1 : D.1.getLsbD 63 = false <;> by_cases h2 : D.2.getLsbD 63 = false <;>
    by_cases h3 : (Words.digits D).sum = 195 <;> simp_all [digits_eq]

theorem chain_eq (pp : Dig) (epoch : ℕ) (he : epoch < 2 ^ 32) (i : Fin Constants.V) (start : ℕ) :
    ∀ (steps : ℕ) (h : start + steps < Constants.CHAIN_LENGTH) (v : Dig),
      EthCryptographySpecs.Xmss.chain (param pp) (UInt32.ofNat epoch) i start steps h (dig v) =
        dig ((List.range' start steps).foldl (fun v s => Words.chainStep i s epoch pp v) v)
  | 0, h, v => by simp [EthCryptographySpecs.Xmss.chain]
  | s + 1, h, v => by
    rw [EthCryptographySpecs.Xmss.chain, chain_eq pp epoch he i start s (by omega) v, List.range'_concat,
      List.foldl_append]
    have hi := i.isLt
    simp only [Constants.V, Constants.CHAIN_LENGTH, Constants.W] at hi h
    simp only [EthCryptographySpecs.Xmss.chainStep, packBytes_dig, tweakHash_eq, chainPosition, toNat_ofNat_lt _ he,
      List.foldl_cons,
      List.foldl_nil, Words.chainStep, Constants.CHAIN_LENGTH, Constants.W]
    rw [toNat_ofNat_lt _ (by omega)]
    have h1 : TweakType.chain.toByte.toNat = 1 := rfl
    simp only [h1, Nat.one_mul, show (2 : ℕ) ^ 3 = 8 from rfl]

theorem leafBytes (ds : List Dig) (a : List (BitVec 64)) :
    (ds.map dig).foldl (fun acc d => acc ++ packBytes d) (wordsBytes a) =
      wordsBytes (a ++ ds.flatMap fun d => [d.1, d.2]) := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.foldl_cons, packBytes_dig, wordsBytes_append, ih, List.flatMap_cons,
      List.append_assoc]

theorem leaf_eq (pp : Dig) (epoch : ℕ) (he : epoch < 2 ^ 32) (tips : Fin 42 → Dig)
    (x : Vector (Fin Constants.CHAIN_LENGTH) Constants.V) :
    otsLeaf (param pp) (UInt32.ofNat epoch)
        (otsRecover (param pp) (UInt32.ofNat epoch) (Vector.ofFn (n := Constants.V) fun i => dig (tips i)) x) =
      dig (Words.leaf epoch pp (List.ofFn fun i : Fin 42 =>
        Words.chainFrom i epoch pp ((x.toList.map Fin.val).getD i 0) (tips i))) := by
  have hl :
      (otsRecover (param pp) (UInt32.ofNat epoch) (Vector.ofFn (n := Constants.V) fun i => dig (tips i)) x).toList =
      (List.ofFn fun i : Fin 42 =>
        Words.chainFrom i epoch pp ((x.toList.map Fin.val).getD i 0) (tips i)).map dig := by
    apply List.ext_getElem
    · simp only [Vector.length_toList, List.length_map, List.length_ofFn]
      rfl
    · intro i h1 h2
      have hi : i < 42 := by simpa using h2
      simp only [otsRecover, Vector.getElem_toList, Fin.getElem_fin, Vector.getElem_ofFn, List.getElem_map,
        List.getElem_ofFn]
      rw [chain_eq pp epoch he]
      have hiV : i < Constants.V := hi
      have hg : (x.toList.map Fin.val).getD i 0 = (x[i]'hiV).val := by
        simp [List.getD_eq_getElem?_getD, hiV]
      rw [hg]
      simp only [Words.chainFrom, Constants.CHAIN_LENGTH, Constants.W]
      rfl
  have h2 : TweakType.leaf.toByte.toNat = 2 := rfl
  have h0 : (0 : UInt32).toNat = 0 := rfl
  unfold otsLeaf
  rw [hl, ← wordsBytes_nil, leafBytes, List.nil_append, tweakHash_eq, toNat_ofNat_lt _ he, h2, h0, Words.leaf]

theorem testBit_eq (e l : ℕ) : e.testBit l = !((e >>> l) % 2 == 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ l) with h | h <;> simp [h]

theorem climbUpto_eq (pp : Dig) (epoch : ℕ) (he : epoch < 2 ^ 32) (path : Fin 32 → Dig) (leaf : Dig) :
    ∀ (k : ℕ) (hk : k ≤ Constants.LOG_LIFETIME),
      Internal.climbUpto (param pp) epoch (Vector.ofFn (n := Constants.LOG_LIFETIME) fun l => dig (path l)) k hk
          (dig leaf) =
        dig ((List.range' 0 k).foldl
          (fun cur l => if h : l < 32 then Words.parent epoch l pp cur (path ⟨l, h⟩) else cur) leaf)
  | 0, hk => by simp [Internal.climbUpto]
  | l + 1, hk => by
    have hl : l < 32 := by simp only [Constants.LOG_LIFETIME] at hk; omega
    rw [Internal.climbUpto, climbUpto_eq pp epoch he path leaf l (by omega), List.range'_concat, List.foldl_append]
    simp only [Internal.climbStep, merkleNode, packBytes_dig, wordsBytes_append, tweakHash_eq, Vector.getElem_ofFn,
      List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul, dif_pos hl]
    rw [Words.parent, testBit_eq]
    have h1 : (UInt32.ofNat (l + 1)).toNat = l + 1 := toNat_ofNat_lt _ (by omega)
    have h2 : (UInt32.ofNat (epoch >>> (l + 1))).toNat = epoch / 2 ^ (l + 1) := by
      rw [Nat.shiftRight_eq_div_pow, toNat_ofNat_lt _ (lt_of_le_of_lt (Nat.div_le_self _ _) he)]
    have h3 : TweakType.merkle.toByte.toNat = 3 := rfl
    rw [h1, h2, h3]
    cases hb : ((epoch >>> l) % 2 == 0) <;>
      simp only [Bool.not_true, Bool.not_false, if_true, if_false, Bool.false_eq_true, List.cons_append,
        List.nil_append] <;> rfl

theorem computeRoot_eq (pp : Dig) (epoch : ℕ) (he : epoch < 2 ^ 32) (path : Fin 32 → Dig) (leaf : Dig) :
    computeRoot (param pp) (UInt32.ofNat epoch) (Vector.ofFn (n := Constants.LOG_LIFETIME) fun l => dig (path l))
        (dig leaf) =
      dig (Words.climb epoch pp path leaf) := by
  simp only [computeRoot, toNat_ofNat_lt _ he]
  rw [climbUpto_eq pp epoch he path leaf]
  simp only [Words.climb, foldl_finRange, Constants.LOG_LIFETIME]

theorem dig_get (D : Dig) (k : ℕ) (hk : k < 16) :
    (dig D)[k]'(by simp only [Constants.DIGEST_LEN]; omega) = byteOf (if k < 8 then D.1 else D.2) (k % 8) := by
  simp only [dig, wordsVec, Vector.getElem_ofFn, byteAt, wordAt, List.getD_eq_getElem?_getD]
  by_cases h : k < 8
  · simp [h, Nat.div_eq_of_lt h]
  · simp [h, show k / 8 = 1 by omega]

theorem dig_inj (a b : Dig) (h : dig a = dig b) : a = b := by
  have e : ∀ k (hk : k < 16), byteOf (if k < 8 then a.1 else a.2) (k % 8) =
      byteOf (if k < 8 then b.1 else b.2) (k % 8) := by
    intro k hk
    rw [← dig_get a k hk, ← dig_get b k hk]
    simp only [h]
  apply Prod.ext
  · apply byteOf_ext
    intro k hk
    have := e k (by omega)
    simpa [show k < 8 by omega, Nat.mod_eq_of_lt (show k < 8 by omega)] using this
  · apply byteOf_ext
    intro k hk
    have := e (k + 8) (by omega)
    simpa [show (k + 8) % 8 = k by omega] using this

theorem beq_dig (a b : Dig) : (a == b) = decide (dig a = dig b) := by
  by_cases h : a = b
  · subst h
    simp
  · have : ¬ dig a = dig b := fun e => h (dig_inj _ _ e)
    rw [decide_eq_false this]
    simpa using h

/-- The main bridge: verification over words is the specification's verification on the bytes of those words. -/
theorem verify_eq (pp root : Dig) (msg : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (epoch : ℕ) (sig : Sig)
    (he : epoch < 2 ^ 32) :
    Words.verify pp root msg epoch sig =
      EthCryptographySpecs.Xmss.verify (pk pp root) (message msg) (signature sig) (UInt32.ofNat epoch) := by
  have e1 : (pk pp root).publicParam = param pp := rfl
  have e2 : (pk pp root).merkleRoot = dig root := rfl
  have e3 : (signature sig).randomness = randomness sig.rho := rfl
  have e4 : (signature sig).chainElements = Vector.ofFn (n := Constants.V) fun i => dig (sig.tips i) := rfl
  have e5 : (signature sig).merklePath = Vector.ofFn (n := Constants.LOG_LIFETIME) fun l => dig (sig.path l) := rfl
  rw [EthCryptographySpecs.Xmss.verify, Words.verify, e1, e2, e3, e4, e5, ← wotsEncode_eq pp msg sig.rho epoch he]
  rcases wotsEncode (param pp) (message msg) (randomness sig.rho) (UInt32.ofNat epoch) with _ | x
  · rfl
  · rw [Option.map_some, Option.elim_some]
    dsimp only
    rw [leaf_eq pp epoch he sig.tips x, computeRoot_eq pp epoch he, beq_dig]


/-! ## Decoding is onto -/

/-- Word `i` of a byte vector: its bytes `8i` to `8i + 7`, little endian, zero past its end. -/
def vword {n : ℕ} (v : Vector UInt8 n) (i : ℕ) : BitVec 64 := (or64 fun t => v.toArray.getD (8 * i + t) 0).toBitVec

theorem wordsVec_vword (n m : ℕ) (hn : n = 8 * m) (v : Vector UInt8 n) :
    wordsVec n ((List.range m).map (vword v)) = v := by
  apply Vector.ext
  intro k hk
  have hm : k / 8 < m := by omega
  simp only [wordsVec, Vector.getElem_ofFn, byteAt, wordAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hm, Option.map_some, Option.getD_some, vword]
  rw [byteOf_or64 _ _ (by omega)]
  simp [show 8 * (k / 8) + k % 8 = k by omega, hk]

theorem dig_onto (d : Digest) : dig (vword d 0, vword d 1) = d := wordsVec_vword _ 2 rfl d

theorem param_onto (d : PublicParam) : param (vword d 0, vword d 1) = d := wordsVec_vword _ 2 rfl d

theorem randomness_onto (r : Randomness) : randomness (vword r 0, vword r 1, vword r 2) = r :=
  wordsVec_vword _ 3 rfl r

/-- Every specification message is the bytes of four words. -/
theorem message_onto (m : Message) : ∃ msg, message msg = m :=
  ⟨(vword m 0, vword m 1, vword m 2, vword m 3), wordsVec_vword _ 4 rfl m⟩

/-- Every specification public key is the bytes of a parameter's and a root's words. -/
theorem publicKey_onto (p : PublicKey) : ∃ pp root, pk pp root = p := by
  obtain ⟨r, q⟩ := p
  exact ⟨(vword q 0, vword q 1), (vword r 0, vword r 1), by simp only [pk, dig_onto, param_onto]⟩

/-- Every specification signature is the bytes of a signature's words. -/
theorem signature_onto (s : Signature) : ∃ sig : Sig, signature sig = s := by
  obtain ⟨ce, r, mp⟩ := s
  refine ⟨⟨fun i => (vword (ce[i.val]'i.isLt) 0, vword (ce[i.val]'i.isLt) 1), (vword r 0, vword r 1, vword r 2),
    fun l => (vword (mp[l.val]'l.isLt) 0, vword (mp[l.val]'l.isLt) 1)⟩, ?_⟩
  simp only [signature, Signature.mk.injEq, randomness_onto, true_and]
  constructor
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, dig_onto]
    rfl
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, dig_onto]
    rfl

/-- Every specification epoch is the `UInt32.ofNat` of a number below `2 ^ 32`. -/
theorem epoch_onto (e : Epoch) : ∃ n < 2 ^ 32, UInt32.ofNat n = e :=
  ⟨e.toNat, e.toNat_lt, UInt32.ofNat_toNat⟩

end LeanVMCircuits.Xmss.Spec
