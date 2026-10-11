import LeanSphincs
import LeanVMCircuits.Sphincs.Words
import LeanVMCircuits.Xmss.Spec

/-!
# leanSPHINCS verification over words is the specification's

`Sphincs.Words.verify` of a root, a public parameter, a message and a signature, all words, is the specification's
`LeanSphincs.verify` on their little-endian bytes (`verify_eq`), when the signature's counters are below `2 ^ 32` (the
specification serializes each in 4 bytes; a word verification accepts only such counters, `counters_lt`). Every hash
but the encoding is `th_eq`: the specification's tweak is the words of `Sphincs.Words.tweak` (`tweak_bytes`), and its
BLAKE2s is `hashWords` (`Xmss.Blake2s`). The encoding hashes 52 bytes in one block (`hash_short`, `encDigest_eq`).
The message digest reads the same bits of the same number (`messageDigest_eq`), the encoding the same digits and top
bits (`encode_eq`), the chains and leaves the same payloads, and the trees climb on the same bits (`fold_eq`).
Decoding words to bytes is onto (`signature_onto`, `publicKey_onto`, `message_onto`), so the bridge covers every
specification input.

This file imports the specification, so it is not a module.
-/

namespace LeanVMCircuits.Sphincs.Spec

open EthCryptographySpecs.Xmss (packBytes)
open LeanVMCircuits.Rec
open LeanVMCircuits.Xmss.Spec (byteOf byteAt wordsBytes wordsVec or64 byteOf_toNat wordsBytes_getD enc
  compress_enc blockWords_eq stateBytes_eq packBytes_wordsVec wordsBytes_append wordsBytes_nil wordBytes_eq
  top_bit foldl_val toNat_ofNat_lt testBit_eq vword wordsVec_vword byteOf_or64 byteOf_ext)
open LeanVMCircuits.Xmss.Words (W Dig)
open LeanVMCircuits.Sphincs.Words (Sig)

/-! ## Decoding words to bytes -/

/-- A digest from its two words. -/
def dig (d : Dig) : LeanSphincs.Digest := wordsVec _ [d.1, d.2]

/-- A public parameter from its two words. -/
def param (d : Dig) : LeanSphincs.PublicParam := wordsVec _ [d.1, d.2]

/-- A randomizer from its two words. -/
def randomizer (d : Dig) : LeanSphincs.Randomizer := wordsVec _ [d.1, d.2]

/-- A message from its four words. -/
def message (m : W × W × W × W) : LeanSphincs.Message := wordsVec _ [m.1, m.2.1, m.2.2.1, m.2.2.2]

/-- A counter from its word: the word's first four bytes. -/
def counter (c : W) : LeanSphincs.Counter := wordsVec _ [c]

/-- A public key from its root's and its parameter's words. -/
def pk (root pp : Dig) : LeanSphincs.PublicKey := ⟨dig root, param pp⟩

/-- A few-time tree's number. -/
def f14 (κ : Fin LeanSphincs.Constants.FTS_TREES) : Fin 14 :=
  ⟨κ.val, by have := κ.isLt; simp only [LeanSphincs.Constants.FTS_TREES, LeanSphincs.Constants.K] at this; omega⟩

/-- A few-time tree's level. -/
def f10 (l : Fin LeanSphincs.Constants.A) : Fin 10 :=
  ⟨l.val, by have := l.isLt; simp only [LeanSphincs.Constants.A] at this; omega⟩

/-- A chain's number. -/
def f42 (i : Fin LeanSphincs.Constants.V) : Fin 42 :=
  ⟨i.val, by have := i.isLt; simp only [LeanSphincs.Constants.V] at this; omega⟩

/-- Layer `lay` of a signature from its words. -/
def layerSig (sig : Sig) (lay : Fin 3) (h : ℕ) (hh : h = Sphincs.Words.height lay) : LeanSphincs.LayerSignature h :=
  ⟨counter (sig.counters lay), Vector.ofFn fun i => dig (sig.tips lay (f42 i)),
    Vector.ofFn fun l => dig (sig.paths lay ⟨l.val, hh ▸ l.isLt⟩)⟩

/-- A signature from its words. -/
def signature (sig : Sig) : LeanSphincs.Signature :=
  ⟨randomizer sig.rho, Vector.ofFn fun κ => ⟨dig (sig.secrets (f14 κ)),
    Vector.ofFn fun l => dig (sig.ftsPaths (f14 κ) (f10 l))⟩,
    layerSig sig 0 _ rfl, layerSig sig 1 _ rfl, layerSig sig 2 _ rfl⟩

theorem packBytes_dig (d : Dig) : packBytes (dig d) = wordsBytes [d.1, d.2] := packBytes_wordsVec _ _ rfl
theorem packBytes_param (d : Dig) : packBytes (param d) = wordsBytes [d.1, d.2] := packBytes_wordsVec _ _ rfl
theorem packBytes_randomizer (d : Dig) : packBytes (randomizer d) = wordsBytes [d.1, d.2] :=
  packBytes_wordsVec _ _ rfl
theorem packBytes_message (m : W × W × W × W) :
    packBytes (message m) = wordsBytes [m.1, m.2.1, m.2.2.1, m.2.2.2] := packBytes_wordsVec _ _ rfl

/-! ## The tweak and the tweakable hash -/

theorem tweak_bytes (t : LeanSphincs.TweakType) (lay : ℕ) (hlay : lay < 256) (tau p j : UInt32) :
    packBytes (LeanSphincs.tweak t lay tau p j) =
      wordsBytes [(Sphincs.Words.tweak t.toByte.toNat lay tau.toNat p.toNat j.toNat).1,
        (Sphincs.Words.tweak t.toByte.toNat lay tau.toNat p.toNat j.toNat).2] := by
  apply ByteArray.ext
  apply Array.ext
  · simp [packBytes, wordsBytes]; rfl
  · intro k h1 h2
    have hk : k < 16 := by simpa [wordsBytes] using h2
    have hty := t.toByte.toNat_lt
    have hs := p.toNat_lt
    have ht := tau.toNat_lt
    have hj := j.toNat_lt
    simp only [packBytes, LeanSphincs.tweak, wordBytes_eq, Vector.toArray_append, Vector.toArray_ofFn, wordsBytes,
      Array.getElem_ofFn]
    apply UInt8.toNat_inj.mp
    simp only [byteAt]
    rw [byteOf_toNat]
    interval_cases k <;>
      simp [byteOf_toNat, wordAt, Sphincs.Words.tweak, Sphincs.Circuit.tweak0,
        LeanSphincs.PROTOCOL_DOMAIN_SEP] <;> omega

/-- The first 16 bytes of the bytes of a digest's words are the bytes of its first two words. -/
theorem take_digest (D : Fin 4 → BitVec 64) :
    (wordsVec 32 (List.ofFn D)).take LeanSphincs.Constants.DIGEST_LEN = dig (D 0, D 1) := by
  apply Vector.toArray_inj.mp
  apply Array.ext
  · simp [dig, wordsVec, LeanSphincs.Constants.DIGEST_LEN]
  · intro k h1 h2
    have hk : k < 16 := by simpa [dig, wordsVec, LeanSphincs.Constants.DIGEST_LEN] using h2
    simp [dig, wordsVec, byteAt, wordAt, List.getD_eq_getElem?_getD]
    rcases (by omega : k / 8 = 0 ∨ k / 8 = 1) with e | e <;> simp [e]

/-- The specification's tweakable hash of whole words is `Sphincs.Words.th`. -/
theorem th_eq (tw : LeanSphincs.Tweak) (tws : W × W) (htw : packBytes tw = wordsBytes [tws.1, tws.2]) (pp : Dig)
    (pl : List W) : LeanSphincs.th (param pp) tw (wordsBytes pl) = dig (Sphincs.Words.th tws pp pl) := by
  simp only [LeanSphincs.th, htw, packBytes_param, wordsBytes_append, LeanVMCircuits.Xmss.Spec.hash_wordsBytes,
    Sphincs.Words.th, List.cons_append, List.nil_append]
  exact take_digest _

/-! ## BLAKE2s of one short block -/

/-- The specification's BLAKE2s of at most 64 bytes, the bytes of words read up to their end: one compression at
the byte count. -/
theorem hash_short (b : ByteArray) (ws : List W) (h1 : 0 < b.size) (h2 : b.size ≤ 64)
    (hb : ∀ k, b.data.getD k 0 = byteAt ws k) :
    EthCryptographySpecs.Xmss.Blake2s.hash b =
      wordsVec 32 (List.ofFn (digest (blake2s256 (BitVec.ofNat 64 b.size) (block ws 0) []))) := by
  have hN : EthCryptographySpecs.Xmss.Blake2s.Internal.blockCount b.size = 1 := by
    simp only [EthCryptographySpecs.Xmss.Blake2s.Internal.blockCount]; omega
  have hinit : (spec_private% EthCryptographySpecs.Xmss.Blake2s.IV).set! 0
      ((spec_private% EthCryptographySpecs.Xmss.Blake2s.IV)[0]! ^^^ 16842784) = enc paramIV := by
    decide +kernel
  have hs : ∀ n, [:n].size = n := by intro n; simp [Std.Legacy.Range.size]
  have hbw : (spec_private% EthCryptographySpecs.Xmss.Blake2s.blockWords) b
      (EthCryptographySpecs.Xmss.Blake2s.Internal.blockOffset 0) = enc (block ws 0) := by
    rw [← blockWords_eq ws 0]
    delta_private blockWords
    simp only [EthCryptographySpecs.Xmss.Blake2s.Internal.little32, hb, wordsBytes_getD]
  simp only [EthCryptographySpecs.Xmss.Blake2s.hash]
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, pure_bind, hN, hinit,
    hs, List.range'_one, List.foldl_cons, List.foldl_nil]
  rw [hbw, compress_enc, UInt64.toBitVec_ofNat', stateBytes_eq]
  have hc : EthCryptographySpecs.Xmss.Blake2s.Internal.blockCounter b.size 0 = b.size := by
    simp only [EthCryptographySpecs.Xmss.Blake2s.Internal.blockCounter,
      EthCryptographySpecs.Xmss.Blake2s.Internal.blockOffset, EthCryptographySpecs.Xmss.Blake2s.Internal.bytesInBlock]
    omega
  rw [hc]
  rfl

/-- The bytes the encoding hashes: a tweak's, the parameter's and the message's words, then a counter's four
bytes, are the bytes of seven words read up to their end, the counter below `2 ^ 32`. -/
theorem enc_getD (ws : List W) (hws : ws.length = 6) (c : W) (hc : c.toNat < 2 ^ 32) (k : ℕ) :
    (wordsBytes ws ++ packBytes (counter c)).data.getD k 0 = byteAt (ws ++ [c]) k := by
  rw [ByteArray.data_append, Array.getD_eq_getD_getElem?]
  have hsz : (wordsBytes ws).data.size = 48 := by
    have := LeanVMCircuits.Xmss.Spec.wordsBytes_size ws
    simp only [ByteArray.size] at this
    omega
  by_cases hk : k < 48
  · rw [Array.getElem?_append_left (by omega), ← Array.getD_eq_getD_getElem?, wordsBytes_getD]
    simp only [byteAt, wordAt, List.getD_eq_getElem?_getD, List.getElem?_append_left (show k / 8 < ws.length by omega)]
  · rw [Array.getElem?_append_right (by omega), hsz]
    simp only [byteAt, wordAt, List.getD_eq_getElem?_getD]
    by_cases hk2 : k < 52
    · have hk8 : k / 8 = 6 := by omega
      rw [List.getElem?_append_right (by omega), hws, hk8]
      have h4 : k - 48 < LeanSphincs.Constants.COUNTER_LEN := by
        simp only [LeanSphincs.Constants.COUNTER_LEN]; omega
      simp [packBytes, counter, wordsVec, h4, byteAt, wordAt,
        show (k - 48) / 8 = 0 by omega, show (k - 48) % 8 = k % 8 by omega]
    · have hnone : (packBytes (counter c)).data[k - 48]? = none := by
        simp [packBytes, counter, wordsVec, LeanSphincs.Constants.COUNTER_LEN]; omega
      rw [hnone, Option.getD_none]
      apply UInt8.toNat_inj.mp
      rw [byteOf_toNat]
      by_cases hk3 : k < 56
      · rw [List.getElem?_append_right (by omega), hws, show k / 8 - 6 = 0 by omega]
        simp only [List.getElem?_cons_zero, Option.getD_some, UInt8.toNat_zero]
        have h8 : 2 ^ 32 ≤ 2 ^ (8 * (k % 8)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.div_eq_of_lt (lt_of_lt_of_le hc h8)]
      · rw [List.getElem?_eq_none (by simp [hws]; omega)]
        simp

/-- The encoding's hash: the first two words of BLAKE2s of the 52 bytes of a tweak, the parameter, the message and
the counter. -/
theorem encDigest_eq (tw : LeanSphincs.Tweak) (tws : W × W) (htw : packBytes tw = wordsBytes [tws.1, tws.2])
    (pp M : Dig) (c : W) (hc : c.toNat < 2 ^ 32) :
    LeanSphincs.th (param pp) tw (packBytes (dig M) ++ packBytes (counter c)) =
      dig (Sphincs.Words.encDigest tws pp M c) := by
  have hb : packBytes tw ++ packBytes (param pp) ++ (packBytes (dig M) ++ packBytes (counter c)) =
      wordsBytes [tws.1, tws.2, pp.1, pp.2, M.1, M.2] ++ packBytes (counter c) := by
    rw [htw, packBytes_param, packBytes_dig, ← ByteArray.append_assoc, wordsBytes_append, wordsBytes_append]
    rfl
  have hsize : (wordsBytes [tws.1, tws.2, pp.1, pp.2, M.1, M.2] ++ packBytes (counter c)).size = 52 := by
    have hc4 : (packBytes (counter c)).size = 4 := by
      simp only [packBytes, ByteArray.size, Vector.size_toArray, LeanSphincs.Constants.COUNTER_LEN]
    rw [ByteArray.size_append, LeanVMCircuits.Xmss.Spec.wordsBytes_size, hc4]
    rfl
  unfold LeanSphincs.th
  rw [hb, hash_short _ [tws.1, tws.2, pp.1, pp.2, M.1, M.2, c] (by omega) (by omega)
    (enc_getD _ rfl c hc), hsize, take_digest]
  rfl

/-! ## The message digest -/

theorem testBit_littleEndian (L : List UInt8) (j : ℕ) :
    (LeanSphincs.littleEndian L).testBit j = (L.getD (j / 8) 0).toNat.testBit (j % 8) := by
  induction L generalizing j with
  | nil => simp [LeanSphincs.littleEndian]
  | cons b L ih =>
    have hb : b.toNat < 2 ^ 8 := b.toNat_lt
    have hl : LeanSphincs.littleEndian (b :: L) = 2 ^ 8 * LeanSphincs.littleEndian L + b.toNat := by
      simp only [LeanSphincs.littleEndian, List.foldr_cons]; ring
    rw [hl, Nat.testBit_two_pow_mul_add _ hb]
    by_cases hj : j < 8
    · rw [if_pos hj, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
      rfl
    · rw [if_neg hj, ih, show j / 8 = (j - 8) / 8 + 1 by omega, show (j - 8) % 8 = j % 8 by omega]
      rfl

theorem testBit_byteOf (w : W) (r i : ℕ) (hi : i < 8) : (byteOf w r).toNat.testBit i = w.toNat.testBit (8 * r + i) := by
  rw [byteOf_toNat, show (256 : ℕ) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_div_two_pow, Nat.add_comm]

/-- The bits of three words as one number. -/
theorem testBit_value (D : Fin 4 → W) (j : ℕ) (hj : j < 192) :
    ((D 0).toNat + 2 ^ 64 * (D 1).toNat + 2 ^ 128 * (D 2).toNat).testBit j =
      (D ⟨j / 64, by omega⟩).toNat.testBit (j % 64) := by
  rw [show (D 0).toNat + 2 ^ 64 * (D 1).toNat + 2 ^ 128 * (D 2).toNat =
      2 ^ 64 * (2 ^ 64 * (D 2).toNat + (D 1).toNat) + (D 0).toNat by ring,
    Nat.testBit_two_pow_mul_add _ (D 0).isLt]
  by_cases h0 : j < 64
  · rw [if_pos h0]
    have : (⟨j / 64, by omega⟩ : Fin 4) = 0 := Fin.ext (by simp; omega)
    rw [this, Nat.mod_eq_of_lt h0]
  · rw [if_neg h0, Nat.testBit_two_pow_mul_add _ (D 1).isLt]
    by_cases h1 : j - 64 < 64
    · rw [if_pos h1]
      have : (⟨j / 64, by omega⟩ : Fin 4) = 1 := Fin.ext (by simp; omega)
      rw [this, show (j - 64) = j % 64 by omega]
    · rw [if_neg h1]
      have : (⟨j / 64, by omega⟩ : Fin 4) = 2 := Fin.ext (by simp; omega)
      rw [this, show j - 64 - 64 = j % 64 by omega]

/-- The specification reads bits `o .. o + l` of the digest's bytes as the words' number. -/
theorem bits_digest (D : Fin 4 → W) (o l : ℕ) (hol : o + l ≤ 192) :
    LeanSphincs.littleEndian (wordsVec 32 (List.ofFn D)).toList / 2 ^ o % 2 ^ l =
      ((D 0).toNat + 2 ^ 64 * (D 1).toNat + 2 ^ 128 * (D 2).toNat) / 2 ^ o % 2 ^ l := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < l
  · simp only [decide_eq_true hi, Bool.true_and]
    rw [testBit_littleEndian, testBit_value D _ (by omega)]
    have hq : (i + o) / 8 < 32 := by omega
    rw [show (wordsVec 32 (List.ofFn D)).toList.getD ((i + o) / 8) 0 = byteAt (List.ofFn D) ((i + o) / 8) by
        simp [wordsVec, List.getD_eq_getElem?_getD, hq],
      byteAt, testBit_byteOf _ _ _ (by omega)]
    have hw : wordAt (List.ofFn D) ((i + o) / 8 / 8) = D ⟨(i + o) / 64, by omega⟩ := by
      rw [wordAt, List.getD_eq_getElem?_getD, List.getElem?_ofFn, Nat.div_div_eq_div_mul,
        dif_pos (show (i + o) / (8 * 8) < 4 by omega)]
      rfl
    rw [hw, show 8 * ((i + o) / 8 % 8) + (i + o) % 8 = (i + o) % 64 by omega]
  · simp [decide_eq_false hi]

theorem msg_bytes (pp root rho : Dig) (msg : W × W × W × W) :
    packBytes (LeanSphincs.tweak .msg 0 0 0 0) ++ packBytes (param pp) ++ packBytes (randomizer rho) ++
        packBytes (dig root) ++ packBytes (message msg) =
      wordsBytes [(Sphincs.Words.tweak 12 0 0 0 0).1, (Sphincs.Words.tweak 12 0 0 0 0).2, pp.1, pp.2, rho.1, rho.2,
        root.1, root.2, msg.1, msg.2.1, msg.2.2.1, msg.2.2.2] := by
  rw [tweak_bytes _ _ (by norm_num), packBytes_param, packBytes_randomizer, packBytes_dig, packBytes_message,
    wordsBytes_append, wordsBytes_append, wordsBytes_append, wordsBytes_append]
  rfl

/-- The specification's message digest is the words' index and leaf indices. -/
theorem messageDigest_eq (pp root rho : Dig) (msg : W × W × W × W) :
    LeanSphincs.messageDigest (param pp) (dig root) (randomizer rho) (message msg) =
      ((Sphincs.Words.messageDigest pp root rho msg).1,
        Vector.ofFn fun κ : Fin LeanSphincs.Constants.K => (Sphincs.Words.messageDigest pp root rho msg).2 κ) := by
  unfold LeanSphincs.messageDigest Sphincs.Words.messageDigest
  simp only [msg_bytes, LeanVMCircuits.Xmss.Spec.hash_wordsBytes]
  apply Prod.ext
  · simp only
    rw [bits_digest _ 0 _ (by simp [LeanSphincs.Constants.H])]
    simp [LeanSphincs.Constants.H]
  · apply Vector.ext
    intro κ hκ
    simp only [Vector.getElem_ofFn]
    rw [bits_digest _ _ _ (by simp only [LeanSphincs.Constants.H, LeanSphincs.Constants.A,
      LeanSphincs.Constants.K] at hκ ⊢; omega)]
    simp only [LeanSphincs.Constants.H, LeanSphincs.Constants.A, Nat.mul_comm κ 10]

/-! ## The encoding -/

theorem foldr_shift (l : List ℕ) (g : ℕ → UInt8) :
    (l.foldr (fun k (acc : UInt64) => acc <<< 8 ||| (g k).toUInt64) 0).toNat =
      (l.foldr (fun k acc => (g k).toNat + 256 * acc) 0) % 2 ^ 64 := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldr_cons, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, ih]
    generalize l.foldr (fun k acc => (g k).toNat + 256 * acc) 0 = N
    have hb : (g k).toNat < 2 ^ 8 := (g k).toNat_lt
    generalize (g k).toNat = b at hb ⊢
    have h8 : (8 : UInt64).toNat % 64 = 8 := rfl
    rw [h8]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow, show b + 256 * N = 2 ^ 8 * N + b by ring, Nat.testBit_two_pow_mul_add _ hb]
    by_cases hi : i < 8
    · have : b.testBit i = b.testBit i := rfl
      simp [hi, show ¬ (8 ≤ i) by omega, show i < 64 by omega]
    · rw [if_neg hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      by_cases h64 : i < 64
      · simp [h64, show 8 ≤ i by omega, show i - 8 < 64 by omega]
      · simp [h64]

theorem littleEndian_bytes (w : W) :
    LeanSphincs.littleEndian ((List.range 8).map fun k => byteOf w k) = w.toNat := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_littleEndian]
  by_cases hj : j < 64
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j / 8 < 8 by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [testBit_byteOf _ _ _ (by omega), show 8 * (j / 8) + j % 8 = j by omega]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp

/-- The specification reads digest half `h` as the word `h` of the pair. -/
theorem digestWord_dig (D : Dig) (h : Fin 2) :
    LeanSphincs.Ots.digestWord (dig D) h = UInt64.ofBitVec (if h.val = 0 then D.1 else D.2) := by
  apply UInt64.toNat_inj.mp
  rw [LeanSphincs.Ots.digestWord, foldr_shift, ← List.foldr_map (f := fun k => ((dig D)[8 * h.val + k]?.getD 0))
    (g := fun b acc => b.toNat + 256 * acc)]
  have hb : (List.range 8).map (fun k => (dig D)[8 * h.val + k]?.getD 0) =
      (List.range 8).map fun k => byteOf (if h.val = 0 then D.1 else D.2) k := by
    apply List.map_congr_left
    intro k hk
    have hk8 : k < 8 := List.mem_range.mp hk
    have hh := h.isLt
    rw [Vector.getElem?_eq_getElem (show 8 * h.val + k < LeanSphincs.Constants.DIGEST_LEN by
      simp only [LeanSphincs.Constants.DIGEST_LEN]; omega), Option.getD_some]
    simp only [dig, wordsVec, Vector.getElem_ofFn, byteAt, wordAt, List.getD_eq_getElem?_getD]
    rcases (by omega : h.val = 0 ∨ h.val = 1) with e | e
    · simp [e, show k / 8 = 0 by omega, Nat.mod_eq_of_lt hk8]
    · simp [e, show (8 + k) / 8 = 1 by omega, show (8 + k) % 8 = k by omega]
  rw [hb]
  have hl : (List.range 8).foldr (fun b acc => (byteOf (if h.val = 0 then D.1 else D.2) b).toNat + 256 * acc) 0 =
      LeanSphincs.littleEndian ((List.range 8).map fun k => byteOf (if h.val = 0 then D.1 else D.2) k) := by
    simp only [LeanSphincs.littleEndian, List.foldr_map]
  rw [List.foldr_map, hl, littleEndian_bytes, Nat.mod_eq_of_lt (BitVec.isLt _)]
  rfl

theorem digit_eq (w : W) (r : ℕ) (hr : r < 21) :
    ((UInt64.ofBitVec w >>> UInt64.ofNat (LeanSphincs.Constants.W * r)).toNat % LeanSphincs.Constants.CHAIN_LEN) =
      Xmss.Words.digit w r := by
  have h3 : (UInt64.ofNat (3 * r)).toNat % 64 = 3 * r := by
    simp [UInt64.toNat_ofNat]
  simp only [Xmss.Words.digit, LeanSphincs.Constants.CHAIN_LEN, LeanSphincs.Constants.W, UInt64.toNat_shiftRight]
  rw [h3, Nat.shiftRight_eq_div_pow]
  rfl

theorem digits_eq (D : Dig) : (LeanSphincs.Ots.digits (dig D)).toList.map Fin.val = Xmss.Words.digits D := by
  apply List.ext_getElem
  · simp only [List.length_map, Vector.length_toList, Xmss.Words.digits, List.length_range]
    rfl
  · intro i h1 h2
    have hi : i < 42 := by simpa [Xmss.Words.digits] using h2
    simp only [List.getElem_map, Vector.getElem_toList, LeanSphincs.Ots.digits, Vector.getElem_ofFn,
      Xmss.Words.digits, List.getElem_range, digestWord_dig, LeanSphincs.Constants.V]
    rw [digit_eq _ _ (by omega)]
    by_cases hlt : i < 21
    · simp [hlt, show i / 21 = 0 by omega]
    · simp [hlt, show i / 21 ≠ 0 by omega]

theorem top_bits (D : Dig) :
    ((LeanSphincs.Ots.digestWord (dig D) 0 ||| LeanSphincs.Ots.digestWord (dig D) 1) >>> 63 != 0) =
      (D.1.getLsbD 63 || D.2.getLsbD 63) := by
  rw [digestWord_dig, digestWord_dig]
  have : (UInt64.ofBitVec D.1 ||| UInt64.ofBitVec D.2) = UInt64.ofBitVec (D.1 ||| D.2) := rfl
  simp only [Fin.isValue, Fin.val_zero, if_true, Fin.val_one, one_ne_zero, if_false, this]
  show (!(UInt64.ofBitVec (D.1 ||| D.2) >>> 63 == 0)) = _
  rw [top_bit, BitVec.getLsbD_or, Bool.not_not]

theorem foldl_val' {n : ℕ} (x : Vector (Fin n) LeanSphincs.Constants.V) :
    x.foldl (fun s c => s + c.val) 0 = (x.toList.map Fin.val).sum := by
  rw [← Vector.foldl_toList, foldl_val, Nat.zero_add]

/-- The specification's encoding is the words' encoding, as digit values, for a counter below `2 ^ 32`. -/
theorem encode_eq (pp M : Dig) (c : W) (hc : c.toNat < 2 ^ 32) (pos : LeanSphincs.Pos) (lay tau e : ℕ)
    (hpl : (pos.lay : ℕ) = lay) (hpt : pos.tau = UInt32.ofNat tau) (hpe : pos.e = UInt32.ofNat e)
    (htau : tau < 2 ^ 32) (he : e < 2 ^ 32) :
    (LeanSphincs.Ots.encode (param pp) pos (dig M) (counter c)).map
        (fun x => x.toList.map Fin.val) = Sphincs.Words.encode lay tau e pp M c := by
  have hl3 : (pos.lay : ℕ) < 256 := lt_of_lt_of_le pos.lay.isLt (by simp [LeanSphincs.Constants.D])
  have htw : packBytes (LeanSphincs.tweak .enc pos.lay pos.tau 0 pos.e) =
      wordsBytes [(Sphincs.Words.tweak 4 lay tau 0 e).1, (Sphincs.Words.tweak 4 lay tau 0 e).2] := by
    rw [tweak_bytes _ _ hl3, hpt, hpe, toNat_ofNat_lt _ htau, toNat_ofNat_lt _ he, hpl]
    rfl
  simp only [LeanSphincs.Ots.encode]
  rw [encDigest_eq _ _ htw pp M c hc]
  unfold Sphincs.Words.encode
  generalize Sphincs.Words.encDigest (Sphincs.Words.tweak 4 lay tau 0 e) pp M c = D
  rw [top_bits, foldl_val', digits_eq]
  by_cases h1 : D.1.getLsbD 63 = false <;> by_cases h2 : D.2.getLsbD 63 = false <;>
    by_cases h3 : (Xmss.Words.digits D).sum = 191 <;> simp_all [digits_eq, LeanSphincs.Constants.TARGET_SUM]

/-! ## Chains, leaves and trees -/

theorem foldl_dig {β : Type} (l : List β) (f : LeanSphincs.Digest → β → LeanSphincs.Digest) (g : Dig → β → Dig)
    (h : ∀ c b, b ∈ l → f (dig c) b = dig (g c b)) (x : Dig) : l.foldl f (dig x) = dig (l.foldl g x) := by
  induction l generalizing x with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldl_cons]
    rw [h x b (by simp), ih (fun c b' hb => h c b' (by simp [hb]))]

/-- The specification's chain walk is the words' chain. -/
theorem walk_eq (pp : Dig) (pos : LeanSphincs.Pos) (lay tau e : ℕ) (hpl : (pos.lay : ℕ) = lay)
    (hpt : pos.tau = UInt32.ofNat tau) (hpe : pos.e = UInt32.ofNat e) (htau : tau < 2 ^ 32) (he : e < 2 ^ 32)
    (i : Fin LeanSphincs.Constants.V) (start steps : ℕ) (hs : start + steps ≤ 8) (v : Dig) :
    LeanSphincs.Ots.walk (param pp) pos i start steps (dig v) =
      dig ((List.range' start steps).foldl (fun v s => Sphincs.Words.chainStep lay tau e i s pp v) v) := by
  unfold LeanSphincs.Ots.walk
  apply foldl_dig
  intro c s hsm
  have hs8 : s < 8 := by rw [List.mem_range'] at hsm; omega
  have hi := i.isLt
  simp only [LeanSphincs.Constants.V] at hi
  rw [packBytes_dig, th_eq _ (Sphincs.Words.tweak 1 lay tau (8 * i.val + s) e)]
  · rfl
  · have hp : LeanSphincs.Constants.CHAIN_LEN * i.val + s < 2 ^ 32 := by
      simp only [LeanSphincs.Constants.CHAIN_LEN, LeanSphincs.Constants.W]; omega
    have hl3 : (pos.lay : ℕ) < 256 := lt_of_lt_of_le pos.lay.isLt (by simp [LeanSphincs.Constants.D])
    rw [tweak_bytes _ _ hl3, hpt, hpe, toNat_ofNat_lt _ htau, toNat_ofNat_lt _ he, toNat_ofNat_lt _ hp, hpl]
    rfl

theorem concat_dig (ds : List Dig) :
    LeanSphincs.concatDigests (ds.map dig) = wordsBytes (ds.flatMap fun d => [d.1, d.2]) := by
  have : ∀ a, (ds.map dig).foldl (fun acc d => acc ++ packBytes d) (wordsBytes a) =
      wordsBytes (a ++ ds.flatMap fun d => [d.1, d.2]) := by
    induction ds with
    | nil => simp
    | cons d ds ih =>
      intro a
      simp only [List.map_cons, List.foldl_cons, packBytes_dig, wordsBytes_append, ih, List.flatMap_cons,
        List.append_assoc]
  have h := this []
  rw [wordsBytes_nil, List.nil_append] at h
  exact h

theorem zipIdx_ofFn {α : Type} (n : ℕ) (f : Fin n → α) :
    (List.ofFn f).zipIdx = (List.finRange n).map fun l => (f l, l.val) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zipIdx]

/-- The specification's tree fold is the words' climb. -/
theorem fold_eq (pp : Dig) (t : LeanSphincs.TweakType) (ty : ℕ) (hty : t.toByte.toNat = ty) (lay : ℕ)
    (hlay : lay < 256) (tau : ℕ) (htau : tau < 2 ^ 32) (e : ℕ) (he : e < 2 ^ 32) (h : ℕ) (hh : h < 2 ^ 31)
    (path : Fin h → Dig) (leaf : Dig) :
    LeanSphincs.fold (param pp) t lay (UInt32.ofNat tau) e (dig leaf) (List.ofFn fun l => dig (path l)) =
      dig (Sphincs.Words.climb ty lay tau e h pp path leaf) := by
  unfold LeanSphincs.fold Sphincs.Words.climb
  rw [zipIdx_ofFn, List.foldl_map]
  apply foldl_dig
  intro c l _
  have hl := l.isLt
  have htw : packBytes (LeanSphincs.tweak t lay (UInt32.ofNat tau) (UInt32.ofNat (l.val + 1))
      (UInt32.ofNat (e >>> (l.val + 1)))) =
      wordsBytes [(Sphincs.Words.tweak ty lay tau (l.val + 1) (e / 2 ^ (l.val + 1))).1,
        (Sphincs.Words.tweak ty lay tau (l.val + 1) (e / 2 ^ (l.val + 1))).2] := by
    rw [tweak_bytes _ _ hlay, toNat_ofNat_lt _ htau, toNat_ofNat_lt _ (by omega), Nat.shiftRight_eq_div_pow,
      toNat_ofNat_lt _ (lt_of_le_of_lt (Nat.div_le_self _ _) he), hty]
  simp only [LeanSphincs.nodeHash, packBytes_dig, wordsBytes_append, Sphincs.Words.parent, testBit_eq]
  cases hb : ((e >>> l.val) % 2 == 0)
  · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
    rw [th_eq _ _ htw]
    rfl
  · simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false]
    rw [th_eq _ _ htw]
    rfl

/-! ## A layer -/

theorem layer_signature (sig : Sig) (lay : Fin 3) :
    (signature sig).layer lay = (counter (sig.counters lay),
      Vector.ofFn (n := LeanSphincs.Constants.V) (fun i => dig (sig.tips lay (f42 i))),
      List.ofFn fun l => dig (sig.paths lay l)) := by
  fin_cases lay <;> rfl

theorem pos_of (idx : ℕ) (lay : Fin 3) :
    LeanSphincs.Pos.of idx lay = ⟨lay, UInt32.ofNat (Sphincs.Words.tau idx lay),
      UInt32.ofNat (Sphincs.Words.leafIndex idx lay)⟩ := by
  fin_cases lay <;>
    simp only [LeanSphincs.Pos.of, Sphincs.Words.tau, Sphincs.Words.leafIndex, Nat.shiftRight_eq_div_pow] <;> rfl

/-- The specification's layer step is the words' one, for a counter below `2 ^ 32`. -/
theorem layerRoot_eq (pp M : Dig) (idx : ℕ) (hidx : idx < 2 ^ 26) (sig : Sig) (lay : Fin 3)
    (hc : (sig.counters lay).toNat < 2 ^ 32) :
    LeanSphincs.layerRoot (param pp) idx (signature sig) (dig M) lay =
      (Sphincs.Words.layerRoot pp idx sig M lay).map dig := by
  have htau : Sphincs.Words.tau idx lay < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have he : Sphincs.Words.leafIndex idx lay < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.mod_le _ _) (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  have hh : Sphincs.Words.height lay < 2 ^ 31 := by fin_cases lay <;> decide
  have hpt : (LeanSphincs.Pos.of idx lay).tau = UInt32.ofNat (Sphincs.Words.tau idx lay) := by
    fin_cases lay <;> simp only [LeanSphincs.Pos.of, Sphincs.Words.tau, Nat.shiftRight_eq_div_pow] <;> rfl
  have hpe : (LeanSphincs.Pos.of idx lay).e = UInt32.ofNat (Sphincs.Words.leafIndex idx lay) := by
    fin_cases lay <;> simp only [LeanSphincs.Pos.of, Sphincs.Words.leafIndex, Nat.shiftRight_eq_div_pow] <;> rfl
  have hpl : ((LeanSphincs.Pos.of idx lay).lay : ℕ) = lay := rfl
  unfold LeanSphincs.layerRoot Sphincs.Words.layerRoot LeanSphincs.Ots.leaf
  rw [layer_signature]
  dsimp only
  rw [← encode_eq pp M _ hc (LeanSphincs.Pos.of idx lay) lay _ _ hpl hpt hpe htau he]
  rcases LeanSphincs.Ots.encode (param pp) (LeanSphincs.Pos.of idx lay) (dig M) (counter (sig.counters lay))
    with _ | x
  · rfl
  · simp only [Option.map_some]
    congr 1
    have hl : (List.ofFn fun i : Fin LeanSphincs.Constants.V =>
        LeanSphincs.Ots.walk (param pp) (LeanSphincs.Pos.of idx lay) i (x[i]).val
          (LeanSphincs.Constants.CHAIN_LEN - 1 - (x[i]).val)
          ((Vector.ofFn (n := LeanSphincs.Constants.V) fun i => dig (sig.tips lay (f42 i)))[i])) =
        (List.ofFn fun i : Fin 42 => Sphincs.Words.chainFrom lay (Sphincs.Words.tau idx lay)
          (Sphincs.Words.leafIndex idx lay) i pp ((x.toList.map Fin.val).getD i 0) (sig.tips lay i)).map dig := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_map]; rfl
      · intro i h1 h2
        have hi : i < 42 := by simpa using h2
        have hiV : i < LeanSphincs.Constants.V := hi
        simp only [List.getElem_ofFn, List.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
        have hx := (x[i]'hiV).isLt
        simp only [LeanSphincs.Constants.CHAIN_LEN, LeanSphincs.Constants.W] at hx
        have hst : (x[i]'hiV).val + (LeanSphincs.Constants.CHAIN_LEN - 1 - (x[i]'hiV).val) ≤ 8 := by
          simp only [LeanSphincs.Constants.CHAIN_LEN, LeanSphincs.Constants.W]; omega
        rw [walk_eq pp _ lay _ _ hpl hpt hpe htau he _ _ _ hst]
        have hg : (x.toList.map Fin.val).getD i 0 = (x[i]'hiV).val := by
          simp [List.getD_eq_getElem?_getD, hiV]
        rw [hg]
        simp only [Sphincs.Words.chainFrom, LeanSphincs.Constants.CHAIN_LEN, LeanSphincs.Constants.W, f42]
    have hleaf : ∀ ends : List Dig, LeanSphincs.Ots.leafHash (param pp) (LeanSphincs.Pos.of idx lay)
        (ends.map dig) = dig (Sphincs.Words.otsLeaf lay (Sphincs.Words.tau idx lay)
          (Sphincs.Words.leafIndex idx lay) pp ends) := by
      intro ends
      unfold LeanSphincs.Ots.leafHash Sphincs.Words.otsLeaf
      rw [concat_dig, th_eq _ (Sphincs.Words.tweak 2 lay (Sphincs.Words.tau idx lay) 0
        (Sphincs.Words.leafIndex idx lay))]
      have hl3 : ((LeanSphincs.Pos.of idx lay).lay : ℕ) < 256 :=
        lt_of_lt_of_le (LeanSphincs.Pos.of idx lay).lay.isLt (by simp [LeanSphincs.Constants.D])
      rw [tweak_bytes _ _ hl3, hpt, hpe, toNat_ofNat_lt _ htau, toNat_ofNat_lt _ he, hpl]
      rfl
    rw [hl, hleaf, hpt, hpe, toNat_ofNat_lt _ he]
    exact fold_eq pp .node 3 rfl lay (lt_of_lt_of_le lay.isLt (by norm_num)) _ htau _ he _ hh (sig.paths lay) _

/-! ## The few-time key -/

/-- The specification's few-time key is the words' one. -/
theorem recover_eq (pp : Dig) (idx : ℕ) (hidx : idx < 2 ^ 26) (u : ℕ → ℕ) (hu : ∀ κ, u κ < 2 ^ 10) (sig : Sig) :
    LeanSphincs.Fts.recover (param pp) idx (Vector.ofFn fun κ : Fin LeanSphincs.Constants.K => u κ)
        (signature sig).fts =
      dig (Sphincs.Words.th (Sphincs.Words.tweak 11 0 idx 0 0) pp
        ((List.ofFn fun κ : Fin 14 => Sphincs.Words.ftsRoot idx κ (u κ) pp (sig.secrets κ) (sig.ftsPaths κ)).flatMap
          fun d => [d.1, d.2])) := by
  have hpt : ∀ κ : Fin LeanSphincs.Constants.FTS_TREES,
      LeanSphincs.fold (param pp) .ftsNode κ (UInt32.ofNat idx) (u κ)
          (LeanSphincs.Fts.leaf (param pp) idx κ (u κ) (dig (sig.secrets (f14 κ))))
          (List.ofFn fun l => dig (sig.ftsPaths (f14 κ) (f10 l))) =
        dig (Sphincs.Words.ftsRoot idx κ (u κ) pp (sig.secrets (f14 κ)) (sig.ftsPaths (f14 κ))) := by
    intro κ
    have hκ : κ.val < 14 := (f14 κ).isLt
    have hleaf : LeanSphincs.Fts.leaf (param pp) idx κ (u κ) (dig (sig.secrets (f14 κ))) =
        dig (Sphincs.Words.th (Sphincs.Words.tweak 9 κ idx 0 (u κ)) pp
          [(sig.secrets (f14 κ)).1, (sig.secrets (f14 κ)).2]) := by
      unfold LeanSphincs.Fts.leaf
      rw [packBytes_dig, th_eq _ (Sphincs.Words.tweak 9 κ idx 0 (u κ))]
      rw [tweak_bytes _ _ (by omega), toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ (by have := hu κ; omega)]
      rfl
    rw [hleaf, fold_eq pp .ftsNode 10 rfl κ (by omega) idx (by omega) (u κ) (by have := hu κ; omega)
      LeanSphincs.Constants.A (by simp [LeanSphincs.Constants.A]) (fun l => sig.ftsPaths (f14 κ) (f10 l))]
    rfl
  have hroots : (List.ofFn fun κ : Fin LeanSphincs.Constants.FTS_TREES =>
      LeanSphincs.fold (param pp) .ftsNode κ (UInt32.ofNat idx) (u κ)
          (LeanSphincs.Fts.leaf (param pp) idx κ (u κ) (dig (sig.secrets (f14 κ))))
          (List.ofFn fun l => dig (sig.ftsPaths (f14 κ) (f10 l)))) =
      (List.ofFn fun κ : Fin LeanSphincs.Constants.FTS_TREES => Sphincs.Words.ftsRoot idx κ (u κ) pp
        (sig.secrets (f14 κ)) (sig.ftsPaths (f14 κ))).map dig := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext hpt)
  unfold LeanSphincs.Fts.recover LeanSphincs.Fts.key
  simp only [signature, Vector.getElem_ofFn, Fin.getElem_fin, Vector.toList_ofFn]
  rw [hroots, concat_dig, th_eq _ (Sphincs.Words.tweak 11 0 idx 0 0)]
  · rfl
  · rw [tweak_bytes _ _ (by norm_num), toNat_ofNat_lt _ (by omega)]
    rfl

/-! ## Verification -/

theorem dig_inj (a b : Dig) (h : dig a = dig b) : a = b := LeanVMCircuits.Xmss.Spec.dig_inj a b h

theorem beq_dig (a b : Dig) : (dig a == dig b) = (a == b) := by
  by_cases h : a = b
  · subst h
    simp
  · have : ¬ dig a = dig b := fun e => h (dig_inj _ _ e)
    simp [this, h]

/-- A layer as the specification numbers it. -/
def fin3D (a : Fin 3) : Fin LeanSphincs.Constants.D :=
  ⟨a.val, by simp [LeanSphincs.Constants.D]⟩

theorem foldlM_dig (l : List (Fin 3)) (f : LeanSphincs.Digest → Fin LeanSphincs.Constants.D → Option LeanSphincs.Digest)
    (g : Dig → Fin 3 → Option Dig) (h : ∀ y a, f (dig y) (fin3D a) = (g y a).map dig) (x : Dig) :
    (l.map fin3D).foldlM f (dig x) = (l.foldlM g x).map dig := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.foldlM_cons]
    rw [h x a]
    rcases g x a with _ | y
    · rfl
    · exact ih y

/-- Word verification after the message digest. -/
def wordsCore (root pp : Dig) (sig : Sig) (idx : ℕ) (u : ℕ → ℕ) : Bool :=
  if u 14 ≠ 0 then false
  else
    let roots := List.ofFn fun kappa : Fin 14 =>
      Sphincs.Words.ftsRoot idx kappa (u kappa) pp (sig.secrets kappa) (sig.ftsPaths kappa)
    let key := Sphincs.Words.th (Sphincs.Words.tweak 11 0 idx 0 0) pp (roots.flatMap fun d => [d.1, d.2])
    match [2, 1, 0].foldlM (Sphincs.Words.layerRoot pp idx sig) key with
    | none => false
    | some top => top == root

/-- The specification's verification after the message digest. -/
def specCore (pkp : LeanSphincs.PublicKey) (sg : LeanSphincs.Signature) (idx : ℕ)
    (u : Vector ℕ LeanSphincs.Constants.K) : Bool :=
  if u[LeanSphincs.Constants.K - 1]'(by decide) != 0 then false
  else
    let fts := LeanSphincs.Fts.recover pkp.publicParam idx u sg.fts
    match [2, 1, 0].foldlM (LeanSphincs.layerRoot pkp.publicParam idx sg) fts with
    | none => false
    | some top => top == pkp.root

theorem words_verify_core (root pp : Dig) (msg : W × W × W × W) (sig : Sig) :
    Sphincs.Words.verify root pp msg sig = wordsCore root pp sig (Sphincs.Words.messageDigest pp root sig.rho msg).1
      (Sphincs.Words.messageDigest pp root sig.rho msg).2 := by
  unfold Sphincs.Words.verify
  generalize Sphincs.Words.messageDigest pp root sig.rho msg = MD
  cases MD
  rfl

theorem spec_verify_core (pkp : LeanSphincs.PublicKey) (m : LeanSphincs.Message) (sg : LeanSphincs.Signature) :
    LeanSphincs.verify pkp m sg = specCore pkp sg
      (LeanSphincs.messageDigest pkp.publicParam pkp.root sg.randomizer m).1
      (LeanSphincs.messageDigest pkp.publicParam pkp.root sg.randomizer m).2 := by
  unfold LeanSphincs.verify
  simp (config := { iota := false }) only []
  generalize LeanSphincs.messageDigest pkp.publicParam pkp.root sg.randomizer m = MD
  cases MD
  rfl

theorem core_eq (root pp : Dig) (sig : Sig) (idx : ℕ) (u : ℕ → ℕ) (hidx : idx < 2 ^ 26) (hu : ∀ κ, u κ < 2 ^ 10)
    (hc : ∀ lay, (sig.counters lay).toNat < 2 ^ 32) :
    specCore (pk root pp) (signature sig) idx (Vector.ofFn fun κ => u κ) = wordsCore root pp sig idx u := by
  unfold specCore wordsCore
  have hk : ((Vector.ofFn fun κ : Fin LeanSphincs.Constants.K => u κ)[LeanSphincs.Constants.K - 1]'(by decide)) =
      u 14 := by
    simp [LeanSphincs.Constants.K]
  rw [hk]
  have e1 : (pk root pp).publicParam = param pp := rfl
  have e2 : (pk root pp).root = dig root := rfl
  rw [e1, e2]
  by_cases h14 : u 14 = 0
  · rw [if_neg (by simp [h14]), if_neg (by simp [h14])]
    simp (config := { iota := false }) only []
    rw [recover_eq pp idx hidx u hu sig,
      show ([2, 1, 0] : List (Fin LeanSphincs.Constants.D)) = ([2, 1, 0] : List (Fin 3)).map fin3D from rfl,
      foldlM_dig _ _ (Sphincs.Words.layerRoot pp idx sig) (fun y a => layerRoot_eq pp y idx hidx sig a (hc a))]
    split <;> split
    · rfl
    · exact absurd ((Option.map_eq_none_iff.mp ‹Option.map dig _ = none›).symm.trans
        ‹List.foldlM _ _ _ = some _›) (by simp)
    · exact absurd ((congrArg (Option.map dig) ‹List.foldlM _ _ _ = none›).symm.trans
        ‹Option.map dig _ = some _›) (by simp)
    · have h3 := (congrArg (Option.map dig) ‹List.foldlM _ _ _ = some _›).symm.trans ‹Option.map dig _ = some _›
      rw [Option.map_some, Option.some.injEq] at h3
      subst h3
      exact beq_dig _ root
  · rw [if_pos (by simp [h14]), if_pos h14]

/-- The main bridge: verification over words is the specification's verification on the bytes of those words, the
counters below `2 ^ 32`. -/
theorem verify_eq (root pp : Dig) (msg : W × W × W × W) (sig : Sig)
    (hc : ∀ lay, (sig.counters lay).toNat < 2 ^ 32) :
    Sphincs.Words.verify root pp msg sig = LeanSphincs.verify (pk root pp) (message msg) (signature sig) := by
  have hb : (Sphincs.Words.messageDigest pp root sig.rho msg).1 < 2 ^ 26 ∧
      ∀ κ, (Sphincs.Words.messageDigest pp root sig.rho msg).2 κ < 2 ^ 10 := by
    unfold Sphincs.Words.messageDigest
    exact ⟨Nat.mod_lt _ (by norm_num), fun κ => Nat.mod_lt _ (by norm_num)⟩
  have e1 : (pk root pp).publicParam = param pp := rfl
  have e2 : (pk root pp).root = dig root := rfl
  have e3 : (signature sig).randomizer = randomizer sig.rho := rfl
  rw [words_verify_core, spec_verify_core, e1, e2, e3, messageDigest_eq]
  exact (core_eq root pp sig _ _ hb.1 hb.2 hc).symm

/-! ## Word verification accepts only counters below `2 ^ 32` -/

theorem foldlM_none (l : List (Fin 3)) (g : Dig → Fin 3 → Option Dig) (a : Fin 3) (ha : a ∈ l)
    (h : ∀ y, g y a = none) (x : Dig) : l.foldlM g x = none := by
  induction l generalizing x with
  | nil => simp at ha
  | cons b l ih =>
    rw [List.foldlM_cons]
    by_cases hab : a = b
    · subst hab
      rw [h x]
      rfl
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with e | e
        · exact absurd e hab
        · exact e
      rcases g x b with _ | y
      · rfl
      · exact ih ha' y

theorem layerRoot_none (pp M : Dig) (idx : ℕ) (sig : Sig) (lay : Fin 3)
    (hc : 2 ^ 32 ≤ (sig.counters lay).toNat) : Sphincs.Words.layerRoot pp idx sig M lay = none := by
  have he : Sphincs.Words.encode lay (Sphincs.Words.tau idx lay) (Sphincs.Words.leafIndex idx lay) pp M
      (sig.counters lay) = none := by
    unfold Sphincs.Words.encode
    simp (config := { iota := false }) only []
    rw [if_neg (fun h => absurd h.1 (by omega))]
  unfold Sphincs.Words.layerRoot
  simp (config := { iota := false }) only []
  rw [he]

/-- A signature word verification accepts has every counter below `2 ^ 32`. -/
theorem counters_lt (root pp : Dig) (msg : W × W × W × W) (sig : Sig)
    (h : Sphincs.Words.verify root pp msg sig = true) : ∀ lay, (sig.counters lay).toNat < 2 ^ 32 := by
  intro lay
  by_contra hlt
  rw [words_verify_core] at h
  unfold wordsCore at h
  split at h
  · exact absurd h (by simp)
  · simp (config := { iota := false }) only [] at h
    split at h
    · exact absurd h (by simp)
    · have hn := foldlM_none [2, 1, 0] (Sphincs.Words.layerRoot pp (Sphincs.Words.messageDigest pp root sig.rho msg).1
        sig) lay (by fin_cases lay <;> simp) (fun y => layerRoot_none pp y _ sig lay (by omega))
      exact absurd ((hn _).symm.trans ‹List.foldlM _ _ _ = some _›) (by simp)

/-! ## Decoding is onto -/

theorem byteOf_vword {n : ℕ} (v : Vector UInt8 n) (k : ℕ) (hk : k < 8) :
    byteOf (vword v 0) k = v.toArray.getD k 0 := by
  rw [vword, byteOf_or64 _ _ hk, Nat.mul_zero, Nat.zero_add]

theorem vword_lt (c : LeanSphincs.Counter) : (vword c 0).toNat < 2 ^ 32 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  by_cases h64 : j < 64
  · have hb := testBit_byteOf (vword c 0) (j / 8) (j % 8) (by omega)
    rw [show 8 * (j / 8) + j % 8 = j by omega, byteOf_vword _ _ (by omega)] at hb
    rw [← hb]
    have : c.toArray.getD (j / 8) 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        simp [LeanSphincs.Constants.COUNTER_LEN]; omega)]
      rfl
    rw [this]
    simp
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem counter_onto (c : LeanSphincs.Counter) : counter (vword c 0) = c := by
  apply Vector.ext
  intro k hk
  have hk4 : k < 4 := by simpa [LeanSphincs.Constants.COUNTER_LEN] using hk
  simp only [counter, wordsVec, Vector.getElem_ofFn, byteAt, wordAt, List.getD_eq_getElem?_getD,
    show k / 8 = 0 by omega, List.getElem?_cons_zero, Option.getD_some, Nat.mod_eq_of_lt (show k < 8 by omega)]
  rw [byteOf_vword _ _ (by omega)]
  simp [hk]

theorem dig_onto (d : LeanSphincs.Digest) : dig (vword d 0, vword d 1) = d := wordsVec_vword _ 2 rfl d

theorem param_onto (d : LeanSphincs.PublicParam) : param (vword d 0, vword d 1) = d := wordsVec_vword _ 2 rfl d

theorem randomizer_onto (d : LeanSphincs.Randomizer) : randomizer (vword d 0, vword d 1) = d :=
  wordsVec_vword _ 2 rfl d

/-- Every specification message is the bytes of four words. -/
theorem message_onto (m : LeanSphincs.Message) : ∃ msg, message msg = m :=
  ⟨(vword m 0, vword m 1, vword m 2, vword m 3), wordsVec_vword _ 4 rfl m⟩

/-- Every specification public key is the bytes of a root's and a parameter's words. -/
theorem publicKey_onto (p : LeanSphincs.PublicKey) : ∃ root pp, pk root pp = p := by
  obtain ⟨r, q⟩ := p
  exact ⟨(vword r 0, vword r 1), (vword q 0, vword q 1), by simp only [pk, dig_onto, param_onto]⟩

/-- The words of a digest. -/
def words2 (d : LeanSphincs.Digest) : Dig := (vword d 0, vword d 1)

/-- The words of a specification signature, its counters below `2 ^ 32`. -/
def sigWords (s : LeanSphincs.Signature) : Sig where
  rho := words2 s.randomizer
  secrets κ := words2 (s.fts[κ.val]'(by simp [LeanSphincs.Constants.FTS_TREES, LeanSphincs.Constants.K])).secret
  ftsPaths κ l := words2 ((s.fts[κ.val]'(by simp [LeanSphincs.Constants.FTS_TREES, LeanSphincs.Constants.K])).path[l.val]'(by
    simp [LeanSphincs.Constants.A]))
  counters lay := vword (s.layer (fin3D lay)).1 0
  tips lay i := words2 ((s.layer (fin3D lay)).2.1[i.val]'(by simp [LeanSphincs.Constants.V]))
  paths lay l := words2 ((s.layer (fin3D lay)).2.2.getD l.val (Vector.replicate _ 0))

/-- Every specification signature is the bytes of a signature's words, its counters below `2 ^ 32`. -/
theorem signature_onto (s : LeanSphincs.Signature) :
    ∃ sig : Sig, (∀ lay, (sig.counters lay).toNat < 2 ^ 32) ∧ signature sig = s := by
  refine ⟨sigWords s, fun lay => vword_lt _, ?_⟩
  obtain ⟨r, f, l0, l1, l2⟩ := s
  obtain ⟨c0, o0, p0⟩ := l0
  obtain ⟨c1, o1, p1⟩ := l1
  obtain ⟨c2, o2, p2⟩ := l2
  simp only [signature, LeanSphincs.Signature.mk.injEq]
  refine ⟨randomizer_onto r, ?_, ?_, ?_, ?_⟩
  · apply Vector.ext
    intro κ hκ
    simp only [Vector.getElem_ofFn, sigWords, words2, f14, f10, dig_onto]
    show _ = (⟨(f[κ]).secret, (f[κ]).path⟩ : LeanSphincs.FtsOpening)
    rw [LeanSphincs.FtsOpening.mk.injEq]
    refine ⟨rfl, ?_⟩
    apply Vector.ext
    intro l hl
    simp only [Vector.getElem_ofFn]
    rfl
  all_goals
    simp only [layerSig, LeanSphincs.LayerSignature.mk.injEq]
    refine ⟨counter_onto _, ?_, ?_⟩
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn, sigWords, words2, f42, dig_onto]
      rfl
    · apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn, sigWords, words2, dig_onto]
      simp [LeanSphincs.Signature.layer, fin3D, List.getD_eq_getElem?_getD, hi]

end LeanVMCircuits.Sphincs.Spec
