module

public import NativeRustc.Sphincs.Layers
public import Native.Sphincs.Input

/-!
# `sphincs_verify` is leanSPHINCS verification

The wrapper `rustc/sphincs.rs` turns the 977 input words of `Native.SphincsVerifier.encode pk msg
sig` into the key's, the message's and the signature's bytes (`sigBytes_eq`: the randomizer and
the FORS openings, then each layer's big-endian counter and words); parsed (`PublicKey.fromBytes`,
`Signature.fromBytes`) they are the bytes of the statement's values (`pk_fromBytes`,
`messageBytes_encode`, `randomizer_fromBytes`, `fors_fromBytes`, `layerHolds_fromBytes`), so
`sphincsVerify` is `Sphincs.verifyWithKeccak` (`verify_eq`).

`verify_decode` covers arbitrary words: re-encoding their decoded fields preserves the wrapper's
key, message and signature bytes, including the truncation of each layer counter to 32 bits.
-/

@[expose] public section

namespace NativeRustc.Sphincs

open _root_.Sphincs HashSig LeanVM.Protocol.KeccakHash Native Native.Keccak

/-! ## Bytes -/

/-- `u32::from_be_bytes` of `u32::to_be_bytes`. -/
theorem be32Of_be32 (x : UInt32) : be32Of (be32 x) = x := by
  have hr : (be32 x).reverse = u32Bytes x := by
    have hx := x.toNat_lt
    apply List.ext_getElem (by simp [be32, u32Bytes, XmssVerifier.bytes])
    intro i h1 h2
    have hi : i < 4 := by simpa [be32] using h1
    apply UInt8.toNat_inj.mp
    interval_cases i <;>
      simp [be32, u32Bytes, XmssVerifier.bytes, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
        Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat']
  rw [be32Of, List.take_of_length_le (by simp [be32]), beNat, hr]
  exact u32Of_u32Bytes x

/-- `len` bytes after a prefix and inside the next part. -/
theorem slice_append_left (p q : List UInt8) {off len : Nat} (h : off + len ≤ p.length) :
    slice (p ++ q) off len = slice p off len := by
  rw [slice, slice, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

/-- `len` bytes past a prefix. -/
theorem slice_append_right (p q : List UInt8) (off len : Nat) :
    slice (p ++ q) (p.length + off) len = slice q off len := by
  rw [slice, slice, List.drop_length_add_append]

/-- The 16 bytes at `8 a` of words' bytes are words `a`, `a + 1`. -/
theorem slice_words (f : Nat → UInt64) {n a : Nat} (h : a + 2 ≤ n) :
    slice (wordsBytes ((List.range n).map f)) (8 * a) 16 = wordsBytes [f a, f (a + 1)] := by
  rw [slice, show (16 : Nat) = 8 * 2 from rfl, slice_wordsBytes, take_two_drop_map_range _ h]

/-! ## The signature's bytes -/

/-- The randomizer's and the FORS openings' bytes: words `8 .. 537`. -/
def headBytes (w : Nat → UInt64) : List UInt8 := wordsBytes ((List.range 530).map fun k ↦ w (8 + k))

/-- Layer `l`'s bytes: its counter, big-endian, then its words. -/
def layerBytes (w : Nat → UInt64) (l : Nat) : List UInt8 :=
  be32 (w (layerWordOff l)).toUInt32 ++
    wordsBytes ((List.range (2 * (64 + layerHeights.getD l 0))).map fun k ↦ w (layerWordOff l + 1 + k))

theorem sigBytes_eq (w : Nat → UInt64) :
    sigBytes w = headBytes w ++ (layerBytes w 0 ++ (layerBytes w 1 ++ layerBytes w 2)) := by
  simp only [sigBytes, show List.range 3 = [0, 1, 2] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rfl

theorem length_headBytes (w : Nat → UInt64) : (headBytes w).length = 4240 := by
  rw [headBytes, Proof.length_wordsBytes]; simp

theorem length_layerBytes (w : Nat → UInt64) (l : Nat) :
    (layerBytes w l).length = 4 + 16 * (64 + layerHeights.getD l 0) := by
  rw [layerBytes, List.length_append, Proof.length_wordsBytes]
  simp [be32]
  omega

/-- The signature's bytes are layer `l`'s bytes after `sigLayerOff l` bytes. -/
theorem sigBytes_split (w : Nat → UInt64) {l : Nat} (hl : l < 3) :
    ∃ pre post : List UInt8, pre.length = sigLayerOff l ∧ sigBytes w = pre ++ (layerBytes w l ++ post) := by
  rw [sigBytes_eq]
  interval_cases l
  · exact ⟨headBytes w, layerBytes w 1 ++ layerBytes w 2, length_headBytes w, rfl⟩
  · refine ⟨headBytes w ++ layerBytes w 0, layerBytes w 2, ?_, by simp only [List.append_assoc]⟩
    rw [List.length_append, length_headBytes, length_layerBytes]
    rfl
  · refine ⟨headBytes w ++ (layerBytes w 0 ++ layerBytes w 1), [], ?_, by simp⟩
    rw [List.length_append, List.length_append, length_headBytes, length_layerBytes,
      length_layerBytes]
    rfl

/-- **The randomizer's and the FORS openings' 16-byte values**: words `8 + a`, `9 + a`. -/
theorem slice_head (w : Nat → UInt64) {a : Nat} (ha : a + 2 ≤ 530) :
    slice (sigBytes w) (8 * a) 16 = wordsBytes [w (8 + a), w (9 + a)] := by
  rw [sigBytes_eq, slice_append_left _ _ (by rw [length_headBytes]; omega), headBytes,
    slice_words _ ha, show 8 + (a + 1) = 9 + a by omega]

/-- **Layer `l`'s counter**: its first word, big-endian. -/
theorem slice_counter (w : Nat → UInt64) {l : Nat} (hl : l < 3) :
    slice (sigBytes w) (sigLayerOff l) 4 = be32 (w (layerWordOff l)).toUInt32 := by
  obtain ⟨pre, post, hpre, h⟩ := sigBytes_split w hl
  rw [h, ← hpre, ← Nat.add_zero pre.length, slice_append_right, layerBytes, List.append_assoc,
    slice_append_left _ _ (by simp [be32])]
  simp [slice, be32]

/-- **Layer `l`'s 16-byte values**: words `layerWordOff l + 1 + a` and the next. -/
theorem slice_layer (w : Nat → UInt64) {l a : Nat} (hl : l < 3)
    (ha : a + 2 ≤ 2 * (64 + layerHeights.getD l 0)) :
    slice (sigBytes w) (sigLayerOff l + 4 + 8 * a) 16 =
      wordsBytes [w (layerWordOff l + 1 + a), w (layerWordOff l + 2 + a)] := by
  obtain ⟨pre, post, hpre, h⟩ := sigBytes_split w hl
  rw [h, ← hpre, Nat.add_assoc, slice_append_right, layerBytes, List.append_assoc,
    show 4 + 8 * a = (be32 (w (layerWordOff l)).toUInt32).length + 8 * a by simp [be32],
    slice_append_right, slice_append_left _ _ (by
      rw [Proof.length_wordsBytes, List.length_map, List.length_range]; omega),
    slice_words _ ha, show layerWordOff l + 1 + (a + 1) = layerWordOff l + 2 + a by omega]

/-! ## The parsed signature -/

variable (pk : _root_.Sphincs.PublicKey) (m : Message) (sig : _root_.Sphincs.Signature)

theorem randomizer_fromBytes :
    (Signature.fromBytes (sigBytes (SphincsVerifier.encode pk m sig))).randomizer =
      le16 sig.randomizer := by
  rw [Signature.fromBytes, show (0 : Nat) = 8 * 0 from rfl, slice_head _ (by omega),
    le16_eq_wordsBytes]
  rfl

theorem fors_fromBytes :
    (Signature.fromBytes (sigBytes (SphincsVerifier.encode pk m sig))).fors = List.ofFn fun c ↦
      ⟨le16 (sig.forsOpening c).secret, List.ofFn fun z ↦ le16 ((sig.forsOpening c).path z)⟩ := by
  apply List.ext_getElem (by simp [Signature.fromBytes, forsTreeCount])
  intro c h1 h2
  have hc : c < 24 := by simpa [Signature.fromBytes] using h1
  have hκ : (⟨c, hc⟩ : ForsTreeIndex).val = c := rfl
  rw [List.getElem_ofFn]
  simp only [Signature.fromBytes, List.getElem_map, List.getElem_range]
  rw [ForsTreeOpening.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [show 16 + 176 * c = 8 * (2 + 22 * c) by omega, slice_head _ (by omega),
      show 8 + (2 + 22 * c) = 10 + 22 * (⟨c, hc⟩ : ForsTreeIndex).val + 0 by omega,
      show 9 + (2 + 22 * c) = 10 + 22 * (⟨c, hc⟩ : ForsTreeIndex).val + 1 by omega,
      SphincsVerifier.encode_fors _ _ _ _ (by omega), SphincsVerifier.encode_fors _ _ _ _ (by omega),
      SphincsVerifier.forsWord_secret _ (by omega), SphincsVerifier.forsWord_secret _ (by omega),
      le16_eq_wordsBytes]
    rfl
  · apply List.ext_getElem (by simp [forsTreeHeight])
    intro z h1 h2
    have hz : z < 10 := by simpa using h1
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      show 32 + 176 * c + 16 * z = 8 * (4 + 22 * c + 2 * z) by omega, slice_head _ (by omega),
      show 8 + (4 + 22 * c + 2 * z) =
        10 + 22 * (⟨c, hc⟩ : ForsTreeIndex).val + (2 + 2 * (⟨z, hz⟩ : Fin forsTreeHeight).val + 0)
        by simp only; omega,
      show 9 + (4 + 22 * c + 2 * z) =
        10 + 22 * (⟨c, hc⟩ : ForsTreeIndex).val + (2 + 2 * (⟨z, hz⟩ : Fin forsTreeHeight).val + 1)
        by simp only; omega,
      SphincsVerifier.encode_fors _ _ _ _ (by simp only; omega),
      SphincsVerifier.encode_fors _ _ _ _ (by simp only; omega),
      SphincsVerifier.forsWord_path _ _ (by omega), SphincsVerifier.forsWord_path _ _ (by omega),
      le16_eq_wordsBytes]
    rfl

theorem layerHeights_eq (l : Layer) : layerHeights.getD l.val 0 = layerHeight l := by
  obtain ⟨l, hl⟩ := l
  have : l < 3 := hl
  interval_cases l <;> rfl

theorem layerWordOff_eq (l : Nat) : layerWordOff l = SphincsVerifier.layerOff l := rfl

/-- Layer `l`'s nodes of the three layers' paths, one after the other. -/
theorem path_flatMap {α : Type} (f : Nat → List α)
    (hf : ∀ k, k < 3 → (f k).length = layerHeights.getD k 0) {l : Nat} (hl : l < 3) :
    (((List.range 3).flatMap f).drop (layerHeights.take l).sum).take (layerHeights.getD l 0) =
      f l := by
  have h0 : (f 0).length = 8 := hf 0 (by omega)
  have h1 : (f 1).length = 8 := hf 1 (by omega)
  have h2 : (f 2).length = 10 := hf 2 (by omega)
  simp only [show List.range 3 = [0, 1, 2] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at *
  interval_cases l
  · exact List.take_left' h0
  · rw [show (layerHeights.take 1).sum = 8 from rfl, List.drop_left' h0]
    exact List.take_left' h1
  · rw [show (layerHeights.take 2).sum = 8 + 8 from rfl, ← List.drop_drop, List.drop_left' h0,
      List.drop_left' h1]
    exact List.take_of_length_le (by rw [h2]; exact le_refl 10)

/-- **Layer `l` of the parsed signature** holds the statement's layer `l`. -/
theorem layerHolds_fromBytes (l : Layer) :
    LayerHolds sig (Signature.fromBytes (sigBytes (SphincsVerifier.encode pk m sig))) l := by
  obtain ⟨l, hl⟩ := l
  have hl3 : l < 3 := hl
  have hh := layerHeights_eq ⟨l, hl⟩
  have hh' : layerHeights.getD l 0 = layerHeight ⟨l, hl⟩ := hh
  have hhl := layerHeight_le ⟨l, hl⟩
  have hget : ((List.range 3).map fun l ↦ (⟨be32Of (slice (sigBytes
      (SphincsVerifier.encode pk m sig)) (sigLayerOff l) 4), (List.range 64).map fun i ↦
        slice (sigBytes (SphincsVerifier.encode pk m sig)) (sigLayerOff l + 4 + 16 * i) 16⟩ :
        LayerSignature)).getD l ⟨0, []⟩ =
      ⟨be32Of (slice (sigBytes (SphincsVerifier.encode pk m sig)) (sigLayerOff l) 4),
        (List.range 64).map fun i ↦
          slice (sigBytes (SphincsVerifier.encode pk m sig)) (sigLayerOff l + 4 + 16 * i) 16⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl3]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [Signature.fromBytes]
    dsimp only
    rw [hget]
    dsimp only
    rw [slice_counter _ hl3, be32Of_be32, layerWordOff_eq, ← Nat.add_zero (SphincsVerifier.layerOff l),
      SphincsVerifier.encode_layer pk m sig l hl (by omega), SphincsVerifier.layerWord_counter,
      UInt64.toNat_toUInt32, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    have : (sig.layers ⟨l, hl⟩).counter.toNat < 2 ^ 32 := (sig.layers ⟨l, hl⟩).counter.isLt
    omega
  · rw [Signature.fromBytes]
    dsimp only
    rw [hget]
    dsimp only
    apply List.ext_getElem (by simp [chainCount])
    intro i h1 h2
    have hi : i < 64 := by simpa using h1
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      show sigLayerOff l + 4 + 16 * i = sigLayerOff l + 4 + 8 * (2 * i) by omega,
      slice_layer _ hl3 (by omega), layerWordOff_eq,
      show SphincsVerifier.layerOff l + 1 + 2 * i =
        SphincsVerifier.layerOff l + (1 + 2 * (⟨i, hi⟩ : ChainIndex).val + 0) by simp only; omega,
      show SphincsVerifier.layerOff l + 2 + 2 * i =
        SphincsVerifier.layerOff l + (1 + 2 * (⟨i, hi⟩ : ChainIndex).val + 1) by simp only; omega,
      SphincsVerifier.encode_layer pk m sig l hl (by simp only; omega),
      SphincsVerifier.encode_layer pk m sig l hl (by simp only; omega),
      SphincsVerifier.layerWord_chain _ _ (by omega), SphincsVerifier.layerWord_chain _ _ (by omega),
      le16_eq_wordsBytes]
    rfl
  · rw [Signature.path, Signature.fromBytes]
    dsimp only
    rw [path_flatMap _ (fun k _ ↦ by simp) hl3]
    apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn, hh'])
    intro z h1 h2
    have hz : z < layerHeight ⟨l, hl⟩ := by
      rw [List.length_map, List.length_range, hh'] at h1; exact h1
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      show sigLayerOff l + 1028 + 16 * z = sigLayerOff l + 4 + 8 * (128 + 2 * z) by omega,
      slice_layer _ hl3 (by omega), layerWordOff_eq,
      show SphincsVerifier.layerOff l + 1 + (128 + 2 * z) = SphincsVerifier.layerOff l +
        (129 + 2 * (⟨z, hz⟩ : Fin (layerHeight ⟨l, hl⟩)).val + 0) by simp only; omega,
      show SphincsVerifier.layerOff l + 2 + (128 + 2 * z) = SphincsVerifier.layerOff l +
        (129 + 2 * (⟨z, hz⟩ : Fin (layerHeight ⟨l, hl⟩)).val + 1) by simp only; omega,
      SphincsVerifier.encode_layer pk m sig l hl (by simp only; omega),
      SphincsVerifier.encode_layer pk m sig l hl (by simp only; omega),
      SphincsVerifier.layerWord_path _ _ (by omega), SphincsVerifier.layerWord_path _ _ (by omega),
      le16_eq_wordsBytes]
    rfl

/-! ## The key, the message and verification -/

/-- **`LeanSphincsPublicKey::from_bytes`** on the key's bytes. -/
theorem pk_fromBytes :
    PublicKey.fromBytes (pkBytes (SphincsVerifier.encode pk m sig)) =
      ⟨littleEndianBytes 16 pk.publicSeed, le16 pk.root⟩ := by
  have hw : pkBytes (SphincsVerifier.encode pk m sig) =
      wordsBytes [digestLo pk.publicSeed, digestHi pk.publicSeed] ++
        wordsBytes [digestLo pk.root, digestHi pk.root] := rfl
  rw [PublicKey.fromBytes, hw, List.take_left' (by rw [Proof.length_wordsBytes]; rfl),
    List.drop_left' (by rw [Proof.length_wordsBytes]; rfl), le16_eq_wordsBytes, littleEndianBytes_16]

/-- The message's bytes. -/
theorem messageBytes_encode :
    messageBytes (SphincsVerifier.encode pk m sig) = littleEndianBytes 32 m := by
  rw [littleEndianBytes_32, messageBytes]
  congr 1

/-- **`sphincs_verify` is leanSPHINCS verification**: the Rust byte model of `verify` on the
wrapper's bytes of the input words `encode pk msg sig` is `Sphincs.verifyWithKeccak`. -/
theorem verify_eq :
    sphincsVerify (SphincsVerifier.encode pk m sig) = verifyWithKeccak pk m sig := by
  rw [sphincsVerify, pk_fromBytes, messageBytes_encode]
  exact verify_spec pk m sig _ (randomizer_fromBytes pk m sig) (fors_fromBytes pk m sig)
    (layerHolds_fromBytes pk m sig)

private theorem decode_digestWord (w : Nat → UInt64) (b k : Nat) (hk : k < 2) :
    SphincsVerifier.digestWord (ofWords (w b) (w (b + 1))) k = w (b + k) := by
  interval_cases k <;>
    simp [SphincsVerifier.digestWord, digestLo_ofWords, digestHi_ofWords]

private theorem decode_messageWord (w : Nat → UInt64) {i : Nat} (hi : i < 4) :
    word256 (SphincsVerifier.decode w).2.1 i = w (4 + i) := by
  have h4 := (w 4).toNat_lt
  have h5 := (w 5).toNat_lt
  have h6 := (w 6).toNat_lt
  have h7 := (w 7).toNat_lt
  apply UInt64.toNat_inj.mp
  interval_cases i <;>
    simp only [SphincsVerifier.decode, word256, BitVec.toNat_ofNat, UInt64.toNat_ofNat']
    <;> norm_num <;> omega

private theorem decode_forsWord (w : Nat → UInt64) (c : ForsTreeIndex)
    {k : Nat} (hk : k < 22) :
    SphincsVerifier.forsWord ((SphincsVerifier.decode w).2.2.forsOpening c) k =
      w (SphincsVerifier.forsOff c.val + k) := by
  simp only [SphincsVerifier.forsWord]
  split
  · exact decode_digestWord w _ _ ‹k < 2›
  · dsimp only [SphincsVerifier.decode]
    rw [decode_digestWord w _ _ (Nat.mod_lt _ (by decide))]
    congr 1
    omega

private theorem decode_layerWord (w : Nat → UInt64) (l : Layer)
    {k : Nat} (hk0 : 0 < k) (hk : k < 129 + 2 * layerHeight l) :
    SphincsVerifier.layerWord ((SphincsVerifier.decode w).2.2.layers l) k =
      w (SphincsVerifier.layerOff l.val + k) := by
  simp only [SphincsVerifier.layerWord, ite_eq_right (Nat.ne_of_gt hk0)]
  split
  · dsimp only [SphincsVerifier.decode]
    rw [decode_digestWord w _ _ (Nat.mod_lt _ (by decide))]
    apply congrArg w
    omega
  · dsimp only [SphincsVerifier.decode]
    rw [decode_digestWord w _ _ (Nat.mod_lt _ (by decide))]
    apply congrArg w
    omega

/-- Re-encoding preserves the key, message, randomizer and FORS words. -/
theorem encode_decode_head (w : Nat → UInt64) {i : Nat} (hi : i < 538) :
    SphincsVerifier.encode (SphincsVerifier.decode w).1 (SphincsVerifier.decode w).2.1
      (SphincsVerifier.decode w).2.2 i = w i := by
  unfold SphincsVerifier.encode
  split
  · simpa only [SphincsVerifier.decode, Nat.zero_add] using decode_digestWord w 0 i ‹i < 2›
  · split
    · have h := decode_digestWord w 2 (i - 2) (by omega)
      simpa only [SphincsVerifier.decode, show 2 + (i - 2) = i by omega] using h
    · split
      · have h := decode_messageWord w (i := i - 4) (by omega)
        simpa only [show 4 + (i - 4) = i by omega] using h
      · split
        · have h := decode_digestWord w 8 (i - 8) (by omega)
          simpa only [SphincsVerifier.decode, show 8 + (i - 8) = i by omega] using h
        · rw [dite_eq_left (show i < SphincsVerifier.layerOff 0 by exact hi)]
          rw [decode_forsWord w _ (Nat.mod_lt _ (by decide))]
          apply congrArg w
          change 10 + 22 * ((i - 10) / 22) + (i - 10) % 22 = i
          omega

/-- Re-encoding preserves every full-width layer word. -/
theorem encode_decode_layer (w : Nat → UInt64) (l : Layer) {k : Nat}
    (hk0 : 0 < k) (hk : k < 129 + 2 * layerHeight l) :
    SphincsVerifier.encode (SphincsVerifier.decode w).1 (SphincsVerifier.decode w).2.1
      (SphincsVerifier.decode w).2.2 (SphincsVerifier.layerOff l.val + k) =
      w (SphincsVerifier.layerOff l.val + k) := by
  rw [SphincsVerifier.encode_layer _ _ _ l.val l.isLt hk]
  exact decode_layerWord w l hk0 hk

/-- The counter conversion preserves exactly the low 32 bits. -/
theorem encode_decode_counter (w : Nat → UInt64) (l : Layer) :
    (SphincsVerifier.encode (SphincsVerifier.decode w).1 (SphincsVerifier.decode w).2.1
      (SphincsVerifier.decode w).2.2 (SphincsVerifier.layerOff l.val)).toUInt32 =
      (w (SphincsVerifier.layerOff l.val)).toUInt32 := by
  rw [← Nat.add_zero (SphincsVerifier.layerOff l.val),
    SphincsVerifier.encode_layer _ _ _ l.val l.isLt (by omega),
    SphincsVerifier.layerWord_counter]
  apply UInt32.toNat_inj.mp
  have h := (w (SphincsVerifier.layerOff l.val)).toUInt32.toNat_lt
  change ((w (SphincsVerifier.layerOff l.val)).toUInt32.toNat.toUInt64).toUInt32.toNat =
    (w (SphincsVerifier.layerOff l.val)).toUInt32.toNat
  rw [UInt64.toNat_toUInt32, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

/-- Every wrapper input is verified against the Statement specification of its decoded fields. -/
theorem verify_decode (w : Nat → UInt64) :
    sphincsVerify w = verifyWithKeccak (SphincsVerifier.decode w).1
      (SphincsVerifier.decode w).2.1 (SphincsVerifier.decode w).2.2 := by
  let e := SphincsVerifier.encode (SphincsVerifier.decode w).1
    (SphincsVerifier.decode w).2.1 (SphincsVerifier.decode w).2.2
  have hp : pkBytes e = pkBytes w := by
    unfold pkBytes
    congr 1
    apply List.map_congr_left
    intro i hi
    exact encode_decode_head w (by have := List.mem_range.mp hi; omega)
  have hm : messageBytes e = messageBytes w := by
    unfold messageBytes
    congr 1
    apply List.map_congr_left
    intro i hi
    exact encode_decode_head w (by have := List.mem_range.mp hi; omega)
  have hh : headBytes e = headBytes w := by
    unfold headBytes
    apply congrArg wordsBytes
    apply List.map_congr_left
    intro i hi
    exact encode_decode_head w (by have := List.mem_range.mp hi; omega)
  have hl : ∀ l < 3, layerBytes e l = layerBytes w l := by
    intro l hl
    unfold layerBytes
    rw [show (e (layerWordOff l)).toUInt32 = (w (layerWordOff l)).toUInt32 from
      encode_decode_counter w ⟨l, hl⟩]
    apply congrArg (fun bs => be32 (w (layerWordOff l)).toUInt32 ++ wordsBytes bs)
    apply List.map_congr_left
    intro k hk
    have hk := List.mem_range.mp hk
    have he : layerHeights.getD l 0 = layerHeight ⟨l, hl⟩ := layerHeights_eq ⟨l, hl⟩
    simpa only [layerWordOff_eq, Nat.add_assoc] using
      encode_decode_layer w ⟨l, hl⟩ (k := 1 + k) (by omega) (by omega)
  have hs : sigBytes e = sigBytes w := by
    rw [sigBytes_eq, sigBytes_eq, hh, hl 0 (by omega), hl 1 (by omega), hl 2 (by omega)]
  rw [← verify_eq (SphincsVerifier.decode w).1 (SphincsVerifier.decode w).2.1
    (SphincsVerifier.decode w).2.2]
  change sphincsVerify w = sphincsVerify e
  unfold sphincsVerify
  rw [hp, hm, hs]

/-! ## Direct raw-byte verification -/

theorem littleEndianBytes_ofLeNat (n : Nat) (b : List UInt8) (hb : b.length = n) :
    HashSig.littleEndianBytes n (BitVec.ofNat (8 * n) (leNat b)) = b := by
  rw [XmssVerifier.littleEndianBytes_eq_bytes]
  apply List.ext_getElem (by simp [XmssVerifier.bytes, hb])
  intro k h1 h2
  have hk : k < b.length := h2
  have hlt : leNat b < 2 ^ (8 * n) := by
    have := leNat_lt b
    rw [hb, show 256 ^ n = 2 ^ (8 * n) by rw [pow_mul]; rfl] at this
    exact this
  apply UInt8.toNat_inj.mp
  simp only [XmssVerifier.bytes, List.getElem_map, List.getElem_range, UInt8.toNat_ofNat',
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact leNat_div_mod b hk

theorem le16_ofLeNat (b : List UInt8) (hb : b.length = 16) :
    le16 (BitVec.ofNat 128 (leNat b)) = b :=
  littleEndianBytes_ofLeNat 16 b hb

theorem be32Of_toNat_eq (b : List UInt8) (hb : b.length = 4) :
    (be32Of b).toNat = (BitVec.ofNat 32 (leNat b.reverse)).toNat := by
  have hlt : leNat b.reverse < 2 ^ 32 := by
    have := leNat_lt b.reverse
    rw [List.length_reverse, hb] at this
    simpa using this
  simp only [be32Of, beNat, List.take_of_length_le (by omega : b.length ≤ 4),
    UInt32.toNat_ofNat', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem le32_be32Of (b : List UInt8) (hb : b.length = 4) :
    (be32 (be32Of b)).reverse = b.reverse := by
  have hrev : (be32 (be32Of b)).reverse = u32Bytes (be32Of b) := by
    apply List.ext_getElem (by simp [be32, u32Bytes, XmssVerifier.bytes])
    intro i h1 _
    have hi : i < 4 := by simpa [be32] using h1
    apply UInt8.toNat_inj.mp
    interval_cases i <;>
      simp [be32, u32Bytes, XmssVerifier.bytes, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
        Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat']
  rw [hrev]
  have hlt : leNat b.reverse < 2 ^ 32 := by
    have := leNat_lt b.reverse
    rw [List.length_reverse, hb] at this
    simpa using this
  apply List.ext_getElem (by simp [u32Bytes, XmssVerifier.bytes, hb])
  intro k h1 h2
  have hk : k < b.reverse.length := h2
  apply UInt8.toNat_inj.mp
  simp only [u32Bytes, XmssVerifier.bytes, List.getElem_map, List.getElem_range, UInt8.toNat_ofNat',
    be32Of_toNat_eq b hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact leNat_div_mod b.reverse hk

private theorem leNatBytes_eq (b : List UInt8) : SphincsVerifier.leNatBytes b = leNat b := rfl
private theorem sliceBytes_eq (b : List UInt8) (off len : Nat) :
    SphincsVerifier.sliceBytes b off len = slice b off len := rfl
private theorem sigByteLayerOff_eq (l : Nat) : SphincsVerifier.sigByteLayerOff l = sigLayerOff l := rfl

private theorem length_slice_le {b : List UInt8} {off len : Nat} (h : off + len ≤ b.length) :
    (slice b off len).length = len := by
  simp only [slice, List.length_take, List.length_drop]
  omega

private theorem pk_fromBytes_raw (pk : List UInt8) (hpk : pk.length = 32) :
    PublicKey.fromBytes pk =
      ⟨littleEndianBytes 16 (SphincsVerifier.decodePk pk).publicSeed,
        le16 (SphincsVerifier.decodePk pk).root⟩ := by
  have hp1 : (pk.take 16).length = 16 := by simp [hpk]
  have hp2 : (pk.drop 16).length = 16 := by simp [hpk]
  rw [PublicKey.fromBytes, SphincsVerifier.decodePk]
  dsimp only
  rw [sliceBytes_eq, sliceBytes_eq, leNatBytes_eq, leNatBytes_eq]
  have hs1 : slice pk 0 16 = pk.take 16 := by simp [slice]
  have hs2 : slice pk 16 16 = pk.drop 16 := by
    rw [slice, List.take_of_length_le (by omega : (pk.drop 16).length ≤ 16)]
  rw [hs1, hs2, littleEndianBytes_ofLeNat 16 (pk.take 16) hp1, le16_ofLeNat (pk.drop 16) hp2]

private theorem msg_fromBytes_raw (msg : List UInt8) (hmsg : msg.length = 32) :
    msg = littleEndianBytes 32 (SphincsVerifier.decodeMsg msg) := by
  rw [SphincsVerifier.decodeMsg, sliceBytes_eq, leNatBytes_eq]
  have hs : slice msg 0 32 = msg := by
    rw [slice, List.drop_zero, List.take_of_length_le (by omega : msg.length ≤ 32)]
  rw [hs]
  exact (littleEndianBytes_ofLeNat 32 msg hmsg).symm

private theorem randomizer_fromBytes_raw (sig : List UInt8) (hsig : sig.length = 7740) :
    (Signature.fromBytes sig).randomizer = le16 (SphincsVerifier.decodeSig sig).randomizer := by
  rw [Signature.fromBytes, SphincsVerifier.decodeSig]
  dsimp only
  rw [sliceBytes_eq, leNatBytes_eq]
  exact (le16_ofLeNat (slice sig 0 16) (length_slice_le (by omega))).symm

private theorem fors_fromBytes_raw (sig : List UInt8) (hsig : sig.length = 7740) :
    (Signature.fromBytes sig).fors = List.ofFn fun c ↦
      ⟨le16 ((SphincsVerifier.decodeSig sig).forsOpening c).secret,
        List.ofFn fun z ↦ le16 (((SphincsVerifier.decodeSig sig).forsOpening c).path z)⟩ := by
  apply List.ext_getElem (by simp [Signature.fromBytes, forsTreeCount])
  intro c h1 _
  have hc : c < 24 := by simpa [Signature.fromBytes] using h1
  rw [List.getElem_ofFn]
  simp only [Signature.fromBytes, SphincsVerifier.decodeSig, List.getElem_map, List.getElem_range]
  rw [ForsTreeOpening.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [sliceBytes_eq, leNatBytes_eq]
    exact (le16_ofLeNat (slice sig (16 + 176 * c) 16) (length_slice_le (by omega))).symm
  · apply List.ext_getElem (by simp [forsTreeHeight])
    intro z hz1 _
    have hz : z < 10 := by simpa using hz1
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, sliceBytes_eq, leNatBytes_eq]
    exact (le16_ofLeNat (slice sig (32 + 176 * c + 16 * z) 16) (length_slice_le (by omega))).symm

private theorem layerHolds_fromBytes_raw (sig : List UInt8) (hsig : sig.length = 7740) (l : Layer) :
    LayerHolds (SphincsVerifier.decodeSig sig) (Signature.fromBytes sig) l := by
  obtain ⟨l, hl⟩ := l
  have hl3 : l < 3 := hl
  have hh : layerHeights.getD l 0 = layerHeight ⟨l, hl⟩ := layerHeights_eq ⟨l, hl⟩
  have hoff : sigLayerOff l + 1028 + 16 * layerHeights.getD l 0 ≤ 7740 := by
    interval_cases l <;> decide
  have hget : ((List.range 3).map fun l ↦ (⟨be32Of (slice sig (sigLayerOff l) 4),
      (List.range 64).map fun i ↦ slice sig (sigLayerOff l + 4 + 16 * i) 16⟩ :
        LayerSignature)).getD l ⟨0, []⟩ =
      ⟨be32Of (slice sig (sigLayerOff l) 4),
        (List.range 64).map fun i ↦ slice sig (sigLayerOff l + 4 + 16 * i) 16⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl3]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [Signature.fromBytes, SphincsVerifier.decodeSig]; dsimp only; rw [hget]; dsimp only
    simp only [sigByteLayerOff_eq, sliceBytes_eq, leNatBytes_eq]
    exact be32Of_toNat_eq (slice sig (sigLayerOff l) 4) (length_slice_le (by omega))
  · rw [Signature.fromBytes, SphincsVerifier.decodeSig]; dsimp only; rw [hget]; dsimp only
    apply List.ext_getElem (by simp [chainCount])
    intro i hi1 _
    have hi : i < 64 := by simpa using hi1
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, sigByteLayerOff_eq,
      sliceBytes_eq, leNatBytes_eq]
    exact (le16_ofLeNat (slice sig (sigLayerOff l + 4 + 16 * i) 16) (length_slice_le (by omega))).symm
  · rw [Signature.path, Signature.fromBytes, SphincsVerifier.decodeSig]; dsimp only
    rw [path_flatMap _ (fun k _ ↦ by simp) hl3]
    apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn, hh])
    intro z hz1 _
    have hz : z < layerHeight ⟨l, hl⟩ := by
      rw [List.length_map, List.length_range, hh] at hz1; exact hz1
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, sigByteLayerOff_eq,
      sliceBytes_eq, leNatBytes_eq]
    exact (le16_ofLeNat (slice sig (sigLayerOff l + 1028 + 16 * z) 16) (length_slice_le (by omega))).symm

/-- **Raw-byte `sphincs_verify` is leanSPHINCS verification** against `decodePk`/`decodeMsg`/`decodeSig`. -/
theorem verify_decode_bytes (pk msg sig : List UInt8)
    (hpk : pk.length = 32) (hmsg : msg.length = 32) (hsig : sig.length = 7740) :
    sphincsVerifyBytes pk msg sig =
      verifyWithKeccak (SphincsVerifier.decodePk pk) (SphincsVerifier.decodeMsg msg)
        (SphincsVerifier.decodeSig sig) := by
  have h := verify_spec (SphincsVerifier.decodePk pk) (SphincsVerifier.decodeMsg msg)
    (SphincsVerifier.decodeSig sig) (Signature.fromBytes sig)
    (randomizer_fromBytes_raw sig hsig) (fors_fromBytes_raw sig hsig)
    (layerHolds_fromBytes_raw sig hsig)
  rw [← pk_fromBytes_raw pk hpk, ← msg_fromBytes_raw msg hmsg] at h
  exact h

end NativeRustc.Sphincs
