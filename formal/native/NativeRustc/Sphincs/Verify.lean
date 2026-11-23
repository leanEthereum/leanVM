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

end NativeRustc.Sphincs
