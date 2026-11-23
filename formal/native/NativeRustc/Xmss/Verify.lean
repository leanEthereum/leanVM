module

public import NativeRustc.Xmss.Spec

/-!
# `xmss_verify` is leanXMSS verification

The wrapper `rustc/xmss.rs` turns the 309 input words of `Native.XmssVerifier.encode pk msg sig`
into the key's, the message's and the signature's bytes; parsed (`PublicKey.fromBytes`,
`Signature.fromBytes`) they are the bytes of the statement's values (`pk_fromBytes`,
`messageBytes_encode`, `takeLayer_encode`, `sig_fromBytes`), so `xmssVerify` is
`LeanXmss.verifyWithKeccak` (`verify_eq`).
-/

@[expose] public section

namespace NativeRustc.Xmss

open HashSig LeanXmss LeanVM.Protocol.KeccakHash Native Native.Keccak Native.XmssVerifier

variable (pk : HashSig.PublicKey) (msg : Message) (sig : LeanXmss.Signature)

/-- The 16 bytes at `4 + 16 m` of the signature's bytes are words `9 + 2 m` and `10 + 2 m`. -/
theorem slice_sigBytes (w : Nat → UInt64) {m : Nat} (hm : 2 * m + 2 ≤ 300) :
    slice (sigBytes w) (4 + 16 * m) 16 = wordsBytes [w (9 + 2 * m), w (10 + 2 * m)] := by
  rw [slice, sigBytes, show 4 + 16 * m = (u32Bytes (w 8).toUInt32).length + 8 * (2 * m) by
      rw [length_u32Bytes]; omega,
    List.drop_length_add_append, show (16 : Nat) = 8 * 2 from rfl, slice_wordsBytes,
    take_two_drop_map_range _ (by omega), show 9 + (2 * m + 1) = 10 + 2 * m by omega]

/-- Words `2 j`, `2 j + 1` of layer `n`'s signature, at byte `4 + 16 (75 n + j)`. -/
theorem slice_layer {n j : Nat} (hn : n < 2) (hj : j < 75) :
    slice (sigBytes (encode pk msg sig)) (4 + 16 * (75 * n + j)) 16 =
      wordsBytes [layerWord (sig.layers ⟨n, hn⟩) (2 * j),
        layerWord (sig.layers ⟨n, hn⟩) (2 * j + 1)] := by
  rw [slice_sigBytes _ (by omega), show 9 + 2 * (75 * n + j) = 9 + 150 * n + 2 * j by omega,
    show 10 + 2 * (75 * n + j) = 9 + 150 * n + (2 * j + 1) by omega,
    encode_layer pk msg sig hn (by omega), encode_layer pk msg sig hn (by omega)]

/-- **`from_bytes`'s closure** on the signature's bytes at layer `n`'s cursor `4 + 1200 n` parses
layer `n`'s signature. -/
theorem takeLayer_encode {n c : Nat} (hn : n < 2) (hc : c = 4 + 1200 * n) :
    takeLayer (sigBytes (encode pk msg sig)) c =
      (layerBytes (sig.layers ⟨n, hn⟩), 4 + 1200 * (n + 1)) := by
  subst hc
  rw [takeLayer, Prod.mk.injEq]
  refine ⟨?_, by omega⟩
  rw [layerBytes, LayerSignature.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [show 4 + 1200 * n = 4 + 16 * (75 * n + 0) by omega, slice_layer pk msg sig hn (by omega),
      le16_eq_wordsBytes]
    rfl
  · apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn]; rfl)
    intro i h1 h2
    have hi : i < chainCount := by simp only [List.length_map, List.length_range] at h1; exact h1
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      show 4 + 1200 * n + 16 + 16 * i = 4 + 16 * (75 * n + (1 + i)) by omega,
      slice_layer pk msg sig hn (by unfold chainCount at hi; omega),
      show 2 * (1 + i) = 2 + 2 * i by omega, show 2 + 2 * i + 1 = 3 + 2 * i by omega,
      (layerWord_chain _ hi).1, (layerWord_chain _ hi).2, le16_eq_wordsBytes]
  · apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn]; rfl)
    intro j h1 h2
    have hj : j < layerHeight := by simp only [List.length_map, List.length_range] at h1; exact h1
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      show 4 + 1200 * n + 944 + 16 * j = 4 + 16 * (75 * n + (59 + j)) by omega,
      slice_layer pk msg sig hn (by unfold layerHeight at hj; omega),
      show 2 * (59 + j) = 118 + 2 * j by omega, show 118 + 2 * j + 1 = 119 + 2 * j by omega,
      (layerWord_path _ hj).1, (layerWord_path _ hj).2, le16_eq_wordsBytes]

/-- The leaf index's `u32`. -/
theorem leafIndex_toNat :
    (encode pk msg sig 8).toUInt32.toNat = sig.leafIndex.val := by
  have h : sig.leafIndex.val < 2 ^ 32 := sig.leafIndex.isLt
  rw [(encode_head pk msg sig).2.2.2, UInt64.toNat_toUInt32, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

/-- **`LeanXmssSignature::from_bytes`** on the signature's bytes. -/
theorem sig_fromBytes :
    Signature.fromBytes (sigBytes (encode pk msg sig)) =
      ⟨(encode pk msg sig 8).toUInt32, layerBytes (sig.layers bottomLayer),
        layerBytes (sig.layers topLayer)⟩ := by
  rw [Signature.fromBytes, takeLayer_encode pk msg sig (n := 0) (by decide) rfl,
    takeLayer_encode pk msg sig (n := 1) (by decide) rfl, sigBytes,
    List.take_left' (length_u32Bytes _), u32Of_u32Bytes]
  rfl

/-- **`LeanXmssPublicKey::from_bytes`** on the key's bytes. -/
theorem pk_fromBytes :
    PublicKey.fromBytes (pkBytes (encode pk msg sig)) =
      ⟨le16 pk.root, littleEndianBytes 16 pk.parameter⟩ := by
  have hw : pkBytes (encode pk msg sig) = wordsBytes [digestLo pk.root, digestHi pk.root] ++
      wordsBytes [digestLo pk.parameter, digestHi pk.parameter] := rfl
  rw [PublicKey.fromBytes, hw, List.take_left' (by rw [Proof.length_wordsBytes]; rfl),
    List.drop_left' (by rw [Proof.length_wordsBytes]; rfl), le16_eq_wordsBytes, littleEndianBytes_16]

/-- The message's bytes. -/
theorem messageBytes_encode : messageBytes (encode pk msg sig) = littleEndianBytes 32 msg := by
  rw [littleEndianBytes_32, ← (encode_head pk msg sig).2.2.1]
  rfl

/-- **`xmss_verify` is leanXMSS verification**: the Rust byte model of `verify` on the wrapper's
bytes of the input words `encode pk msg sig` is `LeanXmss.verifyWithKeccak`. -/
theorem verify_eq : xmssVerify (encode pk msg sig) = verifyWithKeccak pk msg sig := by
  rw [xmssVerify, pk_fromBytes, messageBytes_encode, sig_fromBytes]
  exact verify_spec pk msg sig (leafIndex_toNat pk msg sig)

end NativeRustc.Xmss
