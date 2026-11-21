module

public import Native.Sphincs.Words
public import Native.Sphincs.Layout

/-!
# The input words the verifier reads

Lookups into `encode` (`encode_seed`, `encode_fors`, `encode_layer`, ...), and `Static`: the
words every part of the verifier relies on and none writes, the input among them.
-/

@[expose] public section

namespace Native.SphincsVerifier

open _root_.Sphincs HashSig

variable (pk : _root_.Sphincs.PublicKey) (m : Message) (sig : Signature)

theorem encode_seed0 : encode pk m sig 0 = Native.digestLo pk.publicSeed := rfl
theorem encode_seed1 : encode pk m sig 1 = Native.digestHi pk.publicSeed := rfl
theorem encode_root0 : encode pk m sig 2 = Native.digestLo pk.root := rfl
theorem encode_root1 : encode pk m sig 3 = Native.digestHi pk.root := rfl
theorem encode_msg {i : Nat} (hi : i < 4) : encode pk m sig (4 + i) = Native.word256 m i := by
  unfold encode
  rw [ite_no (show ¬(4 + i < 2) by omega), ite_no (show ¬(4 + i < 4) by omega),
    ite_yes (show 4 + i < 8 by omega), Nat.add_sub_cancel_left]
theorem encode_R0 : encode pk m sig 8 = Native.digestLo sig.randomizer := rfl
theorem encode_R1 : encode pk m sig 9 = Native.digestHi sig.randomizer := rfl

theorem encode_fors (κ : ForsTreeIndex) {k : Nat} (hk : k < 22) :
    encode pk m sig (10 + 22 * κ.val + k) = forsWord (sig.forsOpening κ) k := by
  have hκ := κ.isLt
  unfold forsTreeCount at hκ
  unfold encode
  rw [ite_no (show ¬(10 + 22 * κ.val + k < 2) by omega),
    ite_no (show ¬(10 + 22 * κ.val + k < 4) by omega),
    ite_no (show ¬(10 + 22 * κ.val + k < 8) by omega),
    ite_no (show ¬(10 + 22 * κ.val + k < 10) by omega),
    dite_yes (show 10 + 22 * κ.val + k < layerOff 0 by unfold layerOff; omega)]
  congr 2
  · ext; simp only; omega
  · omega

theorem encode_layer (l : Nat) (hl : l < layerCount) {k : Nat}
    (hk : k < 129 + 2 * layerHeight ⟨l, hl⟩) :
    encode pk m sig (layerOff l + k) = layerWord (sig.layers ⟨l, hl⟩) k := by
  have h3 : l < 3 := hl
  have hh : layerHeight ⟨l, hl⟩ ≤ 10 := by unfold layerHeight; split <;> omega
  unfold encode
  rw [ite_no (show ¬(layerOff l + k < 2) by unfold layerOff; omega),
    ite_no (show ¬(layerOff l + k < 4) by unfold layerOff; omega),
    ite_no (show ¬(layerOff l + k < 8) by unfold layerOff; omega),
    ite_no (show ¬(layerOff l + k < 10) by unfold layerOff; omega),
    dite_no (show ¬(layerOff l + k < layerOff 0) by unfold layerOff; omega)]
  interval_cases l
  · have hk' : k < 145 := by simp [layerHeight] at hk; omega
    rw [ite_yes (show layerOff 0 + k < layerOff 1 by unfold layerOff; omega),
      Nat.add_sub_cancel_left]
    rfl
  · have hk' : k < 145 := by simp [layerHeight] at hk; omega
    rw [ite_no (show ¬(layerOff 1 + k < layerOff 1) by omega),
      ite_yes (show layerOff 1 + k < layerOff 2 by unfold layerOff; omega), Nat.add_sub_cancel_left]
    rfl
  · have hk' : k < 149 := by simp [layerHeight] at hk; omega
    rw [ite_no (show ¬(layerOff 2 + k < layerOff 1) by unfold layerOff; omega),
      ite_no (show ¬(layerOff 2 + k < layerOff 2) by omega),
      ite_yes (show layerOff 2 + k < inputWords by unfold layerOff inputWords; omega),
      Nat.add_sub_cancel_left]
    rfl

theorem forsWord_secret (o : ForsTreeOpening) {k : Nat} (hk : k < 2) :
    forsWord o k = digestWord o.secret k := by
  simp [forsWord, hk]

theorem forsWord_path (o : ForsTreeOpening) (z : Fin forsTreeHeight) {k : Nat} (hk : k < 2) :
    forsWord o (2 + 2 * z.val + k) = digestWord (o.path z) k := by
  have hz := z.isLt
  unfold forsTreeHeight at hz
  unfold forsWord
  rw [ite_no (show ¬(2 + 2 * z.val + k < 2) by omega),
    dite_yes (show 2 + 2 * z.val + k < 22 by omega)]
  congr 2
  · ext; simp only; omega
  · omega

theorem layerWord_counter {l : Layer} (ls : LayerSignature l) :
    layerWord ls 0 = ls.counter.toNat.toUInt64 := rfl

theorem layerWord_chain {l : Layer} (ls : LayerSignature l) (i : ChainIndex) {k : Nat} (hk : k < 2) :
    layerWord ls (1 + 2 * i.val + k) = digestWord (ls.chainValues i) k := by
  have hi := i.isLt
  unfold chainCount at hi
  unfold layerWord
  rw [ite_no (show ¬(1 + 2 * i.val + k = 0) by omega),
    dite_yes (show 1 + 2 * i.val + k < 129 by omega)]
  congr 2
  · ext; simp only; omega
  · omega

theorem layerWord_path {l : Layer} (ls : LayerSignature l) (j : Fin (layerHeight l)) {k : Nat}
    (hk : k < 2) :
    layerWord ls (129 + 2 * j.val + k) = digestWord (ls.authenticationPath j) k := by
  have hj := j.isLt
  unfold layerWord
  rw [ite_no (show ¬(129 + 2 * j.val + k = 0) by omega),
    dite_no (show ¬(129 + 2 * j.val + k < 129) by omega),
    dite_yes (show 129 + 2 * j.val + k < 129 + 2 * layerHeight l by omega)]
  simp only [show (129 + 2 * j.val + k - 129) / 2 = j.val by omega,
    show (129 + 2 * j.val + k - 129) % 2 = k by omega]

theorem digestWord_zero (d : BitVec 128) : digestWord d 0 = Native.digestLo d := rfl
theorem digestWord_one (d : BitVec 128) : digestWord d 1 = Native.digestHi d := rfl

/-- The words every part of the verifier relies on and none writes: the input, `PK.seed` at the
head of both hash buffers, and the address's two zero fields. -/
structure Static (V : Nat → UInt64) : Prop where
  input : ∀ i < inputWords, V (inp + i) = encode pk m sig i
  small0 : V smallBuf = Native.digestLo pk.publicSeed
  small1 : V (smallBuf + 1) = Native.digestHi pk.publicSeed
  big0 : V bigBuf = Native.digestLo pk.publicSeed
  big1 : V (bigBuf + 1) = Native.digestHi pk.publicSeed
  zero1 : V (adrsRec + 1) = 0
  zero2 : V (adrsRec + 2) = 0

theorem kept_input {i : Nat} (hi : i < inputWords) : Kept (inp + i) := by
  unfold Kept inputWords inp mdBuf bigBuf at *; omega

theorem Static.frame {pk : _root_.Sphincs.PublicKey} {m : Message} {sig : Signature}
    {V V' : Nat → UInt64} (h : Static pk m sig V) (hf : Frame V V') : Static pk m sig V' where
  input i hi := (hf _ (kept_input hi)).trans (h.input i hi)
  small0 := (hf _ (by unfold Kept; simp)).trans h.small0
  small1 := (hf _ (by unfold Kept; simp)).trans h.small1
  big0 := (hf _ (by unfold Kept; simp)).trans h.big0
  big1 := (hf _ (by unfold Kept; simp)).trans h.big1
  zero1 := (hf _ (by unfold Kept; simp)).trans h.zero1
  zero2 := (hf _ (by unfold Kept; simp)).trans h.zero2

end Native.SphincsVerifier
