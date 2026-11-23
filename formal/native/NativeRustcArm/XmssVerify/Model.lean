module

public import NativeRustc.Xmss.Model
import Native.Xmss.ModelSpec

/-!
# `xmss_verify`'s model, as its machine code computes it

`xmssVerify` of the input words `w` unfolded to the layers' roots (`xmssVerify_eq`): the key's
bytes (`pkB`, its root and public parameter `root`, `pp`), the message's (`msgB`), the signature's
(`sigB`), its layers (`bottomL`, `topL`, parsed by `LayerSignature::read` from offsets `4` and
`1204`) and the keys' indices (`li`, `li1`). The `u32` of a word's first four bytes
(`u32Bytes_toUInt32`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustc NativeRustc.Xmss LeanVM.Protocol.KeccakHash

@[expose] public section

variable (w : Nat → UInt64)

/-- The key's bytes. -/
def pkB : List UInt8 := pkBytes w
/-- The message's bytes. -/
def msgB : List UInt8 := messageBytes w
/-- The signature's bytes. -/
def sigB : List UInt8 := sigBytes w
/-- The key's root. -/
def root : List UInt8 := (pkB w).take 16
/-- The public parameter. -/
def pp : List UInt8 := (pkB w).drop 16
/-- The bottom layer's signature. -/
def bottomL : LayerSignature := (takeLayer (sigB w) 4).1
/-- The top layer's signature. -/
def topL : LayerSignature := (takeLayer (sigB w) 1204).1
/-- The bottom layer's key index: the leaf index. -/
def li : UInt32 := (w 8).toUInt32
/-- The top layer's key index. -/
def li1 : UInt32 := layerIndex (li w) 1

/-- **`xmss_verify`'s model** layer by layer. -/
theorem xmssVerify_eq : xmssVerify w =
    match layerRoot (pp w) 0 (li w) (msgB w) (bottomL w) with
    | none => false
    | some (_, r0) =>
      match layerRoot (pp w) 1 (li1 w) r0 (topL w) with
      | none => false
      | some (_, r) => r == root w := by
  have hli : u32Of ((sigBytes w).take 4) = li w := by
    rw [sigBytes, List.take_left' (length_u32Bytes _), u32Of_u32Bytes]
    rfl
  have h0 : layerIndex (li w) 0 = li w := by
    unfold layerIndex
    simp
  unfold xmssVerify verify Signature.fromBytes PublicKey.fromBytes
  simp only [hli, h0]
  rfl

/-- The `u32` of a word's bytes: its first four. -/
theorem u32Bytes_toUInt32 (x : UInt64) : u32Bytes x.toUInt32 = (wordBytes x).take 4 := by
  rw [u32Bytes, Native.XmssVerifier.wordBytes_eq_bytes]
  apply List.ext_getElem (by simp [Native.XmssVerifier.bytes])
  intro i h1 h2
  simp only [Native.XmssVerifier.bytes, List.getElem_map, List.getElem_range, List.getElem_take]
  simp only [Native.XmssVerifier.bytes, List.length_map, List.length_range] at h1
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', UInt64.toNat_toUInt32]
  have h : 256 ^ i * 256 ^ (4 - i) = 2 ^ 32 := by
    rw [← Nat.pow_add, show i + (4 - i) = 4 by omega]
    rfl
  rw [← h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact ⟨256 ^ (4 - i - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩

end

end NativeRustcArm.Xmss.XmssVerify
