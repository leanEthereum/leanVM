module

public import NativeRustc.Xmss.Model
import Native.Xmss.ModelSpec

/-!
# `xmss_verify`'s model, as its machine code computes it

`xmssVerify` of the input words `w` unfolded to the layers' roots (`xmssVerify_eq`): the key's
bytes (`pkB`, its root and public parameter `root`, `pp`), the message's (`msgB`), the signature's
(`sigB`), its layers (`bottomL`, `topL`, parsed by `from_bytes`'s closure from cursors `4` and
`1204`) and the keys' indices (`li`, `li1`). The `u32` of a word's first four bytes
(`u32Bytes_toUInt32`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

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

@[expose] public section

/-! ## The path fold, a level at a time -/

/-- `path_fold`'s step at level `z`: the node above of `current` and the path's sibling. -/
def pfStep (pp : List UInt8) (layer e : Nat) (path : List (List UInt8)) (current : List UInt8)
    (z : Nat) : List UInt8 :=
  node pp layer (z + 1) (e >>> (z + 1)).toUInt32
    (if e >>> z &&& 1 = 0 then current ++ path.getD z [] else path.getD z [] ++ current)

/-- `path_fold` after its first `z` levels. -/
def pf (pp : List UInt8) (layer e : Nat) (path : List (List UInt8)) (leaf : List UInt8)
    (z : Nat) : List UInt8 :=
  (List.range z).foldl (pfStep pp layer e path) leaf

theorem pf_zero (pp : List UInt8) (layer e : Nat) (path : List (List UInt8)) (leaf : List UInt8) :
    pf pp layer e path leaf 0 = leaf := rfl

theorem pf_succ (pp : List UInt8) (layer e : Nat) (path : List (List UInt8)) (leaf : List UInt8)
    (z : Nat) : pf pp layer e path leaf (z + 1) = pfStep pp layer e path (pf pp layer e path leaf z) z := by
  rw [pf, List.range_succ, List.foldl_append]
  rfl

/-- **`layer_root`'s path fold** is the fold after its 16 levels. -/
theorem pathFold_eq (pp : List UInt8) (layer e : Nat) (path : List (List UInt8))
    (leaf : List UInt8) (hp : path.length = 16) :
    NativeRustc.Keccak.pathFold leaf e path (fun level j children => node pp layer level j.toUInt32 children) =
      pf pp layer e path leaf 16 := by
  rw [NativeRustc.Keccak.pathFold, hp]
  rfl

theorem length_path {bs : List UInt8} {c : Nat} : (takeLayer bs c).1.path.length = 16 := by
  simp [takeLayer]

theorem length_hashBytes (input : List UInt8) : (NativeRustc.Keccak.hashBytes input).length = 32 := by
  rw [NativeRustc.Keccak.hashBytes,
    show digestBytes (keccak256 input) = Native.Keccak.wordsBytes (keccak256 input).toList from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  simp

theorem length_th (pp : List UInt8) (tw : Tweak) (payload : List UInt8) :
    (th pp tw payload).length = 16 := by
  rw [th, List.length_take, NativeRustc.Keccak.hashBytes,
    show digestBytes (keccak256 (pp ++ address tw ++ payload)) =
      Native.Keccak.wordsBytes (keccak256 (pp ++ address tw ++ payload)).toList from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  simp

theorem length_pf (pp : List UInt8) (layer e : Nat) (path : List (List UInt8)) {leaf : List UInt8}
    (hl : leaf.length = 16) (z : Nat) : (pf pp layer e path leaf z).length = 16 := by
  cases z with
  | zero => exact hl
  | succ z => rw [pf_succ, pfStep, node, length_th]

/-- **A one-time leaf's codeword and leaf**: 58 digits, 16 bytes. -/
theorem wotsLeaf_length {pp : List UInt8} {layer : Nat} {e : UInt32}
    {message randomizer : List UInt8} {values : List (List UInt8)} {x leaf : List UInt8}
    (h : wotsLeaf pp layer e message randomizer values = some (x, leaf)) :
    x.length = 58 ∧ leaf.length = 16 := by
  unfold wotsLeaf at h
  split at h
  · cases h
  · rename_i x' hx
    cases h
    unfold codeword at hx
    split at hx
    · cases hx
      exact ⟨by simp [digits], by rw [wotsLeafHash, length_th]⟩
    · cases hx

end

end NativeRustcX64.Xmss.XmssVerify
