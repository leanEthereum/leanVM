module

public import NativeRustcArm.XmssVerify.Model

/-!
# `xmss_verify`'s model: a layer's path step by step

`pathFold` of a layer as `n` steps (`fold`, `fold_succ`), each `pathStep`: the node above the
current one and its sibling. A layer's root (`layerRoot_eq`). The lengths of a hash, a node, a
`wots_leaf` result. The bottom address's `hi` bytes as the machine code stores them
(`hiBytes_bottom`), and the key indices (`li_toNat`, `li1_toNat`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustc NativeRustc.Xmss NativeRustc.Keccak LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- The path step at level `z`: the node above `current` and its sibling. -/
def pathStep (pp : List UInt8) (layer e : Nat) (path : List (List UInt8)) (current : List UInt8)
    (z : Nat) : List UInt8 :=
  node pp layer (z + 1) (e >>> (z + 1)).toUInt32
    (if e >>> z &&& 1 = 0 then current ++ path.getD z [] else path.getD z [] ++ current)

/-- `n` path steps from the leaf. -/
def fold (pp : List UInt8) (layer e : Nat) (path : List (List UInt8)) (leaf : List UInt8)
    (n : Nat) : List UInt8 :=
  (List.range n).foldl (pathStep pp layer e path) leaf

end

public section

variable {pp : List UInt8} {layer e : Nat} {path : List (List UInt8)} {leaf : List UInt8}

theorem fold_zero : fold pp layer e path leaf 0 = leaf := rfl

theorem fold_succ (n : Nat) :
    fold pp layer e path leaf (n + 1) = pathStep pp layer e path (fold pp layer e path leaf n) n := by
  simp only [fold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A layer's root: its leaf, then the path's steps. -/
theorem layerRoot_eq (pp : List UInt8) (layer : Nat) (e : UInt32) (msg : List UInt8)
    (sig : LayerSignature) :
    layerRoot pp layer e msg sig = (wotsLeaf pp layer e msg sig.randomizer sig.chainValues).map
      fun xl => (xl.1, fold pp layer e.toNat sig.path xl.2 sig.path.length) := by
  unfold layerRoot
  cases wotsLeaf pp layer e msg sig.randomizer sig.chainValues with
  | none => rfl
  | some xl => rfl

theorem length_hashBytes (input : List UInt8) : (hashBytes input).length = 32 := by
  rw [hashBytes, show digestBytes (keccak256 input) = wordsBytes (keccak256 input).toList from rfl,
    Proof.length_wordsBytes]
  simp

theorem length_th (pp : List UInt8) (tw : Tweak) (payload : List UInt8) :
    (th pp tw payload).length = 16 := by
  rw [th, List.length_take, length_hashBytes]
  decide

theorem length_pathStep (cur : List UInt8) (z : Nat) :
    (pathStep pp layer e path cur z).length = 16 :=
  length_th _ _ _

theorem length_fold (h : leaf.length = 16) (n : Nat) : (fold pp layer e path leaf n).length = 16 := by
  cases n with
  | zero => exact h
  | succ n => rw [fold_succ]; exact length_pathStep _ _

/-- A path step's node: the first 16 bytes of the hash of the public parameter, the address and
the children. -/
theorem pathStep_eq (cur : List UInt8) (z : Nat) :
    pathStep pp layer e path cur z =
      (hashBytes (pp ++ address (tweak 3 (layerHi layer (z + 1).toUInt32) (e >>> (z + 1)).toUInt32) ++
        (if e >>> z &&& 1 = 0 then cur ++ path.getD z [] else path.getD z [] ++ cur))).take 16 :=
  rfl

/-- `wots_leaf`'s result: the codeword's 58 digits and the 16 bytes of the leaf. -/
theorem wotsLeaf_some {pp : List UInt8} {layer : Nat} {e : UInt32} {msg r : List UInt8}
    {vals : List (List UInt8)} {x lf : List UInt8} (h : wotsLeaf pp layer e msg r vals = some (x, lf)) :
    x.length = 58 ∧ lf.length = 16 := by
  unfold wotsLeaf at h
  split at h
  · cases h
  · rename_i x' hx
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold codeword at hx
    split at hx
    · cases hx
      exact ⟨by simp [digits], length_th _ _ _⟩
    · cases hx

/-- A layer's root is 16 bytes. -/
theorem layerRoot_length {pp : List UInt8} {layer : Nat} {e : UInt32} {msg : List UInt8}
    {sig : LayerSignature} {x r : List UInt8} (h : layerRoot pp layer e msg sig = some (x, r)) :
    r.length = 16 := by
  rw [layerRoot_eq] at h
  cases hW : wotsLeaf pp layer e msg sig.randomizer sig.chainValues with
  | none =>
    rw [hW] at h
    cases h
  | some xl =>
    obtain ⟨x', lf⟩ := xl
    rw [hW] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact length_fold (wotsLeaf_some hW).2 _

/-- The address's `hi` bytes of a bottom node at level `z + 1`. -/
theorem hiBytes_bottom : ∀ z < 16,
    [UInt8.ofNat (z + 1), UInt8.ofNat ((z + 1) / 256), UInt8.ofNat ((z + 1) % 2 ^ 32 / 2 ^ 16)] =
      (u32Bytes (layerHi 0 (z + 1).toUInt32)).take 3 := by
  decide +kernel

/-- The bottom layer's key index. -/
theorem li_toNat (w : Nat → UInt64) : (li w).toNat = (w 8).toNat % 2 ^ 32 := by
  rw [li, UInt64.toNat_toUInt32]

/-- The top layer's key index. -/
theorem li1_toNat (w : Nat → UInt64) : (li1 w).toNat = (w 8).toNat % 2 ^ 32 / 2 ^ 16 := by
  rw [li1, layerIndex, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64,
    li_toNat, Nat.shiftRight_eq_div_pow]
  have : (w 8).toNat % 2 ^ 32 / 2 ^ 16 < 2 ^ 32 := by omega
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  norm_num
  omega

end

end NativeRustcArm.Xmss.XmssVerify
