module

public import NativeRustcArm.XmssVerify.Frame

/-!
# `xmss_verify`: a layer's bytes in the frame

A layer parsed at cursor `c` of the signature's bytes, laid out as `LayerSignature.memBytes`:
its path's node `z` at `16 z` (`layer_path`), its chain values from `256` (`layer_values`), its
randomizer at `1184` (`layer_rand`).
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustc NativeRustc.Xmss

public section

variable {w : Nat → UInt64} {c z : Nat} {d : DataMem} {a : BitVec 64}

theorem length_path_flatten (hc : c + 1200 ≤ 2404) :
    (takeLayer (sigB w) c).1.path.flatten.length = 256 :=
  length_flatten_range 16 (f := fun j => slice (sigB w) (c + 944 + 16 * j) 16) (s := 16)
    fun _ _ => length_slice (by rw [length_sigB]; omega)

theorem length_values_flatten (hc : c + 1200 ≤ 2404) :
    (takeLayer (sigB w) c).1.chainValues.flatten.length = 928 :=
  length_flatten_range 58 (f := fun j => slice (sigB w) (c + 16 + 16 * j) 16) (s := 16)
    fun _ _ => length_slice (by rw [length_sigB]; omega)

theorem length_path (w : Nat → UInt64) (c : Nat) : (takeLayer (sigB w) c).1.path.length = 16 := by
  simp [takeLayer]

theorem path_getD (hz : z < 16) :
    (takeLayer (sigB w) c).1.path.getD z [] = slice (sigB w) (c + 944 + 16 * z) 16 := by
  simp [takeLayer, List.getD_eq_getElem?_getD, hz]

theorem length_path_getD (hc : c + 1200 ≤ 2404) (hz : z < 16) :
    ((takeLayer (sigB w) c).1.path.getD z []).length = 16 := by
  rw [path_getD hz]
  exact length_slice (by rw [length_sigB]; omega)

/-- **A path node's bytes.** -/
theorem layer_path (hc : c + 1200 ≤ 2404) (h : BytesAt d a (takeLayer (sigB w) c).1.memBytes)
    {z : Nat} (hz : z < 16) :
    BytesAt d (a + BitVec.ofNat 64 (16 * z)) ((takeLayer (sigB w) c).1.path.getD z []) := by
  rw [path_getD hz]
  exact bytesAt_flatten_piece 16 (f := fun j => slice (sigB w) (c + 944 + 16 * j) 16) (s := 16)
    (fun _ _ => length_slice (by rw [length_sigB]; omega)) h.left.left z hz

/-- **The chain values**, 16 bytes each from `256`. -/
theorem layer_values (hc : c + 1200 ≤ 2404) (h : BytesAt d a (takeLayer (sigB w) c).1.memBytes) :
    (List.range 58).map (fun i => bytesOf d (a + BitVec.ofNat 64 256 + BitVec.ofNat 64 (16 * i)) 16) =
      (takeLayer (sigB w) c).1.chainValues := by
  have hv := h.left.right
  rw [length_path_flatten hc] at hv
  show _ = (List.range 58).map (fun j => slice (sigB w) (c + 16 + 16 * j) 16)
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact bytesOf_of (bytesAt_flatten_piece 58 (f := fun j => slice (sigB w) (c + 16 + 16 * j) 16)
    (s := 16) (fun _ _ => length_slice (by rw [length_sigB]; omega)) hv i hi)
    (length_slice (by rw [length_sigB]; omega))

/-- **The randomizer**, at `1184`. -/
theorem layer_rand (hc : c + 1200 ≤ 2404) (h : BytesAt d a (takeLayer (sigB w) c).1.memBytes) :
    BytesAt d (a + BitVec.ofNat 64 1184) (takeLayer (sigB w) c).1.randomizer := by
  have hr := h.right
  rwa [List.length_append, length_path_flatten hc, length_values_flatten hc] at hr

theorem length_rand (hc : c + 1200 ≤ 2404) : (takeLayer (sigB w) c).1.randomizer.length = 16 :=
  length_slice (by rw [length_sigB]; omega)

end

end NativeRustcArm.Xmss.XmssVerify
