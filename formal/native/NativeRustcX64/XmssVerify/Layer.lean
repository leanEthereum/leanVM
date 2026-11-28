module

public import NativeRustcX64.XmssVerify.Parse

/-!
# A layer's bytes in memory (x86-64)

A layer's 1200 bytes as `from_bytes`'s closure lays it out (`LayerSignature.memBytes`): its path's
node `j` at `16 j`, its chain value `i` at `256 + 16 i`, its randomizer at `1184`
(`layer_path`, `layer_value`, `layer_rnd`); a pointer stored as a value's 8 bytes (`ptrAt_of`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc.Xmss

public section

/-- Bytes of a list from an index. -/
theorem bytesAt_sub {d : DataMem} {a : BitVec 64} {bs ys : List UInt8} (h : BytesAt d a bs)
    {k : Nat} (hy : ∀ t (ht : t < ys.length), bs[k + t]? = some ys[t]) :
    BytesAt d (a + BitVec.ofNat 64 k) ys := by
  intro t ht
  have := hy t ht
  rw [List.getElem?_eq_some_iff] at this
  obtain ⟨hl, he⟩ := this
  rw [addr_add_addr, h (k + t) hl, he]

/-- A flattening of 16-byte pieces. -/
theorem length_flatten16 (f : Nat → List UInt8) :
    ∀ (n : Nat), (∀ j < n, (f j).length = 16) → (((List.range n).map f).flatten).length = 16 * n
  | 0, _ => rfl
  | n + 1, hf => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
      length_flatten16 f n (fun j hj => hf j (by omega))]
    simp [hf n (by omega)]
    omega

/-- Element `16 j + t` of a flattening of 16-byte pieces. -/
theorem getElem?_flatten16 (f : Nat → List UInt8) :
    ∀ (n : Nat), (∀ j < n, (f j).length = 16) → ∀ j < n, ∀ t < 16,
      ((List.range n).map f).flatten[16 * j + t]? = (f j)[t]?
  | 0, _, j, hj, _, _ => absurd hj (by omega)
  | n + 1, hf, j, hj, t, ht => by
    rw [List.range_succ, List.map_append, List.flatten_append]
    have hl := length_flatten16 f n (fun j hj => hf j (by omega))
    by_cases hjn : j < n
    · rw [List.getElem?_append_left (by omega)]
      exact getElem?_flatten16 f n (fun j hj => hf j (by omega)) j hjn t ht
    · obtain rfl : j = n := by omega
      rw [List.getElem?_append_right (by omega), hl]
      simp [show 16 * j + t - 16 * j = t by omega]

variable {bs : List UInt8} {c : Nat} (hc : c + 1200 ≤ bs.length)
include hc

theorem slice_length' {o : Nat} (ho : o + 16 ≤ 1200) :
    (NativeRustc.slice bs (c + o) 16).length = 16 :=
  length_slice (by omega)

theorem length_pathFlat :
    (takeLayer bs c).1.path.flatten.length = 256 := by
  simp only [takeLayer]
  rw [length_flatten16 _ 16 fun j hj => by
    rw [show c + 944 + 16 * j = c + (944 + 16 * j) by omega]; exact slice_length' hc (by omega)]

theorem length_valuesFlat :
    (takeLayer bs c).1.chainValues.flatten.length = 928 := by
  simp only [takeLayer]
  rw [length_flatten16 _ 58 fun j hj => by
    rw [show c + 16 + 16 * j = c + (16 + 16 * j) by omega]; exact slice_length' hc (by omega)]

/-- **A path node's bytes** in a layer's. -/
theorem layer_path {d : DataMem} {a : BitVec 64}
    (h : BytesAt d a (takeLayer bs c).1.memBytes) {j : Nat} (hj : j < 16) :
    BytesAt d (a + BitVec.ofNat 64 (16 * j)) ((takeLayer bs c).1.path.getD j []) := by
  refine bytesAt_sub h fun t ht => ?_
  have hpj : (takeLayer bs c).1.path.getD j [] = NativeRustc.slice bs (c + 944 + 16 * j) 16 := by
    simp [takeLayer, List.getD_eq_getElem?_getD, hj]
  have ht' := ht
  rw [hpj, show c + 944 + 16 * j = c + (944 + 16 * j) by omega, slice_length' hc (by omega)] at ht'
  rw [← List.getElem?_eq_getElem, hpj, LayerSignature.memBytes, List.append_assoc,
    List.getElem?_append_left (by rw [length_pathFlat hc]; omega)]
  simp only [takeLayer]
  rw [getElem?_flatten16 _ 16 (fun j hj => by
    rw [show c + 944 + 16 * j = c + (944 + 16 * j) by omega]; exact slice_length' hc (by omega))
    j hj t ht']

/-- **A chain value's bytes** in a layer's. -/
theorem layer_value {d : DataMem} {a : BitVec 64}
    (h : BytesAt d a (takeLayer bs c).1.memBytes) {i : Nat} (hi : i < 58) :
    BytesAt d (a + BitVec.ofNat 64 (256 + 16 * i)) ((takeLayer bs c).1.chainValues.getD i []) := by
  refine bytesAt_sub h fun t ht => ?_
  have hpj : (takeLayer bs c).1.chainValues.getD i [] =
      NativeRustc.slice bs (c + 16 + 16 * i) 16 := by
    simp [takeLayer, List.getD_eq_getElem?_getD, hi]
  have ht' := ht
  rw [hpj, show c + 16 + 16 * i = c + (16 + 16 * i) by omega, slice_length' hc (by omega)] at ht'
  rw [← List.getElem?_eq_getElem, hpj, LayerSignature.memBytes, List.append_assoc,
    List.getElem?_append_right (by rw [length_pathFlat hc]; omega), length_pathFlat hc,
    List.getElem?_append_left (by rw [length_valuesFlat hc]; omega)]
  simp only [takeLayer]
  rw [show 256 + 16 * i + t - 256 = 16 * i + t by omega,
    getElem?_flatten16 _ 58 (fun j hj => by
      rw [show c + 16 + 16 * j = c + (16 + 16 * j) by omega]; exact slice_length' hc (by omega))
    i hi t ht']

/-- **The randomizer's bytes** in a layer's. -/
theorem layer_rnd {d : DataMem} {a : BitVec 64}
    (h : BytesAt d a (takeLayer bs c).1.memBytes) :
    BytesAt d (a + BitVec.ofNat 64 1184) (takeLayer bs c).1.randomizer := by
  refine bytesAt_sub h fun t ht => ?_
  rw [← List.getElem?_eq_getElem, LayerSignature.memBytes, List.append_assoc,
    List.getElem?_append_right (by rw [length_pathFlat hc]; omega), length_pathFlat hc,
    List.getElem?_append_right (by rw [length_valuesFlat hc]; omega), length_valuesFlat hc,
    show 1184 + t - 256 - 928 = t by omega]

end

public section

/-- A pointer stored as a value's 8 bytes. -/
theorem ptrAt_of {d : DataMem} {a x : BitVec 64} (h : BytesAt d a (regBytes x)) :
    ptrAt d a = x := by
  unfold ptrAt
  rw [Sym.loadInt_of_get? d a 8 (fun i => (regBytes x).getD i 0) fun i hi => by
    rw [h i (by rw [length_regBytes]; exact hi)]
    simp [List.getD_eq_getElem?_getD, show i < (regBytes x).length by
      rw [length_regBytes]; exact hi]]
  rw [Option.getD_some]
  have : (List.range 8).map (fun i => (regBytes x).getD i 0) = regBytes x := by
    apply List.ext_getElem (by simp [length_regBytes])
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h2]
  rw [this, ofBytes_regBytes]

end

end NativeRustcX64.Xmss.XmssVerify
