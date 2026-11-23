module

public import NativeVm.Equiv.Field

/-!
# `eq_kernel` in place

rustc's `eq_kernel` computes `eqKernel point` in `out` in place: before coordinate `i` the first
`2^i` entries are `K = eqKernel (point.take i)` (`eqKernel_take_succ`: the next is
`K.map (· * (1 + r)) ++ K.map (· * r)`); a pair `j` stores `hi = K[j]·r` at `2^i + j`, then
`lo + hi = K[j]·(1 + r)` (`mul_one_add`) at `j`. After `j` pairs the two halves are `half1 K r j`
and `(K.take j).map (· * r)` (`half1_succ`).
-/

namespace NativeRustcVm

open NativeVm.Model NativeVm.Equiv

@[expose] public section

/-- `x·(1 + r) = x + x·r` in `E`. -/
theorem mul_one_add (x r : EW) : x * (1 + r) = x + x * r := by
  rw [← EW.toE_inj]
  simp [mul_add]

/-- The kernel's size. -/
theorem size_eqKernel (point : Array EW) : (eqKernel point).size = 2 ^ point.size := by
  rw [eqKernel, ← Array.foldl_toList]
  suffices h : ∀ (l : List EW) (out : Array EW),
      (l.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).size =
        out.size * 2 ^ l.length by
    rw [h]; simp
  intro l
  induction l with
  | nil => intro out; simp
  | cons r l ih =>
    intro out
    rw [List.foldl_cons, ih]
    simp [Nat.pow_succ]
    ring

/-- The kernel of the first `i + 1` coordinates. -/
theorem eqKernel_take_succ (point : List EW) {i : Nat} (h : i < point.length) :
    (eqKernel (point.take (i + 1)).toArray).toList =
      (eqKernel (point.take i).toArray).toList.map (· * (1 + point[i])) ++
        (eqKernel (point.take i).toArray).toList.map (· * point[i]) := by
  rw [eqKernel, eqKernel, ← Array.foldl_toList, ← Array.foldl_toList, List.toList_toArray,
    List.toList_toArray, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil, Array.toList_append, Array.toList_map,
    Array.toList_map]

/-- The low half after `j` pairs. -/
def half1 (K : List EW) (r : EW) (j : Nat) : List EW :=
  (K.take j).map (· * (1 + r)) ++ K.drop j

theorem length_half1 (K : List EW) (r : EW) (j : Nat) : (half1 K r j).length = K.length := by
  simp [half1]; omega

theorem half1_zero (K : List EW) (r : EW) : half1 K r 0 = K := by simp [half1]

theorem half1_len (K : List EW) (r : EW) : half1 K r K.length = K.map (· * (1 + r)) := by
  simp [half1]

/-- After `j` pairs, around entry `j`. -/
theorem half1_split (K : List EW) (r : EW) {j : Nat} (h : j < K.length) :
    half1 K r j = (K.take j).map (· * (1 + r)) ++ ([K[j]] ++ K.drop (j + 1)) := by
  unfold half1
  congr 1
  rw [List.singleton_append, List.drop_eq_getElem_cons h]

/-- After `j + 1` pairs, around entry `j`. -/
theorem half1_succ_split (K : List EW) (r : EW) {j : Nat} (h : j < K.length) :
    half1 K r (j + 1) = (K.take j).map (· * (1 + r)) ++ ([K[j] + K[j] * r] ++ K.drop (j + 1)) := by
  unfold half1
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append,
    List.map_singleton, mul_one_add, List.append_assoc]

/-- The high half after `j + 1` pairs. -/
theorem half2_succ (K : List EW) (r : EW) {j : Nat} (h : j < K.length) :
    (K.take (j + 1)).map (· * r) = (K.take j).map (· * r) ++ [K[j] * r] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append,
    List.map_singleton]

end

end NativeRustcVm
