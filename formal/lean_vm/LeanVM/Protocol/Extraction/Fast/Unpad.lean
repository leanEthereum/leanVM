module

public import LeanVM.Protocol.Extraction.Extractor
public import Common.Lanes
public import Common.Sponge

/-!
# Unpadding in one pass

The statement's `keccakUnpadded bs` tries the `136` prefixes of `bs` short of `1` to `136` bytes,
padding each and comparing with `bs`: about `3·136·|bs|` byte operations. `keccakUnpaddedFast`
strips the padding once (`Common.stripPad`: the trailing zeros and the padding's two bytes), pads
the result and compares: about `3·|bs|`.

* **`keccakUnpaddedFast_eq`**: `keccakUnpaddedFast bs = keccakUnpadded bs`, on every input.

The padding lemmas (`length_keccakPadded`, `keccakPadded_take_length`,
`keccakPadBytes_eq_keccakPadded`) are `Protocol/Rpm/Paths.lean`'s (`length_padded`,
`padded_prefix`, `keccakPadBytes_eq_padded`), restated in the module system.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile Common

public section

/-- **`keccakUnpadded`, in one pass**: strip the padding, pad the result back, compare. -/
@[expose] def keccakUnpaddedFast (bs : Bytes) : Option Bytes :=
  let m := stripPad bs
  if keccakPadded m = bs then some m else none

theorem length_keccakPadded (m : Bytes) :
    (keccakPadded m).length = 136 * (m.length / 136 + 1) := by
  simp only [keccakPadded, rate, List.length_append, List.length_take]
  rw [LeanVM.Rpm.length_padBlock _ (by simp only [List.length_drop]; omega)]
  rw [Nat.min_eq_left (Nat.mul_div_le _ _)]
  ring

theorem padBlock_take_length (rest : Bytes) (h : rest.length < 136) :
    (padBlock rest).take rest.length = rest := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take]
  split_ifs with hj
  · simp [padBlock, List.getElem?_append_left hj,
      show rest.length ≠ j by omega, show (136 : ℕ) - 1 ≠ j by omega, rate]
  · rw [List.getElem?_eq_none (by omega)]

theorem keccakPadded_take_length (m : Bytes) : (keccakPadded m).take m.length = m := by
  have hk : 136 * (m.length / 136) ≤ m.length := Nat.mul_div_le _ _
  simp only [keccakPadded, rate]
  rw [List.take_append, List.take_of_length_le (by simp), List.length_take,
    Nat.min_eq_left hk,
    show m.length - 136 * (m.length / 136) = (m.drop (136 * (m.length / 136))).length by simp,
    padBlock_take_length _ (by simp; omega), List.take_append_drop]

theorem keccakPadBytes_eq_keccakPadded (m : Bytes) : keccakPadBytes m = keccakPadded m := by
  induction h : m.length / 136 generalizing m with
  | zero =>
    have hl : m.length < 136 := by omega
    rw [LeanVM.Rpm.keccakPadBytes_eq_padBlock m hl]
    simp [keccakPadded, rate, h]
  | succ n ih =>
    have hl : 136 ≤ m.length := by omega
    have hd : (m.drop 136).length / 136 = n := by rw [List.length_drop]; omega
    rw [LeanVM.Rpm.keccakPadBytes_of_le m hl, ih _ hd]
    simp only [keccakPadded, rate, h, hd]
    rw [show 136 * (n + 1) = 136 + 136 * n by ring, List.take_add, List.drop_drop,
      List.append_assoc]

/-- Stripping the padding of `keccakPadded m` gives `m`. -/
theorem stripPad_keccakPadded (m : Bytes) : stripPad (keccakPadded m) = m := by
  rw [← keccakPadBytes_eq_keccakPadded, stripPad_keccakPadBytes]

/-- **One pass unpads as the statement does.** -/
theorem keccakUnpaddedFast_eq (bs : Bytes) : keccakUnpaddedFast bs = keccakUnpadded bs := by
  rw [keccakUnpaddedFast]
  split <;> rename_i h
  · -- `m = stripPad bs` pads to `bs`: it is among the statement's candidates, and the first
    -- candidate that pads to `bs` is `m` (the padding is injective).
    symm
    have hlen := length_keccakPadded (stripPad bs)
    rw [h] at hlen
    have hlt : (stripPad bs).length < bs.length := by rw [hlen]; omega
    have hle : bs.length ≤ (stripPad bs).length + 136 := by rw [hlen]; omega
    have hmem : stripPad bs ∈ (List.range rate).map fun k ↦ bs.take (bs.length - 1 - k) := by
      refine List.mem_map.mpr ⟨bs.length - 1 - (stripPad bs).length, List.mem_range.mpr ?_, ?_⟩
      · simp only [rate]
        omega
      · rw [show bs.length - 1 - (bs.length - 1 - (stripPad bs).length) = (stripPad bs).length by
          omega]
        have ht := keccakPadded_take_length (stripPad bs)
        rwa [h] at ht
    obtain ⟨m', hm'⟩ : ∃ m', keccakUnpadded bs = some m' :=
      Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨_, hmem, by simp [h]⟩)
    have h' := List.find?_some hm'
    simp only [decide_eq_true_eq] at h'
    rw [hm', ← h', stripPad_keccakPadded]
  · -- no message pads to `bs`: if one did, stripping `bs` would give it.
    symm
    rw [keccakUnpadded, List.find?_eq_none]
    intro c _ hc
    simp only [decide_eq_true_eq] at hc
    apply h
    rw [← hc, stripPad_keccakPadded]

theorem keccakUnpaddedFast_eq_fun : keccakUnpaddedFast = keccakUnpadded :=
  funext keccakUnpaddedFast_eq

end

end LeanVM.Extraction.Fast
