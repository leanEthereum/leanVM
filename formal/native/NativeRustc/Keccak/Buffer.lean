module

public import NativeRustc.Keccak.Hasher

/-!
# Inlined hashers: buffered bytes and short inputs

Where rustc inlines a `Hasher`'s `update` and `finalize` into a function, a turn of `update`'s
loop that leaves room in the buffer copies its bytes after the buffered ones and advances
`buf_len` (`updateStep_short`, `holds_buffer`); and the Keccak-256 of an input shorter than a block
is the padded input absorbed into the zero state (`hashBytes_short`).
-/

@[expose] public section

namespace NativeRustc.Keccak

private theorem if_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

open LeanVM.Protocol.KeccakHash Native.Keccak

/-- **A turn of `update`'s loop that leaves room**: the bytes `c` after the `a.length % 136`
buffered ones, `buf_len` advanced, the input consumed. -/
theorem updateStep_short {h a c : List UInt8} (hh : HasherHolds h a)
    (hc : a.length % 136 + c.length < 136) :
    updateStep h c = (writeAt (writeAt h (200 + a.length % 136) c) 336
      (wordBytes (a.length % 136 + c.length).toUInt64), []) := by
  have hbl := bufLen_of_holds hh
  have hmin : min (136 - a.length % 136) c.length = c.length := by omega
  simp only [updateStep, hbl, hmin, List.take_length, List.drop_length]
  rw [if_neg' (show ¬(a.length % 136 + c.length = 136) by omega)]

/-- **Buffering bytes**: a hasher that absorbed `a`, with `c` copied after the buffered bytes and
`buf_len` advanced, without filling the buffer, has absorbed `a ++ c`. -/
theorem holds_buffer {h a c : List UInt8} (hh : HasherHolds h a)
    (hc : a.length % 136 + c.length < 136) :
    HasherHolds (writeAt (writeAt h (200 + a.length % 136) c) 336
      (wordBytes (a.length % 136 + c.length).toUInt64)) (a ++ c) := by
  by_cases hc0 : c = []
  · subst hc0
    have hlen := length_of_holds hh
    have hbl := bufLen_of_holds hh
    obtain ⟨rest, hr, rfl⟩ := hh
    rw [List.append_nil, List.length_nil, Nat.add_zero]
    refine ⟨rest, hr, ?_⟩
    have hT : (a.drop (136 * (a.length / 136))).length = a.length % 136 := by simp; omega
    have hw0 : ∀ (l : List UInt8) (o : Nat), writeAt l o [] = l := fun l o => by
      rw [writeAt, List.append_nil, List.length_nil, Nat.add_zero, List.take_append_drop]
    rw [hw0, ← List.append_assoc, ← List.append_assoc,
      writeAt_append_end _ _ _ (by simp [length_stateBytes, hT, hr]; omega)
        (by simp [length_wordBytes])]
  · obtain ⟨k, _, hk, hrest, hh'⟩ := holds_updateStep hh hc0
    rw [updateStep_short hh hc] at hrest hh'
    have hkc : k = c.length := by
      by_contra hne
      have := congrArg List.length hrest
      simp at this
      omega
    rw [hkc, List.take_length] at hh'
    exact hh'

/-- The zero state's bytes. -/
theorem stateBytes_zero : stateBytes (Vector.replicate 25 0) = List.replicate 200 0 := by
  rw [stateBytes, Vector.toList_replicate, wordsBytes_replicate_zero]

/-- **Keccak-256 of a short input**: its padded block absorbed into the zero state, the first 32
bytes. -/
theorem hashBytes_short {d : List UInt8} (h : d.length < 136) :
    hashBytes d = (keccakF (xorBlock (List.replicate 200 0) (finalBlock d))).take 32 := by
  have hd : d.length / 136 = 0 := Nat.div_eq_of_lt h
  rw [hashBytes, ← digestOf_absorb_sponge, hd, Nat.mul_zero, List.drop_zero,
    show sponge d = Vector.replicate 25 0 by rw [sponge, hd]; rfl, ← absorb_stateBytes,
    stateBytes_zero, finalBlock_eq_padBlock]
  rfl

end NativeRustc.Keccak
