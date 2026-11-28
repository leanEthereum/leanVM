module

public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Arrays.Read

/-!
# Pushing onto a `Buf<u64, N>`

`BufWordsAt.push`: the entry written after the others and the count word bumped, the rest kept.
-/

namespace NativeRustcVm

@[expose] public section

/-- The address of entry `i` of the `Buf` at `p`. -/
abbrev bufSlot (p : BitVec 64) (i : Nat) : BitVec 64 := p + BitVec.ofNat 64 (8 + 8 * i)

/-- **A push**: entry `xs.length` and the count word written, nothing else of the buffer. -/
theorem BufWordsAt.push {d d' : Mem 64} {p : BitVec 64} {N : Nat} {xs : List UInt64} {w : UInt64}
    (h : BufWordsAt d p N xs) (hlt : xs.length < N) (hnw : NoWrap p (8 + 8 * N))
    (hc : WordAt d' p (xs.length + 1).toUInt64) (hw : WordAt d' (bufSlot p xs.length) w)
    (hs : SameOutside d d' fun q ↦ InRange p 8 q ∨ InRange (bufSlot p xs.length) 8 q) :
    BufWordsAt d' p N (xs ++ [w]) := by
  obtain ⟨-, -, hws⟩ := h
  refine ⟨by simp; omega, by simpa using hc, ?_⟩
  rw [wordsAt_append_iff]
  have hb := hws.of_sameOutside hs fun i hi hq ↦ by
    rw [length_wordsBytes] at hi
    unfold NoWrap at hnw
    rw [addr_add_add] at hq
    rcases hq with hq | hq
    · rw [inRange_iff (by unfold NoWrap; omega), toNat_add_ofNat (by omega)] at hq
      omega
    · rw [inRange_iff (by unfold NoWrap; rw [toNat_add_ofNat (by omega)]; omega),
        toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at hq
      omega
  refine ⟨hb, ?_⟩
  rw [wordsAt_singleton_iff, addr_add_add]
  exact hw

/-- **A buffer no change touches** is kept. -/
theorem BufWordsAt.of_sameOutside {d d' : Mem 64} {p : BitVec 64} {N : Nat} {xs : List UInt64}
    {R : BitVec 64 → Prop} (h : BufWordsAt d p N xs) (hs : SameOutside d d' R)
    (hR : ∀ q, R q → ¬InRange p (8 + 8 * N) q) (hnw : NoWrap p (8 + 8 * N)) :
    BufWordsAt d' p N xs := by
  obtain ⟨hl, hc, hws⟩ := h
  have hin : ∀ i < 8 + 8 * N, InRange p (8 + 8 * N) (p + BitVec.ofNat 64 i) := fun i hi ↦
    inRange_add hi (by unfold NoWrap at hnw; omega)
  refine ⟨hl, hc.of_sameOutside hs fun i hi hq ↦ hR _ hq (hin i (by
    rw [length_wordBytes] at hi; omega)), hws.of_sameOutside hs fun i hi hq ↦ hR _ hq ?_⟩
  rw [length_wordsBytes] at hi
  rw [addr_add_add]
  exact hin _ (by omega)

end

end NativeRustcVm
