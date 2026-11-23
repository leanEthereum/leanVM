module

public import NativeRustcVm.Wire.Rep
public import NativeRustcVm.MemLemmas

/-!
# The reader in memory

A reader determines its bytes and cursor (`ReaderAt.unique`); it survives a change outside its
footprint (`ReaderAt.frame`) and a new cursor (`ReaderAt.update`).
-/

namespace NativeRustcVm.Wire

open NativeRustcVm.Transcript

public section

theorem ReaderAt.len_lt {d : Mem 64} {r bp : BitVec 64} {B : List UInt8} {c : Nat}
    (h : ReaderAt d r bp B c) : B.length < 2 ^ 64 := by
  have hn := h.noWrap
  have hr := h.ok.2
  unfold NoWrap at hn hr
  by_cases h0 : 0 < B.length
  · have := h.apart h0
    unfold Apart at this
    omega
  · omega

theorem toNat_toUInt64_of_lt {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- **A reader determines** its bytes' address, its bytes and its cursor. -/
theorem ReaderAt.unique {d : Mem 64} {r bp bp' : BitVec 64} {B B' : List UInt8} {c c' : Nat}
    (h : ReaderAt d r bp B c) (h' : ReaderAt d r bp' B' c') : bp' = bp ∧ B' = B ∧ c' = c := by
  have hp := h.ptr.unique h'.ptr
  have hl := h.len.unique h'.len
  have hc := h.cur.unique h'.cur
  have hL := h.len_lt
  have hL' := h'.len_lt
  have hlen : B'.length = B.length := by
    have := congrArg UInt64.toNat hl
    rwa [toNat_toUInt64_of_lt hL, toNat_toUInt64_of_lt hL', eq_comm] at this
  have hbp : bp' = bp := by
    have := congrArg UInt64.toBitVec hp
    exact this.symm
  subst hbp
  refine ⟨rfl, (h.bytes.unique h'.bytes hlen.symm).symm, ?_⟩
  have := congrArg UInt64.toNat hc
  rwa [toNat_toUInt64_of_lt (by have := h.c_le; omega),
    toNat_toUInt64_of_lt (by have := h'.c_le; omega), eq_comm] at this

/-- **A reader survives** a change of memory apart from it and its bytes. -/
theorem ReaderAt.frame {d d' : Mem 64} {r bp : BitVec 64} {B : List UInt8} {c : Nat}
    {R : BitVec 64 → Prop} (h : ReaderAt d r bp B c) (hs : SameOutside d d' R)
    (hr : ∀ i < 24, ¬R (r + BitVec.ofNat 64 i)) (hb : ∀ i < B.length, ¬R (bp + BitVec.ofNat 64 i)) :
    ReaderAt d' r bp B c := by
  have hr' : ∀ o n, o + n ≤ 24 → ∀ i < n, ¬R (r + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
    fun o n hon i hi ↦ by rw [addr_add_add]; exact hr _ (by omega)
  exact ⟨⟨h.ok.1.of_sameOutside hs hr, h.ok.2⟩,
    h.ptr.of_sameOutside hs fun i hi ↦ by
      have := hr' 0 8 (by omega) i (by simpa [length_wordBytes] using hi)
      rwa [addr_add_zero] at this,
    h.len.of_sameOutside hs fun i hi ↦ hr' 8 8 (by omega) i (by simpa [length_wordBytes] using hi),
    h.cur.of_sameOutside hs fun i hi ↦ hr' 16 8 (by omega) i (by simpa [length_wordBytes] using hi),
    h.bytes.of_sameOutside hs hb, h.noWrap, h.apart, h.c_le⟩

/-- **A new cursor**: the reader with the cursor word changed to `c' ≤ L`. -/
theorem ReaderAt.update {d d' : Mem 64} {r bp : BitVec 64} {B : List UInt8} {c c' : Nat}
    (h : ReaderAt d r bp B c) (hs : SameOutside d d' (curRegion r).Holds)
    (hc : WordAt d' (off r 16) c'.toUInt64) (hle : c' ≤ B.length) : ReaderAt d' r bp B c' := by
  have hnw := h.ok.2
  have hR : ∀ i < 24, i < 16 → ¬(curRegion r).Holds (r + BitVec.ofNat 64 i) := fun i hi h16 hin ↦
    not_inRange_sub (N := 24) (o := 16) (m := 8) hnw (by omega) hi (.inl h16) hin
  have hRb : ∀ i < B.length, ¬(curRegion r).Holds (bp + BitVec.ofNat 64 i) := fun i hi hin ↦ by
    have hap := h.apart (by omega)
    have hcur : InRange r 24 (bp + BitVec.ofNat 64 i) :=
      InRange.of_sub (o := 16) (m := 8) hin hnw (by omega)
    exact hap.symm.not_inRange_add h.noWrap hnw hi hcur
  refine ⟨⟨fun i hi ↦ ?_, hnw⟩, h.ptr.of_sameOutside hs fun i hi ↦ ?_,
    h.len.of_sameOutside hs fun i hi ↦ ?_, hc, h.bytes.of_sameOutside hs hRb, h.noWrap, h.apart, hle⟩
  · change i < 24 at hi
    by_cases h16 : i < 16
    · rw [hs _ (hR i hi h16)]; exact h.ok.1 i hi
    · have := hc.mapped (i - 16) (by omega)
      rwa [addr_add_add, show 16 + (i - 16) = i by omega] at this
  · simp only [length_wordBytes] at hi
    exact hR i (by omega) (by omega)
  · simp only [length_wordBytes] at hi
    rw [addr_add_add]
    exact hR _ (by omega) (by omega)

end

end NativeRustcVm.Wire
