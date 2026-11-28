module

public import NativeRustcVm.MemLemmas
public import NativeVm.Transcript.Layout
public import Native.Keccak.Words

/-!
# The word view and the byte memory

`NativeVm.Entry.EntryPre` describes memory as words (`UInt64 → Option UInt64`),
areas by `wd b k` (word `k` from `b`), `Fits` and `Disj`. With the word view of the byte memory
(`wordView d`) these are `WordsAt`, `Mapped`, `NoWrap` and `Apart` of the byte memory:
`wordsAt_of_wordView`, `mapped_of_wordView`, `noWrap_of_fits`, `apart_of_disj`.
-/

namespace NativeRustcVm

open NativeVm.Transcript

public section

theorem toBitVec_wd (b : UInt64) (k : Nat) :
    (wd b k).toBitVec = b.toBitVec + BitVec.ofNat 64 (8 * k) := by
  simp only [wd, UInt64.toBitVec_add]
  congr 1

theorem noWrap_of_fits {b : UInt64} {n : Nat} (h : Fits b n) : NoWrap b.toBitVec (8 * n) := h

theorem fits_of_noWrap {b : UInt64} {n : Nat} (h : NoWrap b.toBitVec (8 * n)) : Fits b n := h

theorem apart_of_disj {a b : UInt64} {n m : Nat} (h : Disj a n b m) :
    Apart a.toBitVec (8 * n) b.toBitVec (8 * m) := h

theorem disj_of_apart {a b : UInt64} {n m : Nat} (h : Apart a.toBitVec (8 * n) b.toBitVec (8 * m)) :
    Disj a n b m := h

/-- Words the word view holds at `wd b i` are the words from `b`. -/
theorem wordsAt_of_wordView {d : Mem 64} {b : UInt64} {ws : List UInt64}
    (h : ∀ i (hi : i < ws.length), wordView d (wd b i) = some ws[i]) : WordsAt d b.toBitVec ws :=
  wordsAt_iff.mpr fun i hi ↦ by
    have := wordAt_of_wordView (h i hi)
    rwa [toBitVec_wd] at this

/-- The words from `b` are what the word view holds at `wd b i`. -/
theorem wordView_of_wordsAt {d : Mem 64} {b : UInt64} {ws : List UInt64}
    (h : WordsAt d b.toBitVec ws) {i : Nat} (hi : i < ws.length) :
    wordView d (wd b i) = some ws[i] :=
  WordAt.wordView (by rw [toBitVec_wd]; exact h.getElem hi)

theorem wordsAt_iff_wordView {d : Mem 64} {b : UInt64} {ws : List UInt64} :
    WordsAt d b.toBitVec ws ↔ ∀ i (hi : i < ws.length), wordView d (wd b i) = some ws[i] :=
  ⟨fun h _ hi ↦ wordView_of_wordsAt h hi, wordsAt_of_wordView⟩

/-- `Native.Keccak.WordsAt` of the word view is `WordsAt` of the bytes. -/
theorem keccakWordsAt_iff {d : Mem 64} {b : UInt64} {ws : List UInt64} :
    Native.Keccak.WordsAt (wordView d) b ws ↔ WordsAt d b.toBitVec ws :=
  wordsAt_iff_wordView.symm

/-- A word the word view holds is eight mapped bytes. -/
theorem mapped_of_wordView_isSome {d : Mem 64} {a : UInt64} (h : (wordView d a).isSome) :
    Mapped d a.toBitVec 8 := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  exact (wordAt_of_wordView hw).mapped

/-- An area of `n` words the word view holds is `8 n` mapped bytes. -/
theorem mapped_of_wordView {d : Mem 64} {b : UInt64} {n : Nat}
    (h : ∀ k < n, (wordView d (wd b k)).isSome) : Mapped d b.toBitVec (8 * n) := fun i hi ↦ by
  have hm := mapped_of_wordView_isSome (h (i / 8) (by omega))
  rw [toBitVec_wd] at hm
  have := hm (i % 8) (Nat.mod_lt _ (by omega))
  rwa [addr_add_add, show 8 * (i / 8) + i % 8 = i by omega] at this

end

end NativeRustcVm
