module

public import NativeRustcVmX64.Whir.GlueLevel.Basic

/-!
# `glue_level`'s memory facts (x86-64)

Representations over bytes where nothing changed (`bytesAt_keep'`, `wordAt_keep`, `ewAt_keep`,
`bufEWAt_keep`, `bufWordsAt_keep`, `gluedAt_keep`); the state's parts as the entry has them and
as region loads read them (`loadW`); the templates' aliases (`headA_ok`, `glued_addr`).
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

public section

variable {d d' : DataMem} {a : BitVec 64} {n : Nat}

/-! ## Representations kept -/

/-- The `n` bytes from `a` the same in `d` and `d'`. -/
abbrev Same (d d' : DataMem) (a : BitVec 64) (n : Nat) : Prop :=
  ∀ j < n, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j)

theorem bytesAt_keep' (hk : Same d d' a n) {o : Nat} {bs : List UInt8} (hle : o + bs.length ≤ n)
    (h : NativeRustcVm.BytesAt d (off a o) bs) : NativeRustcVm.BytesAt d' (off a o) bs :=
  NativeRustcVm.Transcript.bytesAt_congr h fun i hi ↦ by
    rw [NativeRustcVm.Transcript.off_add]
    exact hk _ (by omega)

theorem wordAt_keep (hk : Same d d' a n) {o : Nat} {w : UInt64} (hle : o + 8 ≤ n)
    (h : WordAt d (off a o) w) : WordAt d' (off a o) w :=
  bytesAt_keep' hk (by rw [NativeRustcVm.length_wordBytes]; exact hle) h

theorem ewAt_keep (hk : Same d d' a n) {o : Nat} {x : EW} (hle : o + 16 ≤ n)
    (h : EWAt d (off a o) x) : EWAt d' (off a o) x :=
  bytesAt_keep' hk (by rw [NativeRustcVm.length_ewBytes]; exact hle) h

theorem bufEWAt_keep (hk : Same d d' a n) {o N : Nat} {xs : List EW} (hle : o + (8 + 16 * N) ≤ n)
    (h : BufEWAt d (off a o) N xs) : BufEWAt d' (off a o) N xs := by
  obtain ⟨hl, hw, he⟩ := h
  refine ⟨hl, wordAt_keep hk (by omega) hw, ?_⟩
  have he' : NativeRustcVm.BytesAt d (off a (o + 8)) (xs.flatMap NativeRustcVm.ewBytes) := by
    rw [← off_off]
    exact he
  have := bytesAt_keep' hk (by rw [NativeRustcVm.length_ewsBytes]; omega) he'
  rw [← off_off] at this
  exact this

theorem bufWordsAt_keep (hk : Same d d' a n) {o N : Nat} {xs : List UInt64}
    (hle : o + (8 + 8 * N) ≤ n) (h : BufWordsAt d (off a o) N xs) :
    BufWordsAt d' (off a o) N xs := by
  obtain ⟨hl, hw, he⟩ := h
  refine ⟨hl, wordAt_keep hk (by omega) hw, ?_⟩
  have he' : NativeRustcVm.BytesAt d (off a (o + 8)) (xs.flatMap NativeRustcVm.wordBytes) := by
    rw [← off_off]
    exact he
  have := bytesAt_keep' hk (by rw [NativeRustcVm.length_wordsBytes]; omega) he'
  rw [← off_off] at this
  exact this

/-- **A glued claim kept**: its `6064` bytes the same. -/
theorem gluedAt_keep {o : Nat} {g : GluedClaimW} (hk : Same d d' a n) (hle : o + gluedBytes ≤ n)
    (h : GluedAt d (off a o) g) : GluedAt d' (off a o) g := by
  have hg : gluedBytes = 6064 := rfl
  obtain ⟨sc, fs, w⟩ := g
  obtain ⟨hsc, hfs, h16, hw⟩ := h
  refine ⟨ewAt_keep hk (by omega) hsc, hfs, ?_, ?_⟩
  · rw [off_off] at h16 ⊢
    exact wordAt_keep hk (by omega) h16
  cases w with
  | eq z =>
    obtain ⟨h24, hp⟩ := hw
    rw [off_off] at h24 hp
    show WordAt d' (off (off a o) 24) 0 ∧ BufEWAt d' (off (off a o) 40) stackCap z.toList
    rw [off_off, off_off]
    exact ⟨wordAt_keep hk (by omega) h24, bufEWAt_keep hk (by unfold stackCap; omega) hp⟩
  | induced mu qs ws =>
    obtain ⟨h24, hmu, h32, hq, hws⟩ := hw
    rw [off_off] at h24 h32 hq hws
    show WordAt d' (off (off a o) 24) 1 ∧ mu ≤ stackCap ∧
      WordAt d' (off (off a o) 32) mu.toUInt64 ∧
      BufWordsAt d' (off (off a o) 528) queryCap qs.toList ∧
      BufEWAt d' (off (off a o) 2376) queryCap ws.toList
    rw [off_off, off_off, off_off, off_off]
    exact ⟨wordAt_keep hk (by omega) h24, hmu, wordAt_keep hk (by omega) h32,
      bufWordsAt_keep hk (by unfold queryCap; omega) hq,
      bufEWAt_keep hk (by unfold queryCap; omega) hws⟩

theorem bufEWAt_keep0 (hk : Same d d' a n) {N : Nat} {xs : List EW} (hle : 8 + 16 * N ≤ n)
    (h : BufEWAt d a N xs) : BufEWAt d' a N xs := by
  rw [← off_zero a] at h ⊢
  exact bufEWAt_keep hk (by omega) h

theorem bufWordsAt_keep0 (hk : Same d d' a n) {N : Nat} {xs : List UInt64} (hle : 8 + 8 * N ≤ n)
    (h : BufWordsAt d a N xs) : BufWordsAt d' a N xs := by
  rw [← off_zero a] at h ⊢
  exact bufWordsAt_keep hk (by omega) h

theorem wordAt_keep0 (hk : Same d d' a n) {w : UInt64} (hle : 8 ≤ n) (h : WordAt d a w) :
    WordAt d' a w := by
  rw [← off_zero a] at h ⊢
  exact wordAt_keep hk (by omega) h

theorem wordAt_add0 {w : UInt64} (h : WordAt d a w) : WordAt d (a + BitVec.ofNat 64 0) w := by
  rw [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a]
  exact h

theorem same_trans {d'' : DataMem} (h1 : Same d d' a n) (h2 : Same d' d'' a n) : Same d d'' a n :=
  fun j hj ↦ (h2 j hj).trans (h1 j hj)

/-- A part of the bytes the same. -/
theorem same_off {o k : Nat} (h : Same d d' a n) (hle : o + k ≤ n) : Same d d' (off a o) k :=
  fun j hj ↦ by rw [NativeRustcVm.Transcript.off_add]; exact h _ (by omega)

end

end NativeRustcVmX64.Whir.GlueLevel
