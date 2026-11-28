module

public import NativeRustcVm.Whir.Rep
public import NativeRustcVm.Transcript.Update
public import NativeRustcVm.MemLemmas

/-!
# WHIR's state across changes (x86-64)

Memory agreeing with an earlier one on an area's bytes but at the offsets `W`
(`NativeRustcVm.Transcript.Agree`) keeps a representation over bytes outside `W`
(`bytesAt_of_agree`, `bufEWAt_of_agree`, `gluedAt_of_agree`, each from `agree_sub`).
`WhirStateAt.agree`: the state at `p` kept. `WhirStateAt.fold`: `fold_round`'s writes, the claim,
the `α`s' count and the new `α`, give the folded state. (The AArch64 proof's, restated here.)
-/

namespace NativeRustcVmX64.Whir

open NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (WordAt EWAt EWsAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero Agree)

public section

variable {d d' : Mem 64}

/-- Part of an agreement: the `k` bytes at `o`, none written. -/
theorem agree_sub {a : BitVec 64} {n o k : Nat} {W : Nat → Prop} (h : Agree d d' a n W)
    (hle : o + k ≤ n) (hW : ∀ i < k, ¬ W (o + i)) : Agree d d' (off a o) k (fun _ ↦ False) :=
  fun j hj _ ↦ by rw [off_off]; exact h (o + j) (by omega) (hW j hj)

theorem bytesAt_of_agree {a : BitVec 64} {n : Nat} {bs : List UInt8}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : bs.length ≤ n) (hb : NativeRustcVm.BytesAt d a bs) :
    NativeRustcVm.BytesAt d' a bs :=
  fun i hi ↦ (h i (by omega) id).trans (hb i hi)

theorem wordAt_of_agree {a : BitVec 64} {n : Nat} {w : UInt64}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : 8 ≤ n) (hb : WordAt d a w) : WordAt d' a w :=
  bytesAt_of_agree (bs := NativeRustcVm.wordBytes w) h
    (by rw [NativeRustcVm.length_wordBytes]; exact hle) hb

theorem ewAt_of_agree {a : BitVec 64} {n : Nat} {x : EW}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : 16 ≤ n) (hb : EWAt d a x) : EWAt d' a x :=
  bytesAt_of_agree (bs := NativeRustcVm.ewBytes x) h
    (by rw [NativeRustcVm.length_ewBytes]; exact hle) hb

theorem bufEWAt_of_agree {a : BitVec 64} {n N : Nat} {xs : List EW}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : 8 + 16 * N ≤ n) (hb : BufEWAt d a N xs) :
    BufEWAt d' a N xs := by
  obtain ⟨hl, hw, he⟩ := hb
  refine ⟨hl, wordAt_of_agree h (by omega) hw, ?_⟩
  have h8 : Agree d d' (off a 8) (16 * N) (fun _ ↦ False) := agree_sub h (by omega) fun _ _ ↦ id
  exact bytesAt_of_agree (bs := xs.flatMap NativeRustcVm.ewBytes) h8
    (by rw [NativeRustcVm.length_ewsBytes]; omega) he

theorem bufWordsAt_of_agree {a : BitVec 64} {n N : Nat} {xs : List UInt64}
    (h : Agree d d' a n (fun _ ↦ False)) (hle : 8 + 8 * N ≤ n) (hb : BufWordsAt d a N xs) :
    BufWordsAt d' a N xs := by
  obtain ⟨hl, hw, he⟩ := hb
  refine ⟨hl, wordAt_of_agree h (by omega) hw, ?_⟩
  have h8 : Agree d d' (off a 8) (8 * N) (fun _ ↦ False) := agree_sub h (by omega) fun _ _ ↦ id
  exact bytesAt_of_agree (bs := xs.flatMap NativeRustcVm.wordBytes) h8
    (by rw [NativeRustcVm.length_wordsBytes]; omega) he

/-- **A glued claim kept**: its `6064` bytes not written. -/
theorem gluedAt_of_agree {q : BitVec 64} {g : GluedClaimW}
    (h : Agree d d' q gluedBytes (fun _ ↦ False)) (hg : GluedAt d q g) : GluedAt d' q g := by
  have hs : ∀ o k, o + k ≤ gluedBytes → Agree d d' (off q o) k (fun _ ↦ False) :=
    fun o k hle ↦ agree_sub h hle fun _ _ ↦ id
  obtain ⟨sc, fs, w⟩ := g
  obtain ⟨hsc, hfs, h16, hw⟩ := hg
  refine ⟨ewAt_of_agree h (by decide) hsc, hfs, wordAt_of_agree (hs 16 8 (by decide)) le_rfl h16, ?_⟩
  cases w with
  | eq z =>
    obtain ⟨h24, hp⟩ := hw
    exact ⟨wordAt_of_agree (hs 24 8 (by decide)) le_rfl h24,
      bufEWAt_of_agree (hs 40 488 (by decide)) (by decide) hp⟩
  | induced mu qs ws =>
    obtain ⟨h24, hmu, h32, hq, hws⟩ := hw
    exact ⟨wordAt_of_agree (hs 24 8 (by decide)) le_rfl h24, hmu,
      wordAt_of_agree (hs 32 8 (by decide)) le_rfl h32,
      bufWordsAt_of_agree (hs 528 1848 (by decide)) (by decide) hq,
      bufEWAt_of_agree (hs 2376 3688 (by decide)) (by decide) hws⟩

variable {p : BitVec 64} {w : WhirStateW}

/-- **The state kept.** -/
theorem WhirStateAt.agree (h : WhirStateAt d p w)
    (hA : Agree d d' p stateBytes (fun _ ↦ False)) : WhirStateAt d' p w where
  claim := ewAt_of_agree hA (by decide) h.claim
  alphas := bufEWAt_of_agree (agree_sub hA (o := 16) (k := 488) (by decide) fun _ _ ↦ id)
    (by decide) h.alphas
  glued_le := h.glued_le
  glued_len := wordAt_of_agree (agree_sub hA (o := 504) (k := 8) (by decide) fun _ _ ↦ id)
    le_rfl h.glued_len
  glued i hi := gluedAt_of_agree (agree_sub hA (o := 504 + 8 + 6064 * i) (k := 6064) (by
    have := h.glued_le
    have hi' : i < w.glued.size := hi
    show 504 + 8 + 6064 * i + 6064 ≤ 61152
    unfold gluedCap at this
    omega) fun _ _ ↦ id) (h.glued i hi)

/-- **A fold round's writes**: the claim `c`, the `α`s' count, the new `α` `x`. -/
theorem WhirStateAt.fold (h : WhirStateAt d p w)
    (hlt : w.alphas.size < stackCap) {c x : EW}
    (hA : Agree d d' p stateBytes fun j ↦ j < 24 ∨
      (24 + 16 * w.alphas.size ≤ j ∧ j < 40 + 16 * w.alphas.size))
    (hc : EWAt d' p c) (hn : WordAt d' (off p 16) (w.alphas.size + 1).toUInt64)
    (hx : EWAt d' (off p (24 + 16 * w.alphas.size)) x) :
    WhirStateAt d' p { w with claim := c, alphas := w.alphas.push x } := by
  have hl : w.alphas.size ≤ 29 := by unfold stackCap at hlt; omega
  obtain ⟨-, -, hxs⟩ := h.alphas
  refine ⟨hc, ⟨by simp [stackCap]; omega, by simpa [alphasOff] using hn, ?_⟩, h.glued_le, ?_,
    fun i hi ↦ ?_⟩
  · simp only [Array.toList_push]
    rw [NativeRustcVm.ewsAt_append_iff, NativeRustcVm.ewsAt_singleton_iff]
    refine ⟨?_, ?_⟩
    · have hxs' : EWsAt d (off p 24) w.alphas.toList := by
        have := hxs
        rwa [show off p alphasOff + 8#64 = off p 24 from off_off p 16 8] at this
      rw [show off p alphasOff + 8#64 = off p 24 from off_off p 16 8]
      refine bytesAt_of_agree (agree_sub hA (o := 24) (k := 16 * w.alphas.size) (by
        show 24 + 16 * w.alphas.size ≤ 61152; omega) fun j hj hw ↦ by omega) ?_ hxs'
      rw [NativeRustcVm.length_ewsBytes]; simp
    · rw [show off p alphasOff + 8#64 = off p 24 from off_off p 16 8,
        NativeRustcVm.Transcript.off_add,
        show 24 + 16 * w.alphas.toList.length = 24 + 16 * w.alphas.size by simp]
      exact hx
  · exact wordAt_of_agree (agree_sub hA (o := 504) (k := 8) (by decide) fun j hj hw ↦ by omega)
      le_rfl h.glued_len
  · have := h.glued_le
    have hi' : i < w.glued.size := hi
    exact gluedAt_of_agree (agree_sub hA (o := 504 + 8 + 6064 * i) (k := 6064) (by
      show 504 + 8 + 6064 * i + 6064 ≤ 61152
      unfold gluedCap at this
      omega) fun j hj hw ↦ by omega) (h.glued i hi)

end

end NativeRustcVmX64.Whir
