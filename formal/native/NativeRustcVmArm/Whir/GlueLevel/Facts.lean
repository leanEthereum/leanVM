module

public import NativeRustcVmArm.Whir.GlueLevel.Basic

/-!
# The state's facts `glue_level` carries

`Base s p d`: the parts of the state at `p` that `glue_level` does not write, the `α`s and the
glued claims so far, kept by every step (`Base.agree`). A word, an element, a glued claim at an
offset of the state is kept by a step that does not write its bytes (`kw`, `ke`, `kg`). The first
glued claim is at `o1 s = 512 + 6064 · len`, the second at `o1 s + 6064`, both in the state
(`o1_le`).
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off Agree)

@[expose] public section

/-- Offset of the first glued claim `glue_level` adds. -/
abbrev o1 (s : WhirStateW) : Nat := gluedOff + 8 + gluedBytes * s.glued.size

/-- **The state's parts `glue_level` keeps.** -/
structure Base (s : WhirStateW) (p : BitVec 64) (d : Mem 64) : Prop where
  alphas : BufEWAt d (off p alphasOff) stackCap s.alphas.toList
  old : ∀ i (h : i < s.glued.size), GluedAt d (off p (gluedOff + 8 + gluedBytes * i)) s.glued[i]

end

public section

variable {s : WhirStateW} {p : BitVec 64} {d d' : Mem 64} {W : Nat → Prop}

theorem o1_eq (s : WhirStateW) : o1 s = 512 + 6064 * s.glued.size := rfl

/-- Both new glued claims are in the state. -/
theorem o1_le (h : s.glued.size + 2 ≤ gluedCap) : o1 s + 2 * 6064 ≤ stateBytes := by
  rw [o1_eq]
  unfold gluedCap at h
  show _ ≤ 61152
  omega

theorem Base.of_state (h : WhirStateAt d p s) : Base s p d := ⟨h.alphas, h.glued⟩

/-- **The parts kept** by a step writing the claim, the count or past the glued claims. -/
theorem Base.agree (h : Base s p d) (hA : Agree d d' p stateBytes W)
    (hn : s.glued.size + 2 ≤ gluedCap)
    (hW : ∀ j, W j → j < 16 ∨ (504 ≤ j ∧ j < 512) ∨ o1 s ≤ j) : Base s p d' := by
  have hn' : s.glued.size ≤ 8 := by unfold gluedCap at hn; omega
  refine ⟨bufEWAt_of_agree (agree_sub hA (o := 16) (k := 488) (by decide) fun i hi hw ↦ ?_)
    (by decide) h.alphas, fun i hi ↦ gluedAt_of_agree (agree_sub hA (by
      show 504 + 8 + 6064 * i + 6064 ≤ 61152
      omega) fun j hj hw ↦ ?_) (h.old i hi)⟩
  · have := hW _ hw
    rw [o1_eq] at this
    omega
  · have h := hW _ hw
    simp only [o1_eq, gluedOff, gluedBytes] at h
    have hi' : i < s.glued.size := hi
    have hj' : j < 6064 := hj
    omega

/-- A word kept. -/
theorem kw {o : Nat} {w : UInt64} (hA : Agree d d' p stateBytes W) (hle : o + 8 ≤ stateBytes)
    (hW : ∀ i < 8, ¬ W (o + i)) (h : WordAt d (off p o) w) : WordAt d' (off p o) w :=
  wordAt_of_agree (agree_sub hA hle hW) le_rfl h

/-- An element kept. -/
theorem ke {o : Nat} {x : EW} (hA : Agree d d' p stateBytes W) (hle : o + 16 ≤ stateBytes)
    (hW : ∀ i < 16, ¬ W (o + i)) (h : EWAt d (off p o) x) : EWAt d' (off p o) x :=
  ewAt_of_agree (agree_sub hA hle hW) le_rfl h

/-- A glued claim kept. -/
theorem kg {o : Nat} {g : GluedClaimW} (hA : Agree d d' p stateBytes W)
    (hle : o + gluedBytes ≤ stateBytes) (hW : ∀ i < gluedBytes, ¬ W (o + i))
    (h : GluedAt d (off p o) g) : GluedAt d' (off p o) g :=
  gluedAt_of_agree (agree_sub hA hle hW) h

/-- A buffer of elements kept. -/
theorem kbe {o N : Nat} {xs : List EW} (hA : Agree d d' p stateBytes W)
    (hle : o + (8 + 16 * N) ≤ stateBytes) (hW : ∀ i < 8 + 16 * N, ¬ W (o + i))
    (h : BufEWAt d (off p o) N xs) : BufEWAt d' (off p o) N xs :=
  bufEWAt_of_agree (agree_sub hA hle hW) le_rfl h

/-- A buffer of words kept. -/
theorem kbw {o N : Nat} {xs : List UInt64} (hA : Agree d d' p stateBytes W)
    (hle : o + (8 + 8 * N) ≤ stateBytes) (hW : ∀ i < 8 + 8 * N, ¬ W (o + i))
    (h : BufWordsAt d (off p o) N xs) : BufWordsAt d' (off p o) N xs :=
  bufWordsAt_of_agree (agree_sub hA hle hW) le_rfl h

/-- The state's address plus `o`, as the executor computes it from the glued claims' count. -/
theorem glued_addr (n c : Nat) :
    BitVec.ofNat 64 n * BitVec.ofNat 64 6064 + (p + BitVec.ofInt 64 512) + BitVec.ofNat 64 c =
      off p (512 + 6064 * n + c) := by
  rw [show BitVec.ofInt 64 512 = BitVec.ofNat 64 512 from rfl]
  unfold off
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have := p.isLt
  omega

/-- An offset of the state as a number. -/
theorem toNat_off_state (hp : NoWrap p stateBytes) {j : Nat} (hj : j < 61152) :
    (off p j).toNat = p.toNat + j :=
  NativeRustcVm.Transcript.toNat_off (by unfold NoWrap stateBytes at hp; omega)

/-- Bytes of the state do not wrap. -/
theorem noWrap_off (hp : NoWrap p stateBytes) {j c : Nat} (h : j + c ≤ 61152) (hj : j < 61152) :
    NoWrap (off p j) c := by
  unfold NoWrap stateBytes at *
  rw [toNat_off_state hp hj]
  omega

/-- Bytes of the state are apart from what the state is apart from. -/
theorem apart_off (hp : NoWrap p stateBytes) {a : BitVec 64} {n j c : Nat}
    (h : Apart p stateBytes a n) (hle : j + c ≤ 61152) (hj : j < 61152) : Apart (off p j) c a n := by
  unfold Apart stateBytes at *
  rw [toNat_off_state hp hj]
  omega

/-- The second glued claim's address, from the count after the first. -/
theorem glued_addr1 (n c : Nat) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 1) * BitVec.ofNat 64 6064 + (p + BitVec.ofInt 64 512) +
      BitVec.ofNat 64 c = off p (512 + 6064 * (n + 1) + c) := by
  rw [← BitVec.ofNat_add]
  exact glued_addr (n + 1) c

theorem glued_addr0 (n : Nat) :
    BitVec.ofNat 64 n * BitVec.ofNat 64 6064 + (p + BitVec.ofInt 64 512) =
      off p (512 + 6064 * n) := by
  have := glued_addr (p := p) n 0
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, Nat.add_zero] at this

theorem glued_addr10 (n : Nat) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 1) * BitVec.ofNat 64 6064 + (p + BitVec.ofInt 64 512) =
      off p (512 + 6064 * (n + 1)) := by
  rw [← BitVec.ofNat_add]
  exact glued_addr0 (n + 1)

/-- The count plus one, as the executor adds it. -/
theorem count_succ (n : Nat) :
    UInt64.ofBitVec (BitVec.ofNat 64 n + BitVec.ofNat 64 1) = (n + 1).toUInt64 := by
  rw [← BitVec.ofNat_add]
  rfl

end

end NativeRustcVmArm.Whir.GlueLevel
