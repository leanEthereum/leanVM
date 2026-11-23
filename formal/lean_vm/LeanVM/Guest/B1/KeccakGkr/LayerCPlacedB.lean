/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB

  `keccak_layer`'s bound before the memory, for its two specializations: its frame, its buffers and
  its callees' words (`LayerCPlacedBE` proves it complete within it).
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCPlaced
public import LeanVM.Guest.B1.KeccakGkr.FlatFB
public import LeanVM.Guest.Memory.LoopPre

/-!
# `keccak_layer`, complete and placed within a bound

`layer_completeAtFB` (`LayerCPlacedBE`) is `layer_completeAtF` with the size of the layer's run
bounded before the memory, by

  `layerWords fs first y KP KR = fs (layerName first) + (y + 120)
    + (fs (packLoopName first) + ⌊y/8⌋ * KP) + (fs (remLoopName first) + (y % 8) * KR)`:

the layer's frame; its buffers (`allocDyn` of `y` words for the pack challenges, then 77 for the
round records, 11 for the local point, 25 for the next claim's lanes and 7 for its flips); the
eight-round pack loop's call (`⌊y/8⌋` iterations of at most `KP` words each and its run's one
phantom frame `fs (packLoopName first)` when it is entered, that frame alone when it is skipped,
which is when `y < 8`); the remainder loop's likewise (`y % 8` iterations of at most `KR` words and
its frame, its frame alone when `8 ∣ y`).

The hypotheses on the callees are fs-generic: each loop's run's words, per iteration and its one
phantom frame (`TotalLeOn … LoopPre`, the form of `Count.wSKt_totalLeOn`). The proof is `layer_completeAtF`'s
with `completeAt_flatOutFB`, the pure callees placed within their bounds by
`completeAtDTB_of_relIn`, the honest valuation `layer_obl`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- **`keccak_layer`'s words**: its frame, its buffers (`y + 77 + 11 + 25 + 7`), the eight-round
pack loop's (its frame and `⌊y/8⌋` iterations of at most `KP` words) and the remainder loop's (its
frame and `y % 8` iterations of at most `KR` words). -/
def layerWords (fs : String → ℕ) (first y KP KR : ℕ) : ℕ :=
  fs (layerName first) + (y + 120) + (fs (packLoopName first) + y / 8 * KP) +
    (fs (remLoopName first) + y % 8 * KR)

theorem packLoopName_ne_rem (first : ℕ) : packLoopName first ≠ remLoopName first := by
  unfold packLoopName remLoopName; split <;> decide

/-- The callees' bounds: the pack loop's run (its iterations and its one phantom frame), the
remainder loop's. -/
def layerKidBd (fs : String → ℕ) (first y KP KR : ℕ) (k : Kid) : ℕ :=
  if k.f = packLoopName first then y / 8 * KP + fs (packLoopName first)
  else y % 8 * KR + fs (remLoopName first)

/-- The words of the layer's callees, an entered one's bound, a skipped one's frame. -/
theorem layerKids_bound (fs : String → ℕ) (D : LayerData) (first : ℕ)
    (CL : ClaimLay) (bcur bout tbE b KP KR : ℕ) (htk : ∀ f, fs (tailKey f) ≤ fs f) :
    kidsBound fs (layerKidBd fs first D.y KP KR) (layerKids D first CL bcur bout tbE b) ≤
      fs (packLoopName first) + D.y / 8 * KP +
        (fs (remLoopName first) + D.y % 8 * KR) := by
  have hne := packLoopName_ne_rem first
  simp only [kidsBound, layerKids, layerKidBd, hne.symm, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte]
  have h1 := htk (packLoopName first)
  have h2 := htk (remLoopName first)
  split_ifs <;> omega

theorem lt_of_taken {m : ℕ} (h : decide (1 + gen ^ m ≠ 0) = true) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    exact absurd (e_add_eq_zero_iff.mpr (pow_zero gen).symm) (by simpa using h)
  · exact h0

end
end LeanVM.Guest.B1.VerifySub
