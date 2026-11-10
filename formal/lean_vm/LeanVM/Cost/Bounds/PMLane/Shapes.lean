module

public import LeanVM.Cost.Bounds.PMLane.ShapeDefs

/-!
# Bounds: the decoder on `pmSolver` at every admissible shape

At each of the `72` admissible shapes (`15 ≤ μ ≤ 32`, `1 ≤ R ≤ 4`), one `decide +kernel` each
(a single `decide` over all shapes at once outgrows the memory): the lanes are word-sized
(`DecoderLaneSizes`) and the decoder's bound beyond the word's prices, at the model's prices
with their margin, is at most the one at `(32, 3)` (`pmDecoderWorstPrice`,
`67498454346174488641581264 ≈ 2^85.80`): **`decoderShapePM_ok`**, which
`decodeStacksPMC_cost_worst` (`Bounds/PMLane/Decode.lean`) reads.

The checks evaluate only the extractor's parameter search and the bounds' definitions, none of
their proofs (`Bounds/PMLane/ShapesFirewall.lean`).
-/

namespace LeanVM.Cost.Bounds.PMLane

open LeanVM.Parameters CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction
open LeanVM.Cost.Bounds.Decoder LeanVM.Cost.Bounds.PMBasis

public section

theorem decoderShapeOkPM_15_1 : DecoderShapeOkPM 15 1 := by decide +kernel
theorem decoderShapeOkPM_15_2 : DecoderShapeOkPM 15 2 := by decide +kernel
theorem decoderShapeOkPM_15_3 : DecoderShapeOkPM 15 3 := by decide +kernel
theorem decoderShapeOkPM_15_4 : DecoderShapeOkPM 15 4 := by decide +kernel
theorem decoderShapeOkPM_16_1 : DecoderShapeOkPM 16 1 := by decide +kernel
theorem decoderShapeOkPM_16_2 : DecoderShapeOkPM 16 2 := by decide +kernel
theorem decoderShapeOkPM_16_3 : DecoderShapeOkPM 16 3 := by decide +kernel
theorem decoderShapeOkPM_16_4 : DecoderShapeOkPM 16 4 := by decide +kernel
theorem decoderShapeOkPM_17_1 : DecoderShapeOkPM 17 1 := by decide +kernel
theorem decoderShapeOkPM_17_2 : DecoderShapeOkPM 17 2 := by decide +kernel
theorem decoderShapeOkPM_17_3 : DecoderShapeOkPM 17 3 := by decide +kernel
theorem decoderShapeOkPM_17_4 : DecoderShapeOkPM 17 4 := by decide +kernel
theorem decoderShapeOkPM_18_1 : DecoderShapeOkPM 18 1 := by decide +kernel
theorem decoderShapeOkPM_18_2 : DecoderShapeOkPM 18 2 := by decide +kernel
theorem decoderShapeOkPM_18_3 : DecoderShapeOkPM 18 3 := by decide +kernel
theorem decoderShapeOkPM_18_4 : DecoderShapeOkPM 18 4 := by decide +kernel
theorem decoderShapeOkPM_19_1 : DecoderShapeOkPM 19 1 := by decide +kernel
theorem decoderShapeOkPM_19_2 : DecoderShapeOkPM 19 2 := by decide +kernel
theorem decoderShapeOkPM_19_3 : DecoderShapeOkPM 19 3 := by decide +kernel
theorem decoderShapeOkPM_19_4 : DecoderShapeOkPM 19 4 := by decide +kernel
theorem decoderShapeOkPM_20_1 : DecoderShapeOkPM 20 1 := by decide +kernel
theorem decoderShapeOkPM_20_2 : DecoderShapeOkPM 20 2 := by decide +kernel
theorem decoderShapeOkPM_20_3 : DecoderShapeOkPM 20 3 := by decide +kernel
theorem decoderShapeOkPM_20_4 : DecoderShapeOkPM 20 4 := by decide +kernel
theorem decoderShapeOkPM_21_1 : DecoderShapeOkPM 21 1 := by decide +kernel
theorem decoderShapeOkPM_21_2 : DecoderShapeOkPM 21 2 := by decide +kernel
theorem decoderShapeOkPM_21_3 : DecoderShapeOkPM 21 3 := by decide +kernel
theorem decoderShapeOkPM_21_4 : DecoderShapeOkPM 21 4 := by decide +kernel
theorem decoderShapeOkPM_22_1 : DecoderShapeOkPM 22 1 := by decide +kernel
theorem decoderShapeOkPM_22_2 : DecoderShapeOkPM 22 2 := by decide +kernel
theorem decoderShapeOkPM_22_3 : DecoderShapeOkPM 22 3 := by decide +kernel
theorem decoderShapeOkPM_22_4 : DecoderShapeOkPM 22 4 := by decide +kernel
theorem decoderShapeOkPM_23_1 : DecoderShapeOkPM 23 1 := by decide +kernel
theorem decoderShapeOkPM_23_2 : DecoderShapeOkPM 23 2 := by decide +kernel
theorem decoderShapeOkPM_23_3 : DecoderShapeOkPM 23 3 := by decide +kernel
theorem decoderShapeOkPM_23_4 : DecoderShapeOkPM 23 4 := by decide +kernel
theorem decoderShapeOkPM_24_1 : DecoderShapeOkPM 24 1 := by decide +kernel
theorem decoderShapeOkPM_24_2 : DecoderShapeOkPM 24 2 := by decide +kernel
theorem decoderShapeOkPM_24_3 : DecoderShapeOkPM 24 3 := by decide +kernel
theorem decoderShapeOkPM_24_4 : DecoderShapeOkPM 24 4 := by decide +kernel
theorem decoderShapeOkPM_25_1 : DecoderShapeOkPM 25 1 := by decide +kernel
theorem decoderShapeOkPM_25_2 : DecoderShapeOkPM 25 2 := by decide +kernel
theorem decoderShapeOkPM_25_3 : DecoderShapeOkPM 25 3 := by decide +kernel
theorem decoderShapeOkPM_25_4 : DecoderShapeOkPM 25 4 := by decide +kernel
theorem decoderShapeOkPM_26_1 : DecoderShapeOkPM 26 1 := by decide +kernel
theorem decoderShapeOkPM_26_2 : DecoderShapeOkPM 26 2 := by decide +kernel
theorem decoderShapeOkPM_26_3 : DecoderShapeOkPM 26 3 := by decide +kernel
theorem decoderShapeOkPM_26_4 : DecoderShapeOkPM 26 4 := by decide +kernel
theorem decoderShapeOkPM_27_1 : DecoderShapeOkPM 27 1 := by decide +kernel
theorem decoderShapeOkPM_27_2 : DecoderShapeOkPM 27 2 := by decide +kernel
theorem decoderShapeOkPM_27_3 : DecoderShapeOkPM 27 3 := by decide +kernel
theorem decoderShapeOkPM_27_4 : DecoderShapeOkPM 27 4 := by decide +kernel
theorem decoderShapeOkPM_28_1 : DecoderShapeOkPM 28 1 := by decide +kernel
theorem decoderShapeOkPM_28_2 : DecoderShapeOkPM 28 2 := by decide +kernel
theorem decoderShapeOkPM_28_3 : DecoderShapeOkPM 28 3 := by decide +kernel
theorem decoderShapeOkPM_28_4 : DecoderShapeOkPM 28 4 := by decide +kernel
theorem decoderShapeOkPM_29_1 : DecoderShapeOkPM 29 1 := by decide +kernel
theorem decoderShapeOkPM_29_2 : DecoderShapeOkPM 29 2 := by decide +kernel
theorem decoderShapeOkPM_29_3 : DecoderShapeOkPM 29 3 := by decide +kernel
theorem decoderShapeOkPM_29_4 : DecoderShapeOkPM 29 4 := by decide +kernel
theorem decoderShapeOkPM_30_1 : DecoderShapeOkPM 30 1 := by decide +kernel
theorem decoderShapeOkPM_30_2 : DecoderShapeOkPM 30 2 := by decide +kernel
theorem decoderShapeOkPM_30_3 : DecoderShapeOkPM 30 3 := by decide +kernel
theorem decoderShapeOkPM_30_4 : DecoderShapeOkPM 30 4 := by decide +kernel
theorem decoderShapeOkPM_31_1 : DecoderShapeOkPM 31 1 := by decide +kernel
theorem decoderShapeOkPM_31_2 : DecoderShapeOkPM 31 2 := by decide +kernel
theorem decoderShapeOkPM_31_3 : DecoderShapeOkPM 31 3 := by decide +kernel
theorem decoderShapeOkPM_31_4 : DecoderShapeOkPM 31 4 := by decide +kernel
theorem decoderShapeOkPM_32_1 : DecoderShapeOkPM 32 1 := by decide +kernel
theorem decoderShapeOkPM_32_2 : DecoderShapeOkPM 32 2 := by decide +kernel
theorem decoderShapeOkPM_32_3 : DecoderShapeOkPM 32 3 := by decide +kernel
theorem decoderShapeOkPM_32_4 : DecoderShapeOkPM 32 4 := by decide +kernel

/-- **The decoder's hypotheses at every admissible shape.** -/
theorem decoderShapePM_ok {μ R : ℕ} (h : Whir.Admissible μ R) : DecoderShapeOkPM μ R := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Whir.minLogStack, Whir.maxLogStack] at h1 h2
  have hR : R = 1 ∨ R = 2 ∨ R = 3 ∨ R = 4 := by omega
  rcases (show μ = 15 ∨ μ = 16 ∨ μ = 17 ∨ μ = 18 ∨ μ = 19 ∨ μ = 20 ∨ μ = 21 ∨ μ = 22 ∨ μ = 23 ∨ μ = 24 ∨ μ = 25 ∨ μ = 26 ∨ μ = 27 ∨ μ = 28 ∨ μ = 29 ∨ μ = 30 ∨ μ = 31 ∨ μ = 32 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hR with rfl | rfl | rfl | rfl
  · exact decoderShapeOkPM_15_1
  · exact decoderShapeOkPM_15_2
  · exact decoderShapeOkPM_15_3
  · exact decoderShapeOkPM_15_4
  · exact decoderShapeOkPM_16_1
  · exact decoderShapeOkPM_16_2
  · exact decoderShapeOkPM_16_3
  · exact decoderShapeOkPM_16_4
  · exact decoderShapeOkPM_17_1
  · exact decoderShapeOkPM_17_2
  · exact decoderShapeOkPM_17_3
  · exact decoderShapeOkPM_17_4
  · exact decoderShapeOkPM_18_1
  · exact decoderShapeOkPM_18_2
  · exact decoderShapeOkPM_18_3
  · exact decoderShapeOkPM_18_4
  · exact decoderShapeOkPM_19_1
  · exact decoderShapeOkPM_19_2
  · exact decoderShapeOkPM_19_3
  · exact decoderShapeOkPM_19_4
  · exact decoderShapeOkPM_20_1
  · exact decoderShapeOkPM_20_2
  · exact decoderShapeOkPM_20_3
  · exact decoderShapeOkPM_20_4
  · exact decoderShapeOkPM_21_1
  · exact decoderShapeOkPM_21_2
  · exact decoderShapeOkPM_21_3
  · exact decoderShapeOkPM_21_4
  · exact decoderShapeOkPM_22_1
  · exact decoderShapeOkPM_22_2
  · exact decoderShapeOkPM_22_3
  · exact decoderShapeOkPM_22_4
  · exact decoderShapeOkPM_23_1
  · exact decoderShapeOkPM_23_2
  · exact decoderShapeOkPM_23_3
  · exact decoderShapeOkPM_23_4
  · exact decoderShapeOkPM_24_1
  · exact decoderShapeOkPM_24_2
  · exact decoderShapeOkPM_24_3
  · exact decoderShapeOkPM_24_4
  · exact decoderShapeOkPM_25_1
  · exact decoderShapeOkPM_25_2
  · exact decoderShapeOkPM_25_3
  · exact decoderShapeOkPM_25_4
  · exact decoderShapeOkPM_26_1
  · exact decoderShapeOkPM_26_2
  · exact decoderShapeOkPM_26_3
  · exact decoderShapeOkPM_26_4
  · exact decoderShapeOkPM_27_1
  · exact decoderShapeOkPM_27_2
  · exact decoderShapeOkPM_27_3
  · exact decoderShapeOkPM_27_4
  · exact decoderShapeOkPM_28_1
  · exact decoderShapeOkPM_28_2
  · exact decoderShapeOkPM_28_3
  · exact decoderShapeOkPM_28_4
  · exact decoderShapeOkPM_29_1
  · exact decoderShapeOkPM_29_2
  · exact decoderShapeOkPM_29_3
  · exact decoderShapeOkPM_29_4
  · exact decoderShapeOkPM_30_1
  · exact decoderShapeOkPM_30_2
  · exact decoderShapeOkPM_30_3
  · exact decoderShapeOkPM_30_4
  · exact decoderShapeOkPM_31_1
  · exact decoderShapeOkPM_31_2
  · exact decoderShapeOkPM_31_3
  · exact decoderShapeOkPM_31_4
  · exact decoderShapeOkPM_32_1
  · exact decoderShapeOkPM_32_2
  · exact decoderShapeOkPM_32_3
  · exact decoderShapeOkPM_32_4

/-- **The worst price**: `67498454346174488641581264 ≈ 2^85.80`. -/
theorem pmDecoderWorstPrice_eq : pmDecoderWorstPrice = 67498454346174488641581264 := by
  decide +kernel

end

end LeanVM.Cost.Bounds.PMLane
