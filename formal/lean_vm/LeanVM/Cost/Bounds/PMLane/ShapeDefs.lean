module

public import LeanVM.Cost.Bounds.PMBasis.LaneDefs
public import LeanVM.Cost.Bounds.PMBasis.Values
public import LeanVM.Cost.Bounds.PMLane.InterpDefs

/-!
# Bounds: the decoder on `pmSolver` at every admissible shape, as definitions

`DecoderShapeOkPM μ R`: what the decoder's bound needs at a shape (the lanes word-sized,
`DecoderLaneSizes`, as for the extractor's decoder; the lanes' interpolation within the model's
price, `LaneInterpOKPM`: `PMInterpOK` and `interpPMModel ≤ interpPMPrice`,
`Bounds/PMLane/InterpDefs.lean`) and its value, at the model's prices with their
margin (`marginPrices`), at most the one at `(30, 3)`, which
`Bounds/PMLane/Shapes.lean` decides at each of the `60` admissible shapes. Definitions only, so
that the checks import no proof (`Bounds/PMLane/ShapesFirewall.lean`).
-/

namespace LeanVM.Cost.Bounds.PMLane

open LeanVM.Parameters LeanVM.Extraction LeanVM.Cost.Bounds.Decoder LeanVM.Cost.Bounds.PMBasis

public section

/-- **The decoder's price beyond the word's**, at a stack of `2^μ`: the statement's budget term
`2^max(81, 2μ + 22)` (`leanVmKnowledgeExtractorBudget`) less `2^75`, which the rest of the
extractor's price takes. -/
@[expose] def pmDecoderBudget (μ : ℕ) : ℕ := 2 ^ max 81 (2 * μ + 22) - 2 ^ 75

/-- **The lanes' interpolation within the model's price**, at prices `p`, a lane of `2^κ`
symbols, `2^(κ+R)` points, threshold `A`: the interpolation bound's per-shape conditions
(`PMSolve.PMInterpOK`, `PMSolve.interpPMModel ≤ interpPMPrice`). -/
@[expose] def LaneInterpOKPM (p : PMPrices) (κ R A : ℕ) : Prop :=
  PMSolve.PMInterpOK (2 ^ (κ + R)) (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp ∧
    PMSolve.interpPMModel p (2 ^ (κ + R)) (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp ≤
      interpPMPrice p (2 ^ (κ + R)) (gsParamsFor (2 ^ κ + Whir.initialFold) (2 ^ (κ + R)) A).interp

instance (p : PMPrices) (κ R A : ℕ) : Decidable (LaneInterpOKPM p κ R A) := by
  unfold LaneInterpOKPM; infer_instance

/-- What the decoder's bound needs at a shape, and its value within the stack size's budget. -/
@[expose] def DecoderShapeOkPM (μ R : ℕ) : Prop :=
  DecoderLaneSizes (μ - Whir.initialFold) R (johnsonThreshold μ R) ∧
    LaneInterpOKPM marginPrices (μ - Whir.initialFold) R (johnsonThreshold μ R) ∧
    decoderBoundPM marginPrices μ R 0 0 ≤ pmDecoderBudget μ

instance (μ R : ℕ) : Decidable (DecoderShapeOkPM μ R) := by
  unfold DecoderShapeOkPM; infer_instance

end

end LeanVM.Cost.Bounds.PMLane
