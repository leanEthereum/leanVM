module

public import LeanVM.Cost.Bounds.PMBasis.Defs

/-!
# The prices the decoder's bound is proved at

`marginPrices`: the per-operation prices of `Bounds/PMBasis/Defs.lean`'s model at which the
approximant-basis decoder's bound is proved (`decoderBoundPM`, `Bounds/PMBasis/LaneDefs.lean`;
`decodeStacksPMC_cost_worst`, `Bounds/PMLane/Decode.lean`). A definition alone, so that the shape
checks (`Bounds/PMLane/Shapes.lean`) import only what they evaluate.
-/

namespace LeanVM.Cost.Bounds.PMBasis

public section

/-- **The decoder's prices**: `80` per pointwise multiply-add (`evalDot`); `129`/`87` per element
and stage of the forward/inverse NTT; `1134`/`1401` per `j·2^j` of the conversions to/from the
novel basis (for `j ≤ 36`; with the stages, the transforms' proved prices `fwdNeed`/`invNeed` at
`j = 36` less `ovh` per point); the order-one leaf `11000·r³ + 33500·r²` (above its proved price
`PMCore.leafBound r m + 21·m + 32` for `2 ≤ r < 2^28`, `m ≤ r`; `≈ 10937·r³` at `r = 2077`);
no separate price per schoolbook coefficient product (`coeff := 0`: the GS data's scalings,
`419` per coefficient, fit within `ovh`); `504` per coefficient moved (`fwdNeed 0`, the least
`FFTPricesOK` allows). The transforms' and products' proved prices fit them
(`FFTPricesOK marginPrices`, `PMSolve.fftPricesOK_margin`), the interpolation's proved price fits
the model at every admissible shape (`Bounds/PMLane/Shapes.lean`). -/
@[expose] def marginPrices : PMPrices :=
  { mac := 80, fwd := 129, inv := 87, toNovel := 1134, fromNovel := 1401, leafCube := 11000,
    leafSquare := 33500, coeff := 0, ovh := 504 }

end

end LeanVM.Cost.Bounds.PMBasis
