import LeanVM.Cost.Bounds.Decoder.ShapeDefs

/-!
# Tests: Roth–Ruckenstein's search at the worst shape

At `(28, 4)`, the worst admissible shape (`k = 2^22`, `W = 6968845169`, `ℓ = 1661`), the bound
`rrBound` (`Cost/Bounds/Decoder/ShapeDefs.lean`) on Roth–Ruckenstein's search per lane is
`100532264391592171478138475 ≈ 2^86.38` (`prefixesNFC_cost`: `1 + k·ℓ ≈ 2^32.7` nodes, the
substitution by the butterfly `≈ 2^53.5` per node, the roots `≈ 2^48.4`), evaluated by the kernel.
A documentation value, the one `Cost/Bounds/PMBasis/LaneDefs.lean` cites: no end proof uses it
(the decoder's bound at every admissible shape, Roth–Ruckenstein's term included, is decided in
`Cost/Bounds/PMLane/Shapes.lean`).
-/

namespace LeanVMTests.Cost.RrBound

open LeanVM.Cost.Bounds.Decoder LeanVM.Extraction CompPoly.GuruswamiSudan

example :
    rrBound ((gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp.weightedDegreeBound + 1)
        (interpolationYCap (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp + 2) (2 ^ 22)
        (interpolationYCap (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp) =
      100532264391592171478138475 := by
  decide +kernel

end LeanVMTests.Cost.RrBound
