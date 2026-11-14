import LeanVM.Cost.Bounds.Decoder.ShapeDefs

/-!
# Tests: Roth–Ruckenstein's search at the worst shape

At `(28, 4)` (`k = 2^22 + 6`, level 0's threshold `16975762`, `W = 543224383`, `ℓ = 129`), the
bound `rrBound` (`Cost/Bounds/Decoder/ShapeDefs.lean`) on Roth–Ruckenstein's search per lane is
`35377307173825193512410 ≈ 2^74.91` (`prefixesNFC_cost`: `1 + k·ℓ ≈ 2^29.0` nodes), evaluated by
the kernel.
A documentation value, the one `Cost/Bounds/PMBasis/LaneDefs.lean` cites: no end proof uses it
(the decoder's bound at every admissible shape, Roth–Ruckenstein's term included, is decided in
`Cost/Bounds/PMLane/Shapes.lean`).
-/

namespace LeanVMTests.Cost.RrBound

open LeanVM.Cost.Bounds.Decoder LeanVM.Extraction CompPoly.GuruswamiSudan

example :
    rrBound ((gsParamsFor (2 ^ 22 + 6) (2 ^ (22 + 4)) 16975762).interp.weightedDegreeBound + 1)
        (interpolationYCap (gsParamsFor (2 ^ 22 + 6) (2 ^ (22 + 4)) 16975762).interp + 2)
        (2 ^ 22 + 6) (interpolationYCap (gsParamsFor (2 ^ 22 + 6) (2 ^ (22 + 4)) 16975762).interp) =
      35377307173825193512410 := by
  decide +kernel

end LeanVMTests.Cost.RrBound
