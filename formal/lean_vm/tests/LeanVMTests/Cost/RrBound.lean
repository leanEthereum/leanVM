import LeanVM.Cost.Bounds.Decoder.ShapeDefs

/-!
# Tests: Roth–Ruckenstein's search at the worst shape

At `(28, 4)` (`k = 2^22 + 6`, level 0's threshold `16961245`, `W = 576682329`, `ℓ = 137`), the
bound `rrBound` (`Cost/Bounds/Decoder/ShapeDefs.lean`) on Roth–Ruckenstein's search per lane is
`42327133189982681812830 ≈ 2^75.16` (`prefixesNFC_cost`: `1 + k·ℓ ≈ 2^29.1` nodes), evaluated by
the kernel.
A documentation value, the one `Cost/Bounds/PMBasis/LaneDefs.lean` cites: no end proof uses it
(the decoder's bound at every admissible shape, Roth–Ruckenstein's term included, is decided in
`Cost/Bounds/PMLane/Shapes.lean`).
-/

namespace LeanVMTests.Cost.RrBound

open LeanVM.Cost.Bounds.Decoder LeanVM.Extraction CompPoly.GuruswamiSudan

example :
    rrBound ((gsParamsFor (2 ^ 22 + 6) (2 ^ (22 + 4)) 16961245).interp.weightedDegreeBound + 1)
        (interpolationYCap (gsParamsFor (2 ^ 22 + 6) (2 ^ (22 + 4)) 16961245).interp + 2)
        (2 ^ 22 + 6) (interpolationYCap (gsParamsFor (2 ^ 22 + 6) (2 ^ (22 + 4)) 16961245).interp) =
      42327133189982681812830 := by
  decide +kernel

end LeanVMTests.Cost.RrBound
