module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_338 : kvkStaticRange 338 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_339 : kvkStaticRange 339 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_340_0 : noTopRet ((Data.core340.body.drop 0).take 1428) = true ∧
    blockR (kvklookJ 340) (kvkomLookJ 340) false [(.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 480, 1), (.n 481, 4), (.n 535, 28), (.n 647, 1), (.n 648, 3), (.n 702, 21), (.n 779, 1), (.n 780, 3), (.n 827, 18), (.n 1374, 0), (.n 1375, 13), (.n 2051, 0), (.n 2052, 5), (.n 2473, 0), (.n 2474, 3), (.n 2799, 0), (.n 2800, 2)] Data.core340.params Data.core340.name ((Data.core340.body.drop 0).take 1428)
      ([], []) = some (⟨3900, []⟩, []) ∧
    blockEnv false [(.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 480, 1), (.n 481, 4), (.n 535, 28), (.n 647, 1), (.n 648, 3), (.n 702, 21), (.n 779, 1), (.n 780, 3), (.n 827, 18), (.n 1374, 0), (.n 1375, 13), (.n 2051, 0), (.n 2052, 5), (.n 2473, 0), (.n 2474, 3), (.n 2799, 0), (.n 2800, 2)] Data.core340.params ([], []) ((Data.core340.body.drop 0).take 1428) = ([(.n 1375, 13), (.n 1374, 0), (.n 827, 18), (.n 780, 3), (.n 779, 1), (.n 702, 21), (.n 648, 3), (.n 647, 1), (.n 535, 28), (.n 481, 4), (.n 480, 1), (.n 367, 44), (.n 313, 8), (.n 312, 1), (.n 196, 54), (.n 152, 19), (.n 151, 1)], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_340_1428 : noTopRet ((Data.core340.body.drop 1428).take 1428) = true ∧
    blockR (kvklookJ 340) (kvkomLookJ 340) false [(.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 480, 1), (.n 481, 4), (.n 535, 28), (.n 647, 1), (.n 648, 3), (.n 702, 21), (.n 779, 1), (.n 780, 3), (.n 827, 18), (.n 1374, 0), (.n 1375, 13), (.n 2051, 0), (.n 2052, 5), (.n 2473, 0), (.n 2474, 3), (.n 2799, 0), (.n 2800, 2)] Data.core340.params Data.core340.name ((Data.core340.body.drop 1428).take 1428)
      ([(.n 1375, 13), (.n 1374, 0), (.n 827, 18), (.n 780, 3), (.n 779, 1), (.n 702, 21), (.n 648, 3), (.n 647, 1), (.n 535, 28), (.n 481, 4), (.n 480, 1), (.n 367, 44), (.n 313, 8), (.n 312, 1), (.n 196, 54), (.n 152, 19), (.n 151, 1)], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [(.n 151, 1), (.n 152, 19), (.n 196, 54), (.n 312, 1), (.n 313, 8), (.n 367, 44), (.n 480, 1), (.n 481, 4), (.n 535, 28), (.n 647, 1), (.n 648, 3), (.n 702, 21), (.n 779, 1), (.n 780, 3), (.n 827, 18), (.n 1374, 0), (.n 1375, 13), (.n 2051, 0), (.n 2052, 5), (.n 2473, 0), (.n 2474, 3), (.n 2799, 0), (.n 2800, 2)] Data.core340.params ([(.n 1375, 13), (.n 1374, 0), (.n 827, 18), (.n 780, 3), (.n 779, 1), (.n 702, 21), (.n 648, 3), (.n 647, 1), (.n 535, 28), (.n 481, 4), (.n 480, 1), (.n 367, 44), (.n 313, 8), (.n 312, 1), (.n 196, 54), (.n 152, 19), (.n 151, 1)], []) ((Data.core340.body.drop 1428).take 1428) = ([(.n 2800, 2), (.n 2799, 0), (.n 2474, 3), (.n 2473, 0), (.n 2052, 5), (.n 2051, 0), (.n 1375, 13), (.n 1374, 0), (.n 827, 18), (.n 780, 3), (.n 779, 1), (.n 702, 21), (.n 648, 3), (.n 647, 1), (.n 535, 28), (.n 481, 4), (.n 480, 1), (.n 367, 44), (.n 313, 8), (.n 312, 1), (.n 196, 54), (.n 152, 19), (.n 151, 1)], []) := by
  decide +kernel

end
end LeanVM.Guest
