module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_318 : kvjStaticRange 318 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_331 : kvjStaticRange 331 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_332 : kvjStaticRange 332 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_333_0 : noTopRet ((Data.core333.body.drop 0).take 1428) = true ∧
    blockR (kvjlookJ 333) (kvjomLookJ 333) false [(.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 347, 1), (.n 348, 8), (.n 405, 55), (.n 537, 1), (.n 538, 5), (.n 595, 32), (.n 723, 1), (.n 724, 3), (.n 781, 23), (.n 862, 1), (.n 863, 3), (.n 910, 20), (.n 1457, 0), (.n 1458, 27), (.n 1610, 0), (.n 1611, 6), (.n 2332, 0), (.n 2333, 4), (.n 2354, 0), (.n 2355, 2)] Data.core333.params Data.core333.name ((Data.core333.body.drop 0).take 1428)
      ([], []) = some (⟨10780, []⟩, []) ∧
    blockEnv false [(.n 160, 1), (.n 161, 37), (.n 213, 108), (.n 347, 1), (.n 348, 8), (.n 405, 55), (.n 537, 1), (.n 538, 5), (.n 595, 32), (.n 723, 1), (.n 724, 3), (.n 781, 23), (.n 862, 1), (.n 863, 3), (.n 910, 20), (.n 1457, 0), (.n 1458, 27), (.n 1610, 0), (.n 1611, 6), (.n 2332, 0), (.n 2333, 4), (.n 2354, 0), (.n 2355, 2)] Data.core333.params ([], []) ((Data.core333.body.drop 0).take 1428) = ([(.n 1458, 27), (.n 1457, 0), (.n 910, 20), (.n 863, 3), (.n 862, 1), (.n 781, 23), (.n 724, 3), (.n 723, 1), (.n 595, 32), (.n 538, 5), (.n 537, 1), (.n 405, 55), (.n 348, 8), (.n 347, 1), (.n 213, 108), (.n 161, 37), (.n 160, 1)], []) := by
  decide +kernel

end
end LeanVM.Guest
