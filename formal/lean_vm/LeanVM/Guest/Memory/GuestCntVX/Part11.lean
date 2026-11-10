module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxsplit_344_3558 : blockR (kvxlookJ 344) (kvxomLookJ 344) false [(.n 160, 1), (.n 161, 22), (.n 213, 54), (.n 346, 1), (.n 347, 9), (.n 404, 44), (.n 534, 1), (.n 535, 6), (.n 592, 28), (.n 721, 1), (.n 722, 4), (.n 779, 20), (.n 907, 1), (.n 908, 3), (.n 965, 16), (.n 1043, 1), (.n 1044, 3), (.n 1091, 15), (.n 1820, 0), (.n 1821, 13), (.n 2617, 0), (.n 2618, 5), (.n 3135, 0), (.n 3136, 3), (.n 3557, 0), (.n 3558, 2), (.n 3883, 0), (.n 3884, 2)] Data.core344.params Data.core344.name (Data.core344.body.drop 3558)
    ([(.n 3558, 2), (.n 3557, 0), (.n 3136, 3), (.n 3135, 0), (.n 2618, 5), (.n 2617, 0), (.n 1821, 13), (.n 1820, 0), (.n 1091, 15), (.n 1044, 3), (.n 1043, 1), (.n 965, 16), (.n 908, 3), (.n 907, 1), (.n 779, 20), (.n 722, 4), (.n 721, 1), (.n 592, 28), (.n 535, 6), (.n 534, 1), (.n 404, 44), (.n 347, 9), (.n 346, 1), (.n 213, 54), (.n 161, 22), (.n 160, 1)], []) = some (⟨274, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_345 : kvxStaticRange 345 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_346 : kvxStaticRange 346 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_347_0 : noTopRet ((Data.core347.body.drop 0).take 1428) = true ∧
    blockR (kvxlookJ 347) (kvxomLookJ 347) false [(.n 160, 1), (.n 161, 13), (.n 213, 36), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 3), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 905, 17), (.n 1452, 0), (.n 1453, 9), (.n 1605, 0), (.n 1606, 4), (.n 2127, 0), (.n 2128, 3), (.n 2225, 0), (.n 2226, 2)] Data.core347.params Data.core347.name ((Data.core347.body.drop 0).take 1428)
      ([], []) = some (⟨17959, []⟩, []) ∧
    blockEnv false [(.n 160, 1), (.n 161, 13), (.n 213, 36), (.n 344, 1), (.n 345, 7), (.n 402, 37), (.n 532, 1), (.n 533, 5), (.n 590, 25), (.n 719, 1), (.n 720, 3), (.n 777, 19), (.n 857, 1), (.n 858, 3), (.n 905, 17), (.n 1452, 0), (.n 1453, 9), (.n 1605, 0), (.n 1606, 4), (.n 2127, 0), (.n 2128, 3), (.n 2225, 0), (.n 2226, 2)] Data.core347.params ([], []) ((Data.core347.body.drop 0).take 1428) = ([(.n 1453, 9), (.n 1452, 0), (.n 905, 17), (.n 858, 3), (.n 857, 1), (.n 777, 19), (.n 720, 3), (.n 719, 1), (.n 590, 25), (.n 533, 5), (.n 532, 1), (.n 402, 37), (.n 345, 7), (.n 344, 1), (.n 213, 36), (.n 161, 13), (.n 160, 1)], []) := by
  decide +kernel

end
end LeanVM.Guest
