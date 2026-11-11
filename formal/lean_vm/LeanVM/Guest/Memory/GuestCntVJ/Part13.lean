module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjsplit_351_2372 : blockR (kvjlookJ 351) (kvjomLookJ 351) false [(.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 310, 1), (.n 311, 8), (.n 365, 37), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 812, 1), (.n 813, 3), (.n 867, 16), (.n 942, 1), (.n 943, 3), (.n 990, 14), (.n 1719, 0), (.n 1720, 9), (.n 1896, 0), (.n 1897, 4), (.n 2538, 0), (.n 2539, 3), (.n 2660, 0), (.n 2661, 2), (.n 2910, 0), (.n 2911, 2)] Data.core351.params Data.core351.name (Data.core351.body.drop 2372)
    ([(.n 1897, 4), (.n 1896, 0), (.n 1720, 9), (.n 1719, 0), (.n 990, 14), (.n 943, 3), (.n 942, 1), (.n 867, 16), (.n 813, 3), (.n 812, 1), (.n 700, 19), (.n 646, 4), (.n 645, 1), (.n 533, 25), (.n 479, 5), (.n 478, 1), (.n 365, 37), (.n 311, 8), (.n 310, 1), (.n 196, 36), (.n 152, 15), (.n 151, 1)], []) = some (⟨14, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_352 : kvjStaticRange 352 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_353 : kvjStaticRange 353 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_354_0 : noTopRet ((Data.core354.body.drop 0).take 1428) = true ∧
    blockR (kvjlookJ 354) (kvjomLookJ 354) false [(.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 311, 1), (.n 312, 6), (.n 366, 32), (.n 477, 1), (.n 478, 4), (.n 532, 22), (.n 644, 1), (.n 645, 3), (.n 699, 18), (.n 775, 1), (.n 776, 3), (.n 823, 16), (.n 1370, 0), (.n 1371, 6), (.n 2309, 0), (.n 2310, 4), (.n 2331, 0), (.n 2332, 2), (.n 2809, 0), (.n 2810, 2)] Data.core354.params Data.core354.name ((Data.core354.body.drop 0).take 1428)
      ([], []) = some (⟨3704, []⟩, []) ∧
    blockEnv false [(.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 311, 1), (.n 312, 6), (.n 366, 32), (.n 477, 1), (.n 478, 4), (.n 532, 22), (.n 644, 1), (.n 645, 3), (.n 699, 18), (.n 775, 1), (.n 776, 3), (.n 823, 16), (.n 1370, 0), (.n 1371, 6), (.n 2309, 0), (.n 2310, 4), (.n 2331, 0), (.n 2332, 2), (.n 2809, 0), (.n 2810, 2)] Data.core354.params ([], []) ((Data.core354.body.drop 0).take 1428) = ([(.n 1371, 6), (.n 1370, 0), (.n 823, 16), (.n 776, 3), (.n 775, 1), (.n 699, 18), (.n 645, 3), (.n 644, 1), (.n 532, 22), (.n 478, 4), (.n 477, 1), (.n 366, 32), (.n 312, 6), (.n 311, 1), (.n 196, 27), (.n 152, 11), (.n 151, 1)], []) := by
  decide +kernel

end
end LeanVM.Guest
