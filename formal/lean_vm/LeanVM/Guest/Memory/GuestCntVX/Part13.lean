module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxsplit_351_2372 : blockR (kvxlookJ 351) (kvxomLookJ 351) false [(.n 151, 1), (.n 152, 15), (.n 196, 36), (.n 310, 1), (.n 311, 8), (.n 365, 37), (.n 478, 1), (.n 479, 5), (.n 533, 25), (.n 645, 1), (.n 646, 4), (.n 700, 19), (.n 812, 1), (.n 813, 3), (.n 867, 16), (.n 942, 1), (.n 943, 3), (.n 990, 15), (.n 1719, 0), (.n 1720, 9), (.n 1896, 0), (.n 1897, 4), (.n 2538, 0), (.n 2539, 3), (.n 2660, 0), (.n 2661, 2), (.n 2910, 0), (.n 2911, 2)] Data.core351.params Data.core351.name (Data.core351.body.drop 2372)
    ([(.n 1897, 4), (.n 1896, 0), (.n 1720, 9), (.n 1719, 0), (.n 990, 15), (.n 943, 3), (.n 942, 1), (.n 867, 16), (.n 813, 3), (.n 812, 1), (.n 700, 19), (.n 646, 4), (.n 645, 1), (.n 533, 25), (.n 479, 5), (.n 478, 1), (.n 365, 37), (.n 311, 8), (.n 310, 1), (.n 196, 36), (.n 152, 15), (.n 151, 1)], []) = some (⟨1471, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_352 : kvxStaticRange 352 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_353 : kvxStaticRange 353 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_354_0 : noTopRet ((Data.core354.body.drop 0).take 1428) = true ∧
    blockR (kvxlookJ 354) (kvxomLookJ 354) false [(.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 311, 1), (.n 312, 6), (.n 366, 32), (.n 477, 1), (.n 478, 4), (.n 532, 23), (.n 645, 1), (.n 646, 3), (.n 700, 18), (.n 776, 1), (.n 777, 3), (.n 824, 16), (.n 1371, 0), (.n 1372, 6), (.n 2310, 0), (.n 2311, 4), (.n 2332, 0), (.n 2333, 2), (.n 2886, 0), (.n 2887, 2)] Data.core354.params Data.core354.name ((Data.core354.body.drop 0).take 1428)
      ([], []) = some (⟨13189, []⟩, []) ∧
    blockEnv false [(.n 151, 1), (.n 152, 11), (.n 196, 27), (.n 311, 1), (.n 312, 6), (.n 366, 32), (.n 477, 1), (.n 478, 4), (.n 532, 23), (.n 645, 1), (.n 646, 3), (.n 700, 18), (.n 776, 1), (.n 777, 3), (.n 824, 16), (.n 1371, 0), (.n 1372, 6), (.n 2310, 0), (.n 2311, 4), (.n 2332, 0), (.n 2333, 2), (.n 2886, 0), (.n 2887, 2)] Data.core354.params ([], []) ((Data.core354.body.drop 0).take 1428) = ([(.n 1372, 6), (.n 1371, 0), (.n 824, 16), (.n 777, 3), (.n 776, 1), (.n 700, 18), (.n 646, 3), (.n 645, 1), (.n 532, 23), (.n 478, 4), (.n 477, 1), (.n 366, 32), (.n 312, 6), (.n 311, 1), (.n 196, 27), (.n 152, 11), (.n 151, 1)], []) := by
  decide +kernel

end
end LeanVM.Guest
