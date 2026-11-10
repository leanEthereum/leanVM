module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_352 : kvxStaticRange 352 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_353_0 : noTopRet ((Data.core353.body.drop 0).take 1794) = true ∧
    blockR (kvxlookJ 353) (kvxomLookJ 353) false [(.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 672, 1), (.n 673, 3), (.n 804, 18), (.n 1300, 0), (.n 1301, 6), (.n 2197, 0), (.n 2198, 3), (.n 2877, 0), (.n 2878, 2)] Data.core353.params Data.core353.name ((Data.core353.body.drop 0).take 1794)
      ([], []) = some (⟨13735, []⟩, []) ∧
    blockEnv false [(.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 672, 1), (.n 673, 3), (.n 804, 18), (.n 1300, 0), (.n 1301, 6), (.n 2197, 0), (.n 2198, 3), (.n 2877, 0), (.n 2878, 2)] Data.core353.params ([], []) ((Data.core353.body.drop 0).take 1794) = ([(.n 1301, 6), (.n 1300, 0), (.n 804, 18), (.n 673, 3), (.n 672, 1), (.n 592, 22), (.n 535, 4), (.n 534, 1), (.n 403, 31), (.n 346, 6), (.n 345, 1), (.n 213, 27), (.n 161, 10), (.n 160, 1)], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_353_1794 : noTopRet ((Data.core353.body.drop 1794).take 1794) = true ∧
    blockR (kvxlookJ 353) (kvxomLookJ 353) false [(.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 672, 1), (.n 673, 3), (.n 804, 18), (.n 1300, 0), (.n 1301, 6), (.n 2197, 0), (.n 2198, 3), (.n 2877, 0), (.n 2878, 2)] Data.core353.params Data.core353.name ((Data.core353.body.drop 1794).take 1794)
      ([(.n 1301, 6), (.n 1300, 0), (.n 804, 18), (.n 673, 3), (.n 672, 1), (.n 592, 22), (.n 535, 4), (.n 534, 1), (.n 403, 31), (.n 346, 6), (.n 345, 1), (.n 213, 27), (.n 161, 10), (.n 160, 1)], []) = some (⟨1117, []⟩, []) ∧
    blockEnv false [(.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 672, 1), (.n 673, 3), (.n 804, 18), (.n 1300, 0), (.n 1301, 6), (.n 2197, 0), (.n 2198, 3), (.n 2877, 0), (.n 2878, 2)] Data.core353.params ([(.n 1301, 6), (.n 1300, 0), (.n 804, 18), (.n 673, 3), (.n 672, 1), (.n 592, 22), (.n 535, 4), (.n 534, 1), (.n 403, 31), (.n 346, 6), (.n 345, 1), (.n 213, 27), (.n 161, 10), (.n 160, 1)], []) ((Data.core353.body.drop 1794).take 1794) = ([(.n 2878, 2), (.n 2877, 0), (.n 2198, 3), (.n 2197, 0), (.n 1301, 6), (.n 1300, 0), (.n 804, 18), (.n 673, 3), (.n 672, 1), (.n 592, 22), (.n 535, 4), (.n 534, 1), (.n 403, 31), (.n 346, 6), (.n 345, 1), (.n 213, 27), (.n 161, 10), (.n 160, 1)], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_353_3588 : blockR (kvxlookJ 353) (kvxomLookJ 353) false [(.n 160, 1), (.n 161, 10), (.n 213, 27), (.n 345, 1), (.n 346, 6), (.n 403, 31), (.n 534, 1), (.n 535, 4), (.n 592, 22), (.n 672, 1), (.n 673, 3), (.n 804, 18), (.n 1300, 0), (.n 1301, 6), (.n 2197, 0), (.n 2198, 3), (.n 2877, 0), (.n 2878, 2)] Data.core353.params Data.core353.name (Data.core353.body.drop 3588)
    ([(.n 2878, 2), (.n 2877, 0), (.n 2198, 3), (.n 2197, 0), (.n 1301, 6), (.n 1300, 0), (.n 804, 18), (.n 673, 3), (.n 672, 1), (.n 592, 22), (.n 535, 4), (.n 534, 1), (.n 403, 31), (.n 346, 6), (.n 345, 1), (.n 213, 27), (.n 161, 10), (.n 160, 1)], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
