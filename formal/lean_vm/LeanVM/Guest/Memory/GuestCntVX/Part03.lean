module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_314 : kvxStaticRange 314 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_315_0 : blockR (kvxlookJ 315) (kvxomLookJ 315) false [] Data.core315.params Data.core315.name (Data.core315.body.drop 0)
    ([], []) = some (⟨55819, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_316_0 : blockR (kvxlookJ 316) (kvxomLookJ 316) false [] Data.core316.params Data.core316.name (Data.core316.body.drop 0)
    ([], []) = some (⟨56909, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_317 : kvxStaticRange 317 21 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_338 : kvxStaticRange 338 22 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_360 : kvxStaticRange 360 23 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
