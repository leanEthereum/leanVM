module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1227 : kvxStaticRange 1227 19 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_1246 : kvxStaticRange 1246 11 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
