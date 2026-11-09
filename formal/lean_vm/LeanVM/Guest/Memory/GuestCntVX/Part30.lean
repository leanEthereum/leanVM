module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_936 : kvxStaticRange 936 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_950 : kvxStaticRange 950 13 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_963 : kvxStaticRange 963 9 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
