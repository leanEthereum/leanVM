module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_961 : kvxStaticRange 961 14 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_975 : kvxStaticRange 975 12 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
