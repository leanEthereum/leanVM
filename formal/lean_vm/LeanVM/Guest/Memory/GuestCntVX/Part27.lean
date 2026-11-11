module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_813 : kvxStaticRange 813 17 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_830 : kvxStaticRange 830 16 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
