module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_786 : kvxStaticRange 786 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_804 : kvxStaticRange 804 17 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
