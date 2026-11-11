module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_574 : kvxStaticRange 574 19 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_593 : kvxStaticRange 593 19 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
