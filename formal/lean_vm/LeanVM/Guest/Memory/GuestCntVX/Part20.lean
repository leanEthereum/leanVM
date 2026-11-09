module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_556 : kvxStaticRange 556 18 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_574 : kvxStaticRange 574 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
