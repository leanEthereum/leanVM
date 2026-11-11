module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_711 : kvxStaticRange 711 17 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_728 : kvxStaticRange 728 17 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
