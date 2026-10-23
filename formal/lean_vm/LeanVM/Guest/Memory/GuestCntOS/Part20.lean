module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_724 : kwosStaticRange 724 15 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_739 : kwosStaticRange 739 15 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
