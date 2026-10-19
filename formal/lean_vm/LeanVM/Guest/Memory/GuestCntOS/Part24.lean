module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_838 : kwosStaticRange 838 14 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_852 : kwosStaticRange 852 14 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
