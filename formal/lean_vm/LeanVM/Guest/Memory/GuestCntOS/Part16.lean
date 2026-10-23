module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_602 : kwosStaticRange 602 16 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_618 : kwosStaticRange 618 16 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
