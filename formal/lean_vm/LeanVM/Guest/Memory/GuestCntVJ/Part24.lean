module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_618 : kvjStaticRange 618 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_636 : kvjStaticRange 636 17 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
