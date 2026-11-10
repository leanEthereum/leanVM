module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_618 : kvdStaticRange 618 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_636 : kvdStaticRange 636 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
