module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_618 : kvmStaticRange 618 18 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_636 : kvmStaticRange 636 17 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
