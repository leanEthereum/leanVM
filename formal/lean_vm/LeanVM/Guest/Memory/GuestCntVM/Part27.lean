module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_813 : kvmStaticRange 813 17 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_830 : kvmStaticRange 830 16 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
