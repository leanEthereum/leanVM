module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_939 : kvdStaticRange 939 15 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_954 : kvdStaticRange 954 14 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
