module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_786 : kvdStaticRange 786 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_804 : kvdStaticRange 804 17 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
