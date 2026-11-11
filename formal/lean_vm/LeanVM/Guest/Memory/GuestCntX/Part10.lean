module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_1516 : kwxStaticRange 1516 19 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
