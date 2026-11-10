module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_336 : kwxStaticRange 336 6 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_342 : kwxStaticRange 342 6 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
