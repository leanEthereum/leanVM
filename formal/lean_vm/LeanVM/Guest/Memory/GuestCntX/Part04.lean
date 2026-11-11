module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_337 : kwxStaticRange 337 7 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_344 : kwxStaticRange 344 6 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
