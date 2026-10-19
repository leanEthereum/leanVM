module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_444 : kwojStaticRange 444 30 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_474 : kwojStaticRange 474 30 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_504 : kwojStaticRange 504 30 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_534 : kwojStaticRange 534 30 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
