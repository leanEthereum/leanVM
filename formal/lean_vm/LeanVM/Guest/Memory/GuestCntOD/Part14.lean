module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_444 : kwodStaticRange 444 30 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_474 : kwodStaticRange 474 30 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_504 : kwodStaticRange 504 30 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_534 : kwodStaticRange 534 30 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
