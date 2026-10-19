module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_444 : kwosStaticRange 444 30 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_474 : kwosStaticRange 474 30 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_504 : kwosStaticRange 504 30 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_534 : kwosStaticRange 534 30 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
