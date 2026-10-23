module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_1018 : kwosStaticRange 1018 10 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_1028 : kwosStaticRange 1028 10 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_1038 : kwosStaticRange 1038 5 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
