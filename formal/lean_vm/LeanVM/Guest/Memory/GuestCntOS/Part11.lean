module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_198 : kwosStaticRange 198 2 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_200 : kwosStaticRange 200 1 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_201 : kwosStaticRange 201 1 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
