module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_342 : kukStaticRange 342 6 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_348 : kukStaticRange 348 6 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
