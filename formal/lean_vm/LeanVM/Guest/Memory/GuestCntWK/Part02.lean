module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_291 : kukStaticRange 291 18 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_309 : kukStaticRange 309 7 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
