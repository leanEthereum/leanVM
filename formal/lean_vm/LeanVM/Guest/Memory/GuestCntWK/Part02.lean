module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_320 : kukStaticRange 320 18 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_338 : kukStaticRange 338 3 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
