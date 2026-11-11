module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_320 : kukStaticRange 320 17 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_337 : kukStaticRange 337 7 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
