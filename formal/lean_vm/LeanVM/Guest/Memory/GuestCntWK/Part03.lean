module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_316 : kukStaticRange 316 3 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_319 : kukStaticRange 319 2 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
