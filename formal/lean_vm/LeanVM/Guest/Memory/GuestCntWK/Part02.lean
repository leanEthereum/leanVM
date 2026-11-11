module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_289 : kukStaticRange 289 20 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_309 : kukStaticRange 309 3 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
