module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_344 : kukStaticRange 344 6 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_350 : kukStaticRange 350 7 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
