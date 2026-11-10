module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_293 : kukStaticRange 293 20 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_313 : kukStaticRange 313 3 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
