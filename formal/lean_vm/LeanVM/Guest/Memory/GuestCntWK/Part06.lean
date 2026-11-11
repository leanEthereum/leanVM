module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_987 : kukStaticRange 987 30 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_1017 : kukStaticRange 1017 20 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
