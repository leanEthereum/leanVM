module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_337 : kwsStaticRange 337 3 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_340 : kwsStaticRange 340 3 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
