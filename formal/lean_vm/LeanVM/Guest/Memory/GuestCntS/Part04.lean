module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_336 : kwsStaticRange 336 6 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_342 : kwsStaticRange 342 6 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
