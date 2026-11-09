module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_20 : kwsStaticRange 20 16 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
