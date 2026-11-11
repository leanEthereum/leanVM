module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_313 : kwsStaticRange 313 3 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_316 : kwsStaticRange 316 3 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
