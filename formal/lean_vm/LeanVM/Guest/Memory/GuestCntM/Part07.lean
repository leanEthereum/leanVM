module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_622 : kwmStaticRange 622 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_652 : kwmStaticRange 652 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_682 : kwmStaticRange 682 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_712 : kwmStaticRange 712 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_742 : kwmStaticRange 742 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_772 : kwmStaticRange 772 30 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
