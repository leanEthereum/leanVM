module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_622 : kwsStaticRange 622 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_652 : kwsStaticRange 652 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_682 : kwsStaticRange 682 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_712 : kwsStaticRange 712 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_742 : kwsStaticRange 742 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_772 : kwsStaticRange 772 30 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
