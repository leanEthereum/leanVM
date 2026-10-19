module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_810 : kwomStaticRange 810 14 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_824 : kwomStaticRange 824 14 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
