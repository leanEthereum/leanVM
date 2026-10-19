module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_996 : kwomStaticRange 996 11 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_1007 : kwomStaticRange 1007 11 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
