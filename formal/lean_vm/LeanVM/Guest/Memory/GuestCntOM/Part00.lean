module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_0 : kwomStaticRange 0 11 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_11 : kwomStaticRange 11 1 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_12 : kwomStaticRange 12 2 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
