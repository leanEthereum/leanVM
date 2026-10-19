module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_754 : kwomStaticRange 754 14 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_768 : kwomStaticRange 768 14 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
