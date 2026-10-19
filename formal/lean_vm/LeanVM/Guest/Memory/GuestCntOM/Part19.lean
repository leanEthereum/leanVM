module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_694 : kwomStaticRange 694 15 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_709 : kwomStaticRange 709 15 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
