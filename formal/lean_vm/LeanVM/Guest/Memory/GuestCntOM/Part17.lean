module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_634 : kwomStaticRange 634 15 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_649 : kwomStaticRange 649 15 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
