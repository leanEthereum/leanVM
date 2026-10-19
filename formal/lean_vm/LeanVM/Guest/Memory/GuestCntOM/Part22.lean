module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_782 : kwomStaticRange 782 14 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_796 : kwomStaticRange 796 14 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
