module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_564 : kwomStaticRange 564 22 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_586 : kwomStaticRange 586 16 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
