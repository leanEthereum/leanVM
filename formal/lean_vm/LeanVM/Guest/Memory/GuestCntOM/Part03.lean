module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_17 : kwomStaticRange 17 1 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
