module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_15 : kwomStaticRange 15 2 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
