module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_724 : kwomStaticRange 724 15 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_739 : kwomStaticRange 739 15 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
