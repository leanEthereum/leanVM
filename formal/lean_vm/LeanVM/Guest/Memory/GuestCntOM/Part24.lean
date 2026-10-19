module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_838 : kwomStaticRange 838 14 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_852 : kwomStaticRange 852 14 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
