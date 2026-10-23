module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_925 : kwomStaticRange 925 28 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_953 : kwomStaticRange 953 21 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
