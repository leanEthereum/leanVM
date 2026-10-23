module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_974 : kwomStaticRange 974 11 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_985 : kwomStaticRange 985 11 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
