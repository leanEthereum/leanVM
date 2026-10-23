module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_1018 : kwomStaticRange 1018 10 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_1028 : kwomStaticRange 1028 10 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_1038 : kwomStaticRange 1038 5 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
