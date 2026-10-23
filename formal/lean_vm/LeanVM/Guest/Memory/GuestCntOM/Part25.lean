module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_866 : kwomStaticRange 866 14 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_880 : kwomStaticRange 880 14 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
