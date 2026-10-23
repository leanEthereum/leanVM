module

public import LeanVM.Guest.Memory.GuestCntOM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwomstaticRange_602 : kwomStaticRange 602 16 := by
  unfold kwomStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwomstaticRange_618 : kwomStaticRange 618 16 := by
  unfold kwomStaticRange; decide +kernel

end
end LeanVM.Guest
