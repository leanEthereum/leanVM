module

public import LeanVM.Guest.Memory.GuestCntOS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwosstaticRange_866 : kwosStaticRange 866 14 := by
  unfold kwosStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwosstaticRange_880 : kwosStaticRange 880 14 := by
  unfold kwosStaticRange; decide +kernel

end
end LeanVM.Guest
