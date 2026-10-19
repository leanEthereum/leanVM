module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_634 : kwobStaticRange 634 15 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_649 : kwobStaticRange 649 15 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
