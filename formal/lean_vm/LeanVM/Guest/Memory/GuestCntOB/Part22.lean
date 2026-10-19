module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_782 : kwobStaticRange 782 14 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_796 : kwobStaticRange 796 14 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
