module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_694 : kwobStaticRange 694 15 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_709 : kwobStaticRange 709 15 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
