module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_754 : kwobStaticRange 754 14 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_768 : kwobStaticRange 768 14 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
