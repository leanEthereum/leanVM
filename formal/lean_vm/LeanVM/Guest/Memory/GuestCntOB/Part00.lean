module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_0 : kwobStaticRange 0 11 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_11 : kwobStaticRange 11 1 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_12 : kwobStaticRange 12 2 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
