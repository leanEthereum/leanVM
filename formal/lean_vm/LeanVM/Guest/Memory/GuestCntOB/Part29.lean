module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_996 : kwobStaticRange 996 11 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_1007 : kwobStaticRange 1007 11 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
