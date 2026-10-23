module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_810 : kwobStaticRange 810 14 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_824 : kwobStaticRange 824 14 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
