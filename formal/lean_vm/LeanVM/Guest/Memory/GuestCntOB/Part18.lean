module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_664 : kwobStaticRange 664 15 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_679 : kwobStaticRange 679 15 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
