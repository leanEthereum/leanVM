module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_14 : kwobStaticRange 14 1 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
