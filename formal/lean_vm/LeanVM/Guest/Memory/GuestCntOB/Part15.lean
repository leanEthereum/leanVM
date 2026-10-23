module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_564 : kwobStaticRange 564 22 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_586 : kwobStaticRange 586 16 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
