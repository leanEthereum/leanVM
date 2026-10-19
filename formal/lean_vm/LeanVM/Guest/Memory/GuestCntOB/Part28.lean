module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_974 : kwobStaticRange 974 11 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_985 : kwobStaticRange 985 11 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
