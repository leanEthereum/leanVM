module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_894 : kwobStaticRange 894 14 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_908 : kwobStaticRange 908 17 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
