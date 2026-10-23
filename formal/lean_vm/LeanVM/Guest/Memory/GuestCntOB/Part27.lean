module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_925 : kwobStaticRange 925 28 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_953 : kwobStaticRange 953 21 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
