module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_838 : kwobStaticRange 838 14 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_852 : kwobStaticRange 852 14 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
