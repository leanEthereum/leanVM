module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_866 : kwobStaticRange 866 14 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_880 : kwobStaticRange 880 14 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
