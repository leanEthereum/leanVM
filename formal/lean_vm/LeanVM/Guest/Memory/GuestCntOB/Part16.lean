module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_602 : kwobStaticRange 602 16 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_618 : kwobStaticRange 618 16 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
