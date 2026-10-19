module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_1018 : kwobStaticRange 1018 10 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_1028 : kwobStaticRange 1028 10 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_1038 : kwobStaticRange 1038 5 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
