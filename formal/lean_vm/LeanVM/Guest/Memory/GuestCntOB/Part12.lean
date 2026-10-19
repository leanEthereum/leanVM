module

public import LeanVM.Guest.Memory.GuestCntOB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwobstaticRange_202 : kwobStaticRange 202 1 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_203 : kwobStaticRange 203 1 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_204 : kwobStaticRange 204 30 := by
  unfold kwobStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwobstaticRange_234 : kwobStaticRange 234 30 := by
  unfold kwobStaticRange; decide +kernel

end
end LeanVM.Guest
