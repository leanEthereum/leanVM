module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_18 : kwodStaticRange 18 21 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_39 : kwodStaticRange 39 30 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_69 : kwodStaticRange 69 30 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_99 : kwodStaticRange 99 30 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_129 : kwodStaticRange 129 30 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
