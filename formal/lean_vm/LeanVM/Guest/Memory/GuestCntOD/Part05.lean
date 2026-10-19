module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_159 : kwodStaticRange 159 19 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_178 : kwodStaticRange 178 1 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_179 : kwodStaticRange 179 1 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_180 : kwodStaticRange 180 1 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
