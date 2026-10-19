module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_181 : kwodStaticRange 181 1 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_182 : kwodStaticRange 182 1 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_183 : kwodStaticRange 183 1 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
