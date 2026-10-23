module

public import LeanVM.Guest.Memory.GuestCntOD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwodstaticRange_602 : kwodStaticRange 602 16 := by
  unfold kwodStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwodstaticRange_618 : kwodStaticRange 618 16 := by
  unfold kwodStaticRange; decide +kernel

end
end LeanVM.Guest
