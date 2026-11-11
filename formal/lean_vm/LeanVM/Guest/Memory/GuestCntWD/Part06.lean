module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_987 : kudStaticRange 987 30 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_1017 : kudStaticRange 1017 20 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
