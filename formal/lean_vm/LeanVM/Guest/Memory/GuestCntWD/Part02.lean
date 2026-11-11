module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_288 : kudStaticRange 288 25 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_313 : kudStaticRange 313 3 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
