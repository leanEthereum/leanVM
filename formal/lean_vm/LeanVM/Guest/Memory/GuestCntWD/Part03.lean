module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_316 : kudStaticRange 316 7 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_323 : kudStaticRange 323 30 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_353 : kudStaticRange 353 30 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
