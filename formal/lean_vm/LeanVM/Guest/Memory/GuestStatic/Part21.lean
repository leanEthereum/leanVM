module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_624 : StaticRange 624 30 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_654 : StaticRange 654 30 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_684 : StaticRange 684 30 := by
  unfold StaticRange; decide +kernel

end
end LeanVM.Guest
