module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_804 : StaticRange 804 30 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_834 : StaticRange 834 30 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_864 : StaticRange 864 30 := by
  unfold StaticRange; decide +kernel

end
end LeanVM.Guest
