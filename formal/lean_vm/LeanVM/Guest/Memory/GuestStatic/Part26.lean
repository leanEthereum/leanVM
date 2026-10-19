module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_1004 : StaticRange 1004 10 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_1014 : StaticRange 1014 10 := by
  unfold StaticRange; decide +kernel

end
end LeanVM.Guest
