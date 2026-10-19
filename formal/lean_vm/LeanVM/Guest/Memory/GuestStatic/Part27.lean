module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_1024 : StaticRange 1024 10 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_1034 : StaticRange 1034 9 := by
  unfold StaticRange; decide +kernel

end
end LeanVM.Guest
