module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_180 : StaticRange 180 1 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_181 : StaticRange 181 1 := by
  unfold StaticRange; decide +kernel

end
end LeanVM.Guest
