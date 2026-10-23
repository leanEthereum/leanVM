module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_186 : StaticRange 186 1 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_187 : StaticRange 187 1 := by
  unfold StaticRange; decide +kernel

end
end LeanVM.Guest
