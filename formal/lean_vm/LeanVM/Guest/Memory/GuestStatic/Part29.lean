module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_190 : StaticRange 190 1 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_191 : StaticRange 191 1 := by
  unfold StaticRange; decide +kernel

end
end LeanVM.Guest
