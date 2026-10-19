module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_984 : StaticRange 984 10 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem staticRange_994 : StaticRange 994 10 := by
  unfold StaticRange; decide +kernel

end
end LeanVM.Guest
