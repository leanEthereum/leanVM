module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_191 : kwoxStaticRange 191 2 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_193 : kwoxStaticRange 193 1 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_194 : kwoxStaticRange 194 1 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
