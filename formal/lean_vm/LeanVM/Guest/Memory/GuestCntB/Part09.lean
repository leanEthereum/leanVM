module

public import LeanVM.Guest.Memory.GuestCntB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwbstaticRange_198 : kwbStaticRange 198 30 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_228 : kwbStaticRange 228 28 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_256 : kwbStaticRange 256 28 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_284 : kwbStaticRange 284 28 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_312 : kwbStaticRange 312 28 := by
  unfold kwbStaticRange; decide +kernel

end
end LeanVM.Guest
