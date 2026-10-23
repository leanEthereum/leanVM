module

public import LeanVM.Guest.Memory.GuestCntB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwbstaticRange_340 : kwbStaticRange 340 28 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_368 : kwbStaticRange 368 28 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_396 : kwbStaticRange 396 28 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_424 : kwbStaticRange 424 28 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_452 : kwbStaticRange 452 30 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_482 : kwbStaticRange 482 30 := by
  unfold kwbStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwbstaticRange_512 : kwbStaticRange 512 30 := by
  unfold kwbStaticRange; decide +kernel

end
end LeanVM.Guest
