module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_924 : kujStaticRange 924 30 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_954 : kujStaticRange 954 30 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_984 : kujStaticRange 984 30 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_1014 : kujStaticRange 1014 30 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_1044 : kujStaticRange 1044 11 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
