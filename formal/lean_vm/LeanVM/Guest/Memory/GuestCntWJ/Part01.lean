module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_48 : kujStaticRange 48 26 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_74 : kujStaticRange 74 30 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_104 : kujStaticRange 104 25 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_129 : kujStaticRange 129 27 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_156 : kujStaticRange 156 26 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_182 : kujStaticRange 182 25 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_207 : kujStaticRange 207 26 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_233 : kujStaticRange 233 28 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_261 : kujStaticRange 261 30 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
