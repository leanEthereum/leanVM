module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_48 : kumStaticRange 48 26 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_74 : kumStaticRange 74 30 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_104 : kumStaticRange 104 25 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_129 : kumStaticRange 129 27 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_156 : kumStaticRange 156 26 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_182 : kumStaticRange 182 25 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_207 : kumStaticRange 207 26 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_233 : kumStaticRange 233 28 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_261 : kumStaticRange 261 30 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
