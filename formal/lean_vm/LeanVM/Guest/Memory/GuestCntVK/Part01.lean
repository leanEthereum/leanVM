module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_48 : kvkStaticRange 48 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_78 : kvkStaticRange 78 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_108 : kvkStaticRange 108 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_138 : kvkStaticRange 138 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_168 : kvkStaticRange 168 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_198 : kvkStaticRange 198 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_228 : kvkStaticRange 228 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_258 : kvkStaticRange 258 30 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_288 : kvkStaticRange 288 15 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_303 : kvkStaticRange 303 1 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
