module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_318 : kvjStaticRange 318 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_319_0 : blockR (kvjlookJ 319) (kvjomLookJ 319) false [] Data.core319.params Data.core319.name (Data.core319.body.drop 0)
    ([], []) = some (⟨15304, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_320_0 : blockR (kvjlookJ 320) (kvjomLookJ 320) false [] Data.core320.params Data.core320.name (Data.core320.body.drop 0)
    ([], []) = some (⟨15490, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_321_0 : blockR (kvjlookJ 321) (kvjomLookJ 321) false [] Data.core321.params Data.core321.name (Data.core321.body.drop 0)
    ([], []) = some (⟨16210, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_322_0 : blockR (kvjlookJ 322) (kvjomLookJ 322) false [] Data.core322.params Data.core322.name (Data.core322.body.drop 0)
    ([], []) = some (⟨16979, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_323 : kvjStaticRange 323 21 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_344 : kvjStaticRange 344 22 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
