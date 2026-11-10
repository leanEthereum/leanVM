module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_319 : kvjStaticRange 319 1 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_320_0 : blockR (kvjlookJ 320) (kvjomLookJ 320) false [] Data.core320.params Data.core320.name (Data.core320.body.drop 0)
    ([], []) = some (⟨15304, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_321_0 : blockR (kvjlookJ 321) (kvjomLookJ 321) false [] Data.core321.params Data.core321.name (Data.core321.body.drop 0)
    ([], []) = some (⟨15490, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_322_0 : blockR (kvjlookJ 322) (kvjomLookJ 322) false [] Data.core322.params Data.core322.name (Data.core322.body.drop 0)
    ([], []) = some (⟨16210, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjsplit_323_0 : blockR (kvjlookJ 323) (kvjomLookJ 323) false [] Data.core323.params Data.core323.name (Data.core323.body.drop 0)
    ([], []) = some (⟨16979, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_324 : kvjStaticRange 324 21 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_345 : kvjStaticRange 345 22 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
