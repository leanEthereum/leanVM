module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_318 : kvxStaticRange 318 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_319_0 : blockR (kvxlookJ 319) (kvxomLookJ 319) false [] Data.core319.params Data.core319.name (Data.core319.body.drop 0)
    ([], []) = some (⟨55819, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_320_0 : blockR (kvxlookJ 320) (kvxomLookJ 320) false [] Data.core320.params Data.core320.name (Data.core320.body.drop 0)
    ([], []) = some (⟨56909, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_321_0 : blockR (kvxlookJ 321) (kvxomLookJ 321) false [] Data.core321.params Data.core321.name (Data.core321.body.drop 0)
    ([], []) = some (⟨57766, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_322_0 : blockR (kvxlookJ 322) (kvxomLookJ 322) false [] Data.core322.params Data.core322.name (Data.core322.body.drop 0)
    ([], []) = some (⟨60292, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_323 : kvxStaticRange 323 21 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_344 : kvxStaticRange 344 22 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
