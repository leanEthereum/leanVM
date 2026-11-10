module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_319 : kvxStaticRange 319 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_320_0 : blockR (kvxlookJ 320) (kvxomLookJ 320) false [] Data.core320.params Data.core320.name (Data.core320.body.drop 0)
    ([], []) = some (⟨55819, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_321_0 : blockR (kvxlookJ 321) (kvxomLookJ 321) false [] Data.core321.params Data.core321.name (Data.core321.body.drop 0)
    ([], []) = some (⟨56909, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_322_0 : blockR (kvxlookJ 322) (kvxomLookJ 322) false [] Data.core322.params Data.core322.name (Data.core322.body.drop 0)
    ([], []) = some (⟨57766, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxsplit_323_0 : blockR (kvxlookJ 323) (kvxomLookJ 323) false [] Data.core323.params Data.core323.name (Data.core323.body.drop 0)
    ([], []) = some (⟨60292, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_324 : kvxStaticRange 324 21 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_345 : kvxStaticRange 345 22 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
