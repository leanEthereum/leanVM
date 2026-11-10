module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_319 : kvkStaticRange 319 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_320_0 : blockR (kvklookJ 320) (kvkomLookJ 320) false [] Data.core320.params Data.core320.name (Data.core320.body.drop 0)
    ([], []) = some (⟨8268, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_321_0 : blockR (kvklookJ 321) (kvkomLookJ 321) false [] Data.core321.params Data.core321.name (Data.core321.body.drop 0)
    ([], []) = some (⟨8398, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_322_0 : blockR (kvklookJ 322) (kvkomLookJ 322) false [] Data.core322.params Data.core322.name (Data.core322.body.drop 0)
    ([], []) = some (⟨8746, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_323_0 : blockR (kvklookJ 323) (kvkomLookJ 323) false [] Data.core323.params Data.core323.name (Data.core323.body.drop 0)
    ([], []) = some (⟨10591, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_324 : kvkStaticRange 324 21 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_345 : kvkStaticRange 345 22 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
