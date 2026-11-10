module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_319 : kvdStaticRange 319 1 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdsplit_320_0 : blockR (kvdlookJ 320) (kvdomLookJ 320) false [] Data.core320.params Data.core320.name (Data.core320.body.drop 0)
    ([], []) = some (⟨23860, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvdsplit_321_0 : blockR (kvdlookJ 321) (kvdomLookJ 321) false [] Data.core321.params Data.core321.name (Data.core321.body.drop 0)
    ([], []) = some (⟨25077, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvdsplit_322_0 : blockR (kvdlookJ 322) (kvdomLookJ 322) false [] Data.core322.params Data.core322.name (Data.core322.body.drop 0)
    ([], []) = some (⟨26985, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvdsplit_323_0 : blockR (kvdlookJ 323) (kvdomLookJ 323) false [] Data.core323.params Data.core323.name (Data.core323.body.drop 0)
    ([], []) = some (⟨28229, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_324 : kvdStaticRange 324 21 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_345 : kvdStaticRange 345 22 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
