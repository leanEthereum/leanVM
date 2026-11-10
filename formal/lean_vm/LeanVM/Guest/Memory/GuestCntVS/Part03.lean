module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_319 : kvsStaticRange 319 1 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_320_0 : blockR (kvslookJ 320) (kvsomLookJ 320) false [] Data.core320.params Data.core320.name (Data.core320.body.drop 0)
    ([], []) = some (⟨10869, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_321_0 : blockR (kvslookJ 321) (kvsomLookJ 321) false [] Data.core321.params Data.core321.name (Data.core321.body.drop 0)
    ([], []) = some (⟨11481, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_322_0 : blockR (kvslookJ 322) (kvsomLookJ 322) false [] Data.core322.params Data.core322.name (Data.core322.body.drop 0)
    ([], []) = some (⟨12232, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_323_0 : blockR (kvslookJ 323) (kvsomLookJ 323) false [] Data.core323.params Data.core323.name (Data.core323.body.drop 0)
    ([], []) = some (⟨12789, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_324 : kvsStaticRange 324 21 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_345 : kvsStaticRange 345 22 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
