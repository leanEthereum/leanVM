module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_314 : kvsStaticRange 314 1 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_315_0 : blockR (kvslookJ 315) (kvsomLookJ 315) false [] Data.core315.params Data.core315.name (Data.core315.body.drop 0)
    ([], []) = some (⟨10869, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_316_0 : blockR (kvslookJ 316) (kvsomLookJ 316) false [] Data.core316.params Data.core316.name (Data.core316.body.drop 0)
    ([], []) = some (⟨11481, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_317 : kvsStaticRange 317 21 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_338 : kvsStaticRange 338 22 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_360 : kvsStaticRange 360 23 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
