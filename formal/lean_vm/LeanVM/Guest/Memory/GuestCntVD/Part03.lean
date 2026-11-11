module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_314 : kvdStaticRange 314 1 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdsplit_315_0 : blockR (kvdlookJ 315) (kvdomLookJ 315) false [] Data.core315.params Data.core315.name (Data.core315.body.drop 0)
    ([], []) = some (⟨23860, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvdsplit_316_0 : blockR (kvdlookJ 316) (kvdomLookJ 316) false [] Data.core316.params Data.core316.name (Data.core316.body.drop 0)
    ([], []) = some (⟨25077, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_317 : kvdStaticRange 317 21 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_338 : kvdStaticRange 338 22 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_360 : kvdStaticRange 360 23 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
