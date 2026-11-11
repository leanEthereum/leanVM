module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_314 : kvkStaticRange 314 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_315_0 : blockR (kvklookJ 315) (kvkomLookJ 315) false [] Data.core315.params Data.core315.name (Data.core315.body.drop 0)
    ([], []) = some (⟨8268, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_316_0 : blockR (kvklookJ 316) (kvkomLookJ 316) false [] Data.core316.params Data.core316.name (Data.core316.body.drop 0)
    ([], []) = some (⟨8398, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_317 : kvkStaticRange 317 21 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_338 : kvkStaticRange 338 22 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_360 : kvkStaticRange 360 23 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
