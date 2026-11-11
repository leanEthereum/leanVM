module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_314 : kvmStaticRange 314 1 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmsplit_315_0 : blockR (kvmlookJ 315) (kvmomLookJ 315) false [] Data.core315.params Data.core315.name (Data.core315.body.drop 0)
    ([], []) = some (⟨64765, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvmsplit_316_0 : blockR (kvmlookJ 316) (kvmomLookJ 316) false [] Data.core316.params Data.core316.name (Data.core316.body.drop 0)
    ([], []) = some (⟨66289, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_317 : kvmStaticRange 317 21 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_338 : kvmStaticRange 338 22 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_360 : kvmStaticRange 360 23 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
