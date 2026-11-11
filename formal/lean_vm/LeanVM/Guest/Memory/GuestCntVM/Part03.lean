module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_318 : kvmStaticRange 318 1 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmsplit_319_0 : blockR (kvmlookJ 319) (kvmomLookJ 319) false [] Data.core319.params Data.core319.name (Data.core319.body.drop 0)
    ([], []) = some (⟨64765, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvmsplit_320_0 : blockR (kvmlookJ 320) (kvmomLookJ 320) false [] Data.core320.params Data.core320.name (Data.core320.body.drop 0)
    ([], []) = some (⟨66289, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvmsplit_321_0 : blockR (kvmlookJ 321) (kvmomLookJ 321) false [] Data.core321.params Data.core321.name (Data.core321.body.drop 0)
    ([], []) = some (⟨67125, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvmsplit_322_0 : blockR (kvmlookJ 322) (kvmomLookJ 322) false [] Data.core322.params Data.core322.name (Data.core322.body.drop 0)
    ([], []) = some (⟨71631, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_323 : kvmStaticRange 323 21 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_344 : kvmStaticRange 344 22 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
