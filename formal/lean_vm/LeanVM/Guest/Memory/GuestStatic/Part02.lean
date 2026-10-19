module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem staticRange_15 : StaticRange 15 1 := by
  unfold StaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem split_16_0 : noTopRet ((Data.core16.body.drop 0).take 506) = true ∧
    blockR (lookJ 16) (omLookJ 16) false [] Data.core16.params Data.core16.name ((Data.core16.body.drop 0).take 506) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem split_16_506 : blockR (lookJ 16) (omLookJ 16) false [] Data.core16.params Data.core16.name (Data.core16.body.drop 506) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem split_17_0 : noTopRet ((Data.core17.body.drop 0).take 232) = true ∧
    blockR (lookJ 17) (omLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 0).take 232) ([], []) = some (⟨29, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
