module

public import LeanVM.Guest.Memory.GuestStatic.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem split_17_432 : noTopRet ((Data.core17.body.drop 432).take 28) = true ∧
    blockR (lookJ 17) (omLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 432).take 28) ([], []) = some (⟨29, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem split_17_460 : noTopRet ((Data.core17.body.drop 460).take 12) = true ∧
    blockR (lookJ 17) (omLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 460).take 12) ([], []) = some (⟨29, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
