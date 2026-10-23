module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_0 : kwdStaticRange 0 16 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_16_0 : noTopRet ((Data.core16.body.drop 0).take 222) = true ∧
    blockR (kwdlookJ 16) (kwdomLookJ 16) false [] Data.core16.params Data.core16.name ((Data.core16.body.drop 0).take 222) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_16_222 : noTopRet ((Data.core16.body.drop 222).take 276) = true ∧
    blockR (kwdlookJ 16) (kwdomLookJ 16) false [] Data.core16.params Data.core16.name ((Data.core16.body.drop 222).take 276) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_16_498 : blockR (kwdlookJ 16) (kwdomLookJ 16) false [] Data.core16.params Data.core16.name (Data.core16.body.drop 498) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_17_0 : noTopRet ((Data.core17.body.drop 0).take 220) = true ∧
    blockR (kwdlookJ 17) (kwdomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 0).take 220) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_17_220 : noTopRet ((Data.core17.body.drop 220).take 1) = true ∧
    blockR (kwdlookJ 17) (kwdomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 220).take 1) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_17_221 : noTopRet ((Data.core17.body.drop 221).take 11) = true ∧
    blockR (kwdlookJ 17) (kwdomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 221).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
