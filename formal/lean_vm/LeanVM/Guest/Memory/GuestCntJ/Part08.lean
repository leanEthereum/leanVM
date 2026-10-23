module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjsplit_17_512 : noTopRet ((Data.core17.body.drop 512).take 1) = true ∧
    blockR (kwjlookJ 17) (kwjomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 512).take 1) ([], []) = some (⟨1, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjsplit_17_513 : noTopRet ((Data.core17.body.drop 513).take 264) = true ∧
    blockR (kwjlookJ 17) (kwjomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 513).take 264) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjsplit_17_777 : blockR (kwjlookJ 17) (kwjomLookJ 17) false [] Data.core17.params Data.core17.name (Data.core17.body.drop 777) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_18 : kwjStaticRange 18 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_48 : kwjStaticRange 48 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_78 : kwjStaticRange 78 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_108 : kwjStaticRange 108 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_138 : kwjStaticRange 138 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_168 : kwjStaticRange 168 30 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
