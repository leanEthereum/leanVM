module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxsplit_17_512 : noTopRet ((Data.core17.body.drop 512).take 1) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 512).take 1) ([], []) = some (⟨6, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_17_513 : noTopRet ((Data.core17.body.drop 513).take 264) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 513).take 264) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_17_777 : blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name (Data.core17.body.drop 777) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_18 : kwxStaticRange 18 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_48 : kwxStaticRange 48 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_78 : kwxStaticRange 78 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_108 : kwxStaticRange 108 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_138 : kwxStaticRange 138 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_168 : kwxStaticRange 168 30 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
