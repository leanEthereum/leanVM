module

public import LeanVM.Guest.B2C.KTempsBase

namespace LeanVM.Guest.B2C

@[expose] public section

set_option maxRecDepth 100000 in
theorem tmpsRange_0 : TmpsRange 0 12 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_12 : TmpsRange 12 3 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_15 : TmpsRange 15 1 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_18 : TmpsRange 18 40 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_58 : TmpsRange 58 12 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_70 : TmpsRange 70 40 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_110 : TmpsRange 110 40 := by
  unfold TmpsRange; decide +kernel

set_option maxRecDepth 100000 in
theorem tmpsRange_150 : TmpsRange 150 28 := by
  unfold TmpsRange; decide +kernel

end
end LeanVM.Guest.B2C
