/-
  LeanVM.Guest.B1.Whir.CHonAlloc1

  Candidates 7..13's body allocations, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bodyStatic_7 : BodyStatic (osCfg 7) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_8 : BodyStatic (osCfg 8) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_9 : BodyStatic (osCfg 9) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_10 : BodyStatic (osCfg 10) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_11 : BodyStatic (osCfg 11) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_12 : BodyStatic (osCfg 12) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_13 : BodyStatic (osCfg 13) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
