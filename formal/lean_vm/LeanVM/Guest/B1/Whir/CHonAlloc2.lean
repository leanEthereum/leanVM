/-
  LeanVM.Guest.B1.Whir.CHonAlloc2

  Candidates 14..20's body allocations, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bodyStatic_14 : BodyStatic (osCfg 14) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_15 : BodyStatic (osCfg 15) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_16 : BodyStatic (osCfg 16) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_17 : BodyStatic (osCfg 17) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_18 : BodyStatic (osCfg 18) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_19 : BodyStatic (osCfg 19) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_20 : BodyStatic (osCfg 20) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
