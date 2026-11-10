/-
  LeanVM.Guest.B1.Whir.CHonAlloc0

  Candidates 0..6's body allocations, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bodyStatic_0 : BodyStatic (osCfg 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_1 : BodyStatic (osCfg 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_2 : BodyStatic (osCfg 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_3 : BodyStatic (osCfg 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_4 : BodyStatic (osCfg 4) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_5 : BodyStatic (osCfg 5) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_6 : BodyStatic (osCfg 6) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
