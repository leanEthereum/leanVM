/-
  LeanVM.Guest.B1.Whir.CHonStatic0

  Candidates 0..6's honest buffers' configuration facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honStatic_0 : HonStatic (osCfg 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_1 : HonStatic (osCfg 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_2 : HonStatic (osCfg 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_3 : HonStatic (osCfg 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_4 : HonStatic (osCfg 4) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_5 : HonStatic (osCfg 5) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_6 : HonStatic (osCfg 6) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
