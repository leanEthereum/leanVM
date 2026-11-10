/-
  LeanVM.Guest.B1.Whir.CHonStatic1

  Candidates 7..13's honest buffers' configuration facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honStatic_7 : HonStatic (osCfg 7) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_8 : HonStatic (osCfg 8) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_9 : HonStatic (osCfg 9) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_10 : HonStatic (osCfg 10) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_11 : HonStatic (osCfg 11) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_12 : HonStatic (osCfg 12) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_13 : HonStatic (osCfg 13) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
