/-
  LeanVM.Guest.B1.Whir.CHonStatic3

  Candidates 21..27's honest buffers' configuration facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honStatic_21 : HonStatic (osCfg 21) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_22 : HonStatic (osCfg 22) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_23 : HonStatic (osCfg 23) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_24 : HonStatic (osCfg 24) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_25 : HonStatic (osCfg 25) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_26 : HonStatic (osCfg 26) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_27 : HonStatic (osCfg 27) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
