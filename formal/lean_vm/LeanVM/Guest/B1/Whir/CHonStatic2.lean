/-
  LeanVM.Guest.B1.Whir.CHonStatic2

  Candidates 14..20's honest buffers' configuration facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honStatic_14 : HonStatic (osCfg 14) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_15 : HonStatic (osCfg 15) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_16 : HonStatic (osCfg 16) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_17 : HonStatic (osCfg 17) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_18 : HonStatic (osCfg 18) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_19 : HonStatic (osCfg 19) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_20 : HonStatic (osCfg 20) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
