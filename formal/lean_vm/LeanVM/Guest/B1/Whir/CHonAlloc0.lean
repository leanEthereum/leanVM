/-
  LeanVM.Guest.B1.Whir.CHonAlloc0

  The arms' body allocation statements at the first rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bodyAllocs_0 : BodyAllocs (osCfgR 0 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_1 : BodyAllocs (osCfgR 1 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_2 : BodyAllocs (osCfgR 2 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_3 : BodyAllocs (osCfgR 3 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_4 : BodyAllocs (osCfgR 4 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_5 : BodyAllocs (osCfgR 5 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_6 : BodyAllocs (osCfgR 6 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_7 : BodyAllocs (osCfgR 7 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_8 : BodyAllocs (osCfgR 8 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_9 : BodyAllocs (osCfgR 9 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyAllocs_10 : BodyAllocs (osCfgR 10 0) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
