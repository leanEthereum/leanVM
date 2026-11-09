/-
  LeanVM.Guest.WalkOs1

  The cut obligations (`CutsKnown`) of `open_stacked__L7` to `open_stacked__L13`
  (`os_cutsKnown`, `WalkOsOk1.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsOk1

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem walk_310 : CutsKnown 310 :=
  os_cutsKnown (m := 7) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_7 osOk_310

set_option maxRecDepth 100000 in
theorem walk_311 : CutsKnown 311 :=
  os_cutsKnown (m := 8) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_8 osOk_311

set_option maxRecDepth 100000 in
theorem walk_312 : CutsKnown 312 :=
  os_cutsKnown (m := 9) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_9 osOk_312

set_option maxRecDepth 100000 in
theorem walk_313 : CutsKnown 313 :=
  os_cutsKnown (m := 10) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_10 osOk_313

set_option maxRecDepth 100000 in
theorem walk_314 : CutsKnown 314 :=
  os_cutsKnown (m := 11) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_11 osOk_314

set_option maxRecDepth 100000 in
theorem walk_315 : CutsKnown 315 :=
  os_cutsKnown (m := 12) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_12 osOk_315

set_option maxRecDepth 100000 in
theorem walk_316 : CutsKnown 316 :=
  os_cutsKnown (m := 13) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_13 osOk_316

end
end LeanVM.Guest.End
