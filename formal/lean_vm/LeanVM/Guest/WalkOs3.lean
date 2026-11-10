/-
  LeanVM.Guest.WalkOs3

  The cut obligations (`CutsKnown`) of `open_stacked__L21` to `open_stacked__L27`
  (`os_cutsKnown`, `WalkOsOk3.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsOk3

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem walk_353 : CutsKnown 353 :=
  os_cutsKnown (m := 21) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_21 osOk_353

set_option maxRecDepth 100000 in
theorem walk_354 : CutsKnown 354 :=
  os_cutsKnown (m := 22) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_22 osOk_354

set_option maxRecDepth 100000 in
theorem walk_355 : CutsKnown 355 :=
  os_cutsKnown (m := 23) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_23 osOk_355

set_option maxRecDepth 100000 in
theorem walk_356 : CutsKnown 356 :=
  os_cutsKnown (m := 24) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_24 osOk_356

set_option maxRecDepth 100000 in
theorem walk_357 : CutsKnown 357 :=
  os_cutsKnown (m := 25) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_25 osOk_357

set_option maxRecDepth 100000 in
theorem walk_358 : CutsKnown 358 :=
  os_cutsKnown (m := 26) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_26 osOk_358

set_option maxRecDepth 100000 in
theorem walk_359 : CutsKnown 359 :=
  os_cutsKnown (m := 27) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_27 osOk_359

end
end LeanVM.Guest.End
