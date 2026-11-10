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
theorem walk_339 : CutsKnown 339 :=
  os_cutsKnown (m := 7) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_7 osOk_339

set_option maxRecDepth 100000 in
theorem walk_340 : CutsKnown 340 :=
  os_cutsKnown (m := 8) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_8 osOk_340

set_option maxRecDepth 100000 in
theorem walk_341 : CutsKnown 341 :=
  os_cutsKnown (m := 9) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_9 osOk_341

set_option maxRecDepth 100000 in
theorem walk_342 : CutsKnown 342 :=
  os_cutsKnown (m := 10) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_10 osOk_342

set_option maxRecDepth 100000 in
theorem walk_343 : CutsKnown 343 :=
  os_cutsKnown (m := 11) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_11 osOk_343

set_option maxRecDepth 100000 in
theorem walk_344 : CutsKnown 344 :=
  os_cutsKnown (m := 12) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_12 osOk_344

set_option maxRecDepth 100000 in
theorem walk_345 : CutsKnown 345 :=
  os_cutsKnown (m := 13) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_13 osOk_345

end
end LeanVM.Guest.End
