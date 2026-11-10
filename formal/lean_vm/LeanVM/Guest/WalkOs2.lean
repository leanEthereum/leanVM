/-
  LeanVM.Guest.WalkOs2

  The cut obligations (`CutsKnown`) of `open_stacked__L14` to `open_stacked__L20`
  (`os_cutsKnown`, `WalkOsOk2.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsOk2

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem walk_346 : CutsKnown 346 :=
  os_cutsKnown (m := 14) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_14 osOk_346

set_option maxRecDepth 100000 in
theorem walk_347 : CutsKnown 347 :=
  os_cutsKnown (m := 15) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_15 osOk_347

set_option maxRecDepth 100000 in
theorem walk_348 : CutsKnown 348 :=
  os_cutsKnown (m := 16) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_16 osOk_348

set_option maxRecDepth 100000 in
theorem walk_349 : CutsKnown 349 :=
  os_cutsKnown (m := 17) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_17 osOk_349

set_option maxRecDepth 100000 in
theorem walk_350 : CutsKnown 350 :=
  os_cutsKnown (m := 18) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_18 osOk_350

set_option maxRecDepth 100000 in
theorem walk_351 : CutsKnown 351 :=
  os_cutsKnown (m := 19) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_19 osOk_351

set_option maxRecDepth 100000 in
theorem walk_352 : CutsKnown 352 :=
  os_cutsKnown (m := 20) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_20 osOk_352

end
end LeanVM.Guest.End
