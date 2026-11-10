/-
  LeanVM.Guest.WalkOs0

  The cut obligations (`CutsKnown`) of `open_stacked__L0` to `open_stacked__L6`
  (`os_cutsKnown`, `WalkOsOk0.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsOk0

namespace LeanVM.Guest.End

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem walk_332 : CutsKnown 332 :=
  os_cutsKnown (m := 0) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_0 osOk_332

set_option maxRecDepth 100000 in
theorem walk_333 : CutsKnown 333 :=
  os_cutsKnown (m := 1) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_1 osOk_333

set_option maxRecDepth 100000 in
theorem walk_334 : CutsKnown 334 :=
  os_cutsKnown (m := 2) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_2 osOk_334

set_option maxRecDepth 100000 in
theorem walk_335 : CutsKnown 335 :=
  os_cutsKnown (m := 3) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_3 osOk_335

set_option maxRecDepth 100000 in
theorem walk_336 : CutsKnown 336 :=
  os_cutsKnown (m := 4) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_4 osOk_336

set_option maxRecDepth 100000 in
theorem walk_337 : CutsKnown 337 :=
  os_cutsKnown (m := 5) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_5 osOk_337

set_option maxRecDepth 100000 in
theorem walk_338 : CutsKnown 338 :=
  os_cutsKnown (m := 6) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_6 osOk_338

end
end LeanVM.Guest.End
