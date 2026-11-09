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
theorem walk_324 : CutsKnown 324 :=
  os_cutsKnown (m := 21) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_21 osOk_324

set_option maxRecDepth 100000 in
theorem walk_325 : CutsKnown 325 :=
  os_cutsKnown (m := 22) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_22 osOk_325

set_option maxRecDepth 100000 in
theorem walk_326 : CutsKnown 326 :=
  os_cutsKnown (m := 23) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_23 osOk_326

set_option maxRecDepth 100000 in
theorem walk_327 : CutsKnown 327 :=
  os_cutsKnown (m := 24) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_24 osOk_327

set_option maxRecDepth 100000 in
theorem walk_328 : CutsKnown 328 :=
  os_cutsKnown (m := 25) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_25 osOk_328

set_option maxRecDepth 100000 in
theorem walk_329 : CutsKnown 329 :=
  os_cutsKnown (m := 26) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_26 osOk_329

set_option maxRecDepth 100000 in
theorem walk_330 : CutsKnown 330 :=
  os_cutsKnown (m := 27) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_27 osOk_330

end
end LeanVM.Guest.End
