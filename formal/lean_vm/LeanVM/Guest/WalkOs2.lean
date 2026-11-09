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
theorem walk_317 : CutsKnown 317 :=
  os_cutsKnown (m := 14) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_14 osOk_317

set_option maxRecDepth 100000 in
theorem walk_318 : CutsKnown 318 :=
  os_cutsKnown (m := 15) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_15 osOk_318

set_option maxRecDepth 100000 in
theorem walk_319 : CutsKnown 319 :=
  os_cutsKnown (m := 16) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_16 osOk_319

set_option maxRecDepth 100000 in
theorem walk_320 : CutsKnown 320 :=
  os_cutsKnown (m := 17) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_17 osOk_320

set_option maxRecDepth 100000 in
theorem walk_321 : CutsKnown 321 :=
  os_cutsKnown (m := 18) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_18 osOk_321

set_option maxRecDepth 100000 in
theorem walk_322 : CutsKnown 322 :=
  os_cutsKnown (m := 19) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_19 osOk_322

set_option maxRecDepth 100000 in
theorem walk_323 : CutsKnown 323 :=
  os_cutsKnown (m := 20) (by decide) (os_body (by decide) (by decide) (by decide) (by decide +kernel))
    osLvB_20 osOk_323

end
end LeanVM.Guest.End
