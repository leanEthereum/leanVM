/-
  LeanVM.Guest.WalkWp

  The cut obligations (`CutsKnown`) of `walk_path`'s specializations (`wp_cutsKnown`,
  `WalkWpOk.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkWpOk

namespace LeanVM.Guest.End

@[expose] public section

/-- `walk_path__L12_L3`. -/
theorem walk_1439 : CutsKnown 1439 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1439

/-- `walk_path__L12_L5`. -/
theorem walk_1442 : CutsKnown 1442 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1442

/-- `walk_path__L12_L4`. -/
theorem walk_1459 : CutsKnown 1459 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1459

/-- `walk_path__L12_L6`. -/
theorem walk_1462 : CutsKnown 1462 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1462

/-- `walk_path__L12_L7`. -/
theorem walk_1471 : CutsKnown 1471 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1471

/-- `walk_path__L18_L2`. -/
theorem walk_1480 : CutsKnown 1480 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1480

/-- `walk_path__L18_L3`. -/
theorem walk_1489 : CutsKnown 1489 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1489

/-- `walk_path__L18_L4`. -/
theorem walk_1497 : CutsKnown 1497 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1497

/-- `walk_path__L18_L5`. -/
theorem walk_1503 : CutsKnown 1503 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1503

/-- `walk_path__L18_L6`. -/
theorem walk_1509 : CutsKnown 1509 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1509

/-- `walk_path__L18_L7`. -/
theorem walk_1515 : CutsKnown 1515 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1515

/-- `walk_path__L24_L2`. -/
theorem walk_1521 : CutsKnown 1521 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1521

/-- `walk_path__L24_L3`. -/
theorem walk_1523 : CutsKnown 1523 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1523

/-- `walk_path__L24_L4`. -/
theorem walk_1528 : CutsKnown 1528 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1528

/-- `walk_path__L12_L2`. -/
theorem walk_1532 : CutsKnown 1532 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1532

/-- `walk_path__L6_L7`. -/
theorem walk_1533 : CutsKnown 1533 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1533

/-- `walk_path__L6_L6`. -/
theorem walk_1534 : CutsKnown 1534 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1534

/-- `walk_path__L12_L8`. -/
theorem walk_1535 : CutsKnown 1535 :=
  wp_cutsKnown (by decide) (by decide) walkOk_1535

end
end LeanVM.Guest.End
