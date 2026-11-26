/-
  LeanVM.Guest.B1.Place.OsKidsP

  The callees of a straight-line body placed in sequence, per level a group of calls whose layout
  depends on where the group is placed (f128's `open_stacked`: the first squeeze's decoder and the
  squeeze loop).
-/

module

public import LeanVM.Guest.B1.Place.OsKidsB

/-!
# Callees in sequence, per level a placed group

`OsLvKP`: a level's frames, the calls before the group, the group, the calls after it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- A level's frames: the calls before the group, the group, the calls after it. -/
structure OsLvKP where
  A : List Call
  P : List Call
  B : List Call

/-- A level's frames in order. -/
def OsLvKP.calls (k : OsLvKP) : List Call := k.A ++ (k.P ++ k.B)

end
end LeanVM.Guest.B1
