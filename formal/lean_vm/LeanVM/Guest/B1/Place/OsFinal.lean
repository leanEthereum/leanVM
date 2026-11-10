/-
  LeanVM.Guest.B1.Place.OsFinal

  f128's `open_stacked` is complete placed at every candidate.
-/

module

public import LeanVM.Guest.B1.Place.OsCandAll
public import LeanVM.Guest.B1.Whir.CHonest

/-!
# `open_stacked`, placed

**`open_stacked_completeAtD`**, **`open_stacked_completeAtB`**: OsSpec's statements, from the
placed lift (`Place/OsCandAll`) and the body's completeness at honest values
(`Whir.osHonestSpec_holds`).
-/

namespace LeanVM.Guest.B1

@[expose] public section

/-- **`open_stacked` is complete placed at every candidate.** -/
theorem open_stacked_completeAtD : open_stacked_completeAtD_Spec :=
  open_stacked_completeAtD_of Whir.osHonestSpec_holds

/-- **`open_stacked` is complete placed at every candidate, within `osBosAt` words.** -/
theorem open_stacked_completeAtB : open_stacked_completeAtB_Spec :=
  open_stacked_completeAtB_of Whir.osHonestSpec_holds

end
end LeanVM.Guest.B1
