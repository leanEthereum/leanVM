/-
  LeanVM.Guest.B1.Opening.OodPointHi

  `opening_ood_point` at the dimensions `23 .. 26` of the larger stacks.
-/

module

public import LeanVM.Guest.B1.Opening.OodPoint

/-!
# `opening_ood_point__L23` .. `__L26`

The specializations a stack of `2^29 .. 2^32` cells reads at its first level, as
`OodPoint.lean`'s (`ood_iff` at the core IR's body); `oodPointNamesAll` extends `oodPointNames`
by them and `opening_ood_point_all_holds` gives every entry's meaning.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
theorem ood_L23_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L23" args rets ↔
      MeaningOpeningOodPoint 23 rd args rets :=
  ood_iff 23 (by decide) (Program.find?_of_indexOf? (j := 829) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L24_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L24" args rets ↔
      MeaningOpeningOodPoint 24 rd args rets :=
  ood_iff 24 (by decide) (Program.find?_of_indexOf? (j := 874) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L25_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L25" args rets ↔
      MeaningOpeningOodPoint 25 rd args rets :=
  ood_iff 25 (by decide) (Program.find?_of_indexOf? (j := 923) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem ood_L26_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_ood_point__L26" args rets ↔
      MeaningOpeningOodPoint 26 rd args rets :=
  ood_iff 26 (by decide) (Program.find?_of_indexOf? (j := 971) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- Every deployed `opening_ood_point` specialization, `6 ≤ n ≤ 26`. -/
def oodPointNamesAll : List (String × ℕ) :=
  oodPointNames ++ [("opening_ood_point__L23", 23), ("opening_ood_point__L24", 24),
    ("opening_ood_point__L25", 25), ("opening_ood_point__L26", 26)]

/-- **`opening_ood_point`'s core IR is its meaning**, at every deployed dimension. -/
theorem opening_ood_point_all_holds : ∀ p ∈ oodPointNamesAll, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd p.1 args rets ↔ MeaningOpeningOodPoint p.2 rd args rets := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact opening_ood_point_holds p hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    exacts [ood_L23_iff, ood_L24_iff, ood_L25_iff, ood_L26_iff]

end
end LeanVM.Guest.B1
