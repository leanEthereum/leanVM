/-
  LeanVM.Guest.B1.Fs.TailRound

  B1 for `opening_tail_round` at the guest's `coreProgram`: `TailRoundP.lean` instantiated.
-/

module

public import LeanVM.Guest.B1.Fs.TailRoundP
public import LeanVM.Guest.B1.Common.Find

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- `opening_tail_round`'s core IR is its meaning. -/
abbrev opening_tail_round_Spec : Prop := opening_tail_round_SpecP coreProgram

theorem find_opening_tail_round : coreProgram.find? "opening_tail_round" = some
    fn% «opening_tail_round» :=
  coreProgram_find?_at (j := idx% «opening_tail_round») rfl

instance finds_opening_tail_round : Finds coreProgram "opening_tail_round" Fn.«opening_tail_round».core :=
  ⟨find_opening_tail_round⟩

/-- **`opening_tail_round`'s core IR is its meaning.** -/
theorem opening_tail_round_holds : opening_tail_round_Spec := opening_tail_round_holdsP coreProgram

end
end LeanVM.Guest.B1
