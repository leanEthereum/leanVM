/-
  LeanVM.Guest.B1.Bits.GPower

  B1 for `g_power_of_word` at the guest's `coreProgram`: `GPowerP.lean`'s proof, instantiated.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Bits.GPowerP
public import LeanVM.Guest.B1.Common.Find

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

theorem find_g_power_of_word : coreProgram.find? "g_power_of_word" = some fn% «g_power_of_word» :=
  coreProgram_find?_at (j := idx% «g_power_of_word») rfl

instance finds_g_power_of_word : Finds coreProgram "g_power_of_word" Fn.«g_power_of_word».core := ⟨find_g_power_of_word⟩

/-- **`g_power_of_word`'s core IR is its meaning.** -/
theorem g_power_of_word_holds : g_power_of_word_Spec := g_power_of_word_holdsP coreProgram

end
end LeanVM.Guest.B1
