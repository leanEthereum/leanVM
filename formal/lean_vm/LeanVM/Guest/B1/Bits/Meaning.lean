/-
  LeanVM.Guest.B1.Bits.Meaning

  The statements that the guest's bit, log and exponent functions compute their meanings
  (`MeaningP.lean`), at `coreProgram`.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Bits.MeaningP

/-!
# Bits, logs and the exponent, at the guest

`…_Spec` is `MeaningP.lean`'s `…_SpecP` at `coreProgram`; its proof is the theorem
`…_holds : …_Spec` of the family's modules.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- `exponent_tables`' core IR is its meaning. -/
def exponent_tables_Spec : Prop := exponent_tables_SpecP coreProgram

/-- `g_power_of_word`'s core IR is its meaning. -/
def g_power_of_word_Spec : Prop := g_power_of_word_SpecP coreProgram

/-- `assert_small_g_power`'s core IR is its meaning. -/
def assert_small_g_power_Spec : Prop := assert_small_g_power_SpecP coreProgram

/-- `log2_ceil_in_the_exponent__L{fl}_L34`'s core IR is its meaning. -/
def log2_ceil_in_the_exponent_Spec (name : String) (fl : ℕ) : Prop :=
  log2_ceil_in_the_exponent_SpecP coreProgram name fl

/-- The deployed `log2_ceil_in_the_exponent` specializations are their meanings. -/
def log2_Spec : Prop := log2_SpecP coreProgram

/-- `grind_check__L{bits}`'s core IR is its meaning. -/
def grind_check_Spec (bits : ℕ) : Prop := grind_check_SpecP coreProgram bits

/-- Every deployed `grind_check` is its meaning. -/
def grind_check_all_Spec : Prop := grind_check_all_SpecP coreProgram

end
end LeanVM.Guest.B1
