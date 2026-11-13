/-
  LeanVM.Guest.B1.Bits.MeaningP

  The meanings of B1's bit functions stated for any program: what each computes, and that a
  program's relation at the function's name is it. No guest data.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# Bits: meanings for any program

`…_SpecP P`: program `P`'s relation at the function's name is its meaning. The proof of
`…_SpecP P` (`…_holdsP`) holds for every `P` that finds the function (`Finds`) and imports that
function's core module only; `Meaning.lean` states `…_Spec` at `coreProgram`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `g_power_of_word` (lean_ethereum.py:748-761) -/

/-- **`g_power_of_word(value)`**: the value is the integer `n < 2^6` (`E(n)`), and the function
returns `g^n`. -/
def MeaningGPowerOfWord : List E → List E → Prop
  | [v], rets => ∃ n < 2 ^ 6, v = eOfNat n ∧ rets = [gen ^ n]
  | _, _ => False

/-- `P`'s relation at `g_power_of_word` is its meaning. -/
def g_power_of_word_SpecP (P : Program) : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    P.Rel rd "g_power_of_word" args rets ↔ MeaningGPowerOfWord args rets

end
end LeanVM.Guest.B1
