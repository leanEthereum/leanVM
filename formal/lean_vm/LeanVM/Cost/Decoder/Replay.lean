module

public import LeanVM.Cost.Decoder.Memory
public import LeanVM.Guest.Located.ReplayFast
public import LeanVM.Protocol.Extraction.Fast.RunVec
import all Statement.LeanIsa

/-!
# The guest decoder's compiled chain: the replay of the run

The decoder finds each callee's frame by replaying the run from `(g^0, 1)` over its fuel
(`Located.statesTable memT codeT guest L replayFuel ⟨g^0, 1⟩`, `Guest/Fast/Decode.lean`'s
`decode_eq_numbered`). Compiled here on the memory as a vector (`mem`, the image `L = mem.get`):

* `statesVec memT codeT prog mem fin`: `statesTable`, each step the extractor's compiled step
  `Extraction.Fast.stepVec` (the halting loop's, `Cost/Extractor/Runner.lean`: not compiled
  again, the compiler finds it by its head), the final registers `fin` an argument, computed once;
  recursive on the fuel (measure: the fuel);
* `replayStatesOf memT codeT prog mem`: the replay of the run from `(g^0, 1)` over `replayFuel`,
  the final registers `Registers.final prog` computed once.
  The fuel `replayFuel` (`2^128`) is compiled under a name of its own (`replayFuelC`), which the
  bounds name.

`Equations.lean`: `replayStatesOf_eq : replayStatesOf memT codeT prog mem =
statesTable memT codeT prog mem.get replayFuel ⟨gpow 0, 1⟩`.

**The price.** The step is priced per VM step (`Bounds/Step.lean`'s `stepVec_cost`: at most
`411697 + 42·log₂|codeT| + 1092·log₂|memT|`, ≈ `2^18.77` at `|memT| = |codeT| = 2^32`). The
replay stops at the final state (or a failed step) long before its fuel (`2^128`) on a halting
run of `T` steps (`Located.steps_lt_replayFuel`), so its price is `T + 1` rounds of `statesVec`'s
own work (a comparison with `fin`, a cons, a `match`) plus `T` steps, `Registers.final` once:
`replayStatesOf`'s price ≈ `c₀ + (T + 1)·c₁ + Σ_{i<T} price(stepVec rᵢ) ≤ c₀ + (T + 1)·(c₁ +
stepPrice)`, `c₀`, `c₁` small constants of the compiled bodies (`statesVecC.costEq`,
`replayStatesOfC.costEq`). **This is the decoder's big runtime term: steps × step price.**
Proved in `Bounds/GuestReplay.lean`: `c₁ = 48`, and on the address tables `powTable κ`,
`powTable ℓ` (`replayStatesOf_cost`) at most `(runnerStepPrice κ ℓ + 48)·|states| + 18000`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction.Fast LeanVM.Guest.Located

@[expose] public section

/-- **The states of the run from `r`, on the memory vector** (`Located.statesTable` at
`mem.get`): `r`, then, unless `r` is `fin`, the states from its step (the extractor's
`stepVec`), for `fuel` steps at most. Each round costs a comparison with `fin` and one
`stepVec`: the replay's price is its number of steps times the step's price. -/
def statesVec (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ} (mem : Vector E (2 ^ κ))
    (fin : Registers K) : ℕ → Registers K → List (Registers K)
  | 0, r => [r]
  | n + 1, r => r :: if r = fin then [] else
      match stepVec memT codeT prog mem r with
      | some r' => statesVec memT codeT prog mem fin n r'
      | none => []

/-- **The replay of the run from `(g^0, 1)` over its fuel**, on the memory vector, the final
registers computed once. Its price is the run's steps times the step's price (the module's
docstring). -/
def replayStatesOf (memT codeT : Array (ℕ × ℕ)) (prog : LeanIsaProgram) {κ : ℕ}
    (mem : Vector E (2 ^ κ)) : List (Registers K) :=
  statesVec memT codeT prog mem (Registers.final prog) replayFuel ⟨addressOfIndex 0, 1⟩

-- the fuel, under a name of its own (its name then does not depend on the program's indices)
cost_compile replayFuelC := replayFuel
cost_compile statesVecC measure fun _ _ _ _ _ _ n _ ↦ n := statesVec
cost_compile replayStatesOfC := replayStatesOf

end

end LeanVM.Cost.Decoder
