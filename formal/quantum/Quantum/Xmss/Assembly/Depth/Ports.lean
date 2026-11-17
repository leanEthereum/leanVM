module

public import Quantum.Xmss.Assembly.Template

@[expose] public section

/-!
# The rounds of the depth-limited XMSS chain

The parallel programs of the depth-limited chain call the template runtimes' ports single or in
rounds of one sponge port (`portR`).
-/

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge

variable (X Z : Type) [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] (S M' : Type)
  [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M']

/-- The rounds of the parallel programs: rounds of a sponge port. -/
abbrev portR : SpongePort → (recHwSpec X Z S M').Port := fun p ↦ .inl (.inl (.inl p))

end Quantum.Xmss.Assembly

end
