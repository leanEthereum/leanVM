/-
  LeanVM.Guest.B1.Main.CompleteE

  Callees all of whose valid trees satisfy a predicate of the memory, such as one exact for free (`exactFree`).
-/

module

public import LeanVM.Guest.B1.Main.CompleteP
public import LeanVM.Guest.B1.Main.RelAtInE
public import LeanVM.Guest.Exact.Free

/-!
# Callees whose every valid tree satisfies `Q`

`EveryOn k f Lin args Q`: every valid tree of `f` at `args` satisfies `Tree.Every (Q rd)` on every memory `rd` holding
the caller's words. `Q` is a predicate of the memory, as exactness is (a heap destination's words are read through it).
`everyOn_exact`: a function passing `exactFree` is exact on every memory.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : Layout} {args : List E}
  {Out : List E → Layout → Prop} {ps : Reader → List Pop} {Q : Reader → String → Val → Prop}

/-- **Every valid tree of `f` at `args` satisfies `Every (Q rd)`**, on every memory `rd` of the caller's words. -/
def EveryOn (k : ℕ) (f : String) (Lin : Layout) (args : List E) (Q : Reader → String → Val → Prop) : Prop :=
  ∀ rd, LowDef k rd → MemL rd Lin → ∀ (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
    t.Every (Q rd)

/-- **A function passing `exactFree` is exact**, on every memory. -/
theorem everyOn_exact (hg : ExactFreeG f) : EveryOn k f Lin args fun rd => ExactAt coreProgram rd :=
  fun rd _ _ _ _ hn hv => every_exact_of_free hg hv hn rd

end
end LeanVM.Guest.B1
