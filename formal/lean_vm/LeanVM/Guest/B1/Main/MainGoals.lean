/-
  LeanVM.Guest.B1.Main.MainGoals

  `main`'s honest oracle and words on an honest run, which its callees' placed completeness reads
  (`hLmain`).
-/

module

public import LeanVM.Guest.B1.Main.MainHonest
public import LeanVM.Guest.Data.NameStrings

/-!
# `main`'s callees on an honest run

`hm`, `hLmain`: `main`'s honest oracle and words at `fp` (its buffers `hOwn`, then
`exponent_tables`' table).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtD Returns bufL)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- `main`'s honest oracle at `fp`. -/
abbrev hm : MainIn := (hData seed s w).toIn fs fp

/-- **`main`'s honest words at `fp`**: its buffers, then `exponent_tables`' table. -/
abbrev hLmain : B1.Main.Layout :=
  bufL (fp + fs "main") (mSizes (hData seed s w)) (hOwn seed s w) ++ etL (hData seed s w) fs fp

end
end LeanVM.Guest.B1.Main
