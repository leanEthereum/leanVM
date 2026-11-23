/-
  LeanVM.Guest.CoreMode.ListLit

  `list_mem% i` and `fa%[h₀, …]`: the proof terms of a list literal's membership and of a fact of each
  of its elements, written once here so that the generated modules state them by position.
-/

module

public meta import Lean.Elab.Term

/-!
# List literals' proof terms

`list_mem% i` is `List.mem_cons_of_mem _ (… (List.mem_cons_self))`, `i` steps: the `i`-th element of a
list literal is among it. `fa%[h₀, …, hₙ]` is `Mode.fa_cons h₀ (… (Mode.fa_cons hₙ Mode.fa_nil))`: a
fact of each element of a list literal, element by element. Both expand to the terms the generators
wrote out before, so their elaboration is the same.
-/

public section

/-- `list_mem% i`: the `i`-th element of a list literal is among it. -/
syntax "list_mem% " num : term

macro_rules
  | `(list_mem% $n) => do
    let mut t ← `(List.mem_cons_self)
    for _ in [0:n.getNat] do t ← `(List.mem_cons_of_mem _ $t)
    return t

/-- `fa%[h₀, …, hₙ]`: a fact of each element of a list literal, `hᵢ` the `i`-th's. -/
syntax "fa%[" term,* "]" : term

macro_rules
  | `(fa%[$hs,*]) => do
    -- the names resolved where the term is written (`Mode/CertDefs.lean`'s), not here
    let cons := Lean.mkIdent `LeanVM.Guest.Mode.fa_cons
    let mut t ← `($(Lean.mkIdent `LeanVM.Guest.Mode.fa_nil))
    for h in hs.getElems.reverse do t ← `($cons $h $t)
    return t

end
