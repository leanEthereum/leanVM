/-
  LeanVM.Protocol.ToArkLib.Oracles

  Two oracle-statement families ArkLib's oracle reductions are stated over: none, and exactly
  one. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.OracleInterface

/-!
# The empty and the singleton oracle family

An ArkLib oracle reduction carries a family of oracles the verifier may query, indexed by some
type. `NoOracle` is the family with no oracle (index `Fin 0`); `OneOracle M` is the family with
exactly one oracle, of type `M` (index `Fin 1`). A protocol that commits to one object starts
with the first and continues with the second.
-/

namespace LeanVM.Protocol

@[expose] public section

/-- No oracle: the empty family. -/
abbrev NoOracle : Fin 0 → Type := fun i ↦ i.elim0

/-- Exactly one oracle, of type `M`. -/
abbrev OneOracle (M : Type) : Fin 1 → Type := fun _ ↦ M

/-- All functions out of `Fin 0` are equal, so the empty oracle family has one inhabitant. -/
theorem noOracle_eq (o o' : ∀ i, NoOracle i) : o = o' := funext fun i ↦ i.elim0

end
end LeanVM.Protocol
