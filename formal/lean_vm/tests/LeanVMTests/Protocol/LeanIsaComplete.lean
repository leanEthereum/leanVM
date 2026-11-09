import LeanVM.Protocol.LeanIsa.Complete
import LeanVMTests.Arithmetization.Statement

/-!
# Tests: the adaptor, completeness

* **The statements, by type**: a witness satisfying the constraint system has its sizes, stacks
  into a column satisfying `M3Honest` of the leanISA instance (`M3Holds`, and every padding row
  holds its table's padding row, the `KECCAK` output lanes of a padding row being Keccak-f[1600]
  of zero), and is read back off it.
* **The relation is inhabited.** The hand-built witness of the constraint statement's tests
  (`walk_satisfiedBy`) stacks into a column satisfying `M3Honest` of the leanISA instance.
* **The round trip of the relations.** On admissible sizes, the witness read back off the stack of
  a witness satisfying the constraint system satisfies it too: completeness followed by soundness.
* **The instance meets the bus phase's conditions and the degree bound**, at every size.
-/

namespace LeanVMTests.Protocol.LeanIsaComplete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.LeanIsa
open Air.Flat (EnsembleWitness)

/-- A witness satisfying the constraint system has its sizes. -/
example (prog : LeanIsaProgram) (input : PublicInput) (κ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (h : SatisfiedBy prog input w) : ∃ s, Sizes.ofWitness w = some s :=
  sizes_of_satisfiedBy h

/-- The adaptor's completeness. -/
example (prog : LeanIsaProgram) (input : PublicInput) (κ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (s : Sizes) (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    M3Holds (leanIsaInstance prog s) input (stackOf prog s w) :=
  m3Holds_stackOf h hs

/-- With honest padding. -/
example (prog : LeanIsaProgram) (input : PublicInput) (κ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (s : Sizes) (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    M3Honest (leanIsaInstance prog s) input (stackOf prog s w) :=
  m3Honest_stackOf h hs

/-- The round trip: completeness, then soundness on admissible sizes. -/
example (prog : LeanIsaProgram) (input : PublicInput) (κ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (s : Sizes) (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s)
    (hadm : s.Admissible prog) :
    SatisfiedBy prog input (witnessOf prog s (stackOf prog s w)) :=
  satisfiedBy_witnessOf prog s _ hadm (m3Holds_stackOf h hs)

/-- The witness read back has the witness's public input and image. -/
example (prog : LeanIsaProgram) (input : PublicInput) (κ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (s : Sizes) (h : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) :
    (witnessOf prog s (stackOf prog s w)).publicInput = w.publicInput ∧
      imageOf (witnessOf prog s (stackOf prog s w)).data = imageOf w.data :=
  ⟨(witnessOf_stackOf h hs).2.2.2.1, (witnessOf_stackOf h hs).2.2.2.2⟩

/-- The leanISA instance's relation is inhabited: the constraint statement's fixture stacks. -/
example : ∃ s q, M3Honest (leanIsaInstance LeanVMTests.Arithmetization.Statement.walkProg s)
    LeanVMTests.Arithmetization.Statement.mulInput q :=
  let ⟨s, hs⟩ := sizes_of_satisfiedBy LeanVMTests.Arithmetization.Statement.walk_satisfiedBy
  ⟨s, _, m3Honest_stackOf LeanVMTests.Arithmetization.Statement.walk_satisfiedBy hs⟩

/-- The bus phase's conditions and the degree bound, at every size. -/
example (prog : LeanIsaProgram) (s : Sizes) :
    Bus.Conditions (leanIsaInstance prog s) ∧ (leanIsaInstance prog s).d ≤ 2 :=
  ⟨leanIsa_conditions prog s, le_rfl⟩

end LeanVMTests.Protocol.LeanIsaComplete
