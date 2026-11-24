/-
  LeanVM.Protocol.ToArkLib.Typed.Commit

  The question a protocol asks an oracle message at the end, and the relation the component
  before it must reach for the question to pass. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Component
public import LeanVM.Protocol.ToArkLib.Oracles

/-!
# A question to a committed message

A protocol that commits to its witness as an oracle message of type `M` ends by asking the
message one question (`Question`): what to ask on a statement, the check on the answer, and the
statement output when it passes. `Question.rel relOut` is what the component before the question
must reach: the check passes and the output is in `relOut`.
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.Oracle

@[expose] public section

variable (M : Type) [OracleInterface M]

/-- The question asked of the message at the end: what to ask on a statement, the check on the
answer, and the statement output when it passes. -/
structure Question (T U : Type) where
  /-- The question. -/
  query : T → OracleInterface.Query M
  /-- The check on the answer. -/
  check : (t : T) → OracleInterface.Response (query t) → Bool
  /-- The statement output. -/
  out : T → U

variable {M} {T U W : Type}

/-- What the component before the question reaches: the check passes and the output is in
`relOut`. -/
def Question.rel (Q : Question M T U) (relOut : Set ((U × ∀ i, OneOracle M i) × W)) :
    Set ((T × ∀ i, OneOracle M i) × W) :=
  {p | Q.check p.1.1 (OracleInterface.answer (p.1.2 0) (Q.query p.1.1)) = true ∧
    ((Q.out p.1.1, p.1.2), p.2) ∈ relOut}

end
end LeanVM.Protocol.Typed
