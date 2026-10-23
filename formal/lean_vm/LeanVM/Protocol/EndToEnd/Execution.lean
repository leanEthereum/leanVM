/-
  LeanVM.Protocol.EndToEnd.Execution

  From a stack satisfying the leanISA instance's relation to a valid execution: the adaptor's
  soundness composed with leanISA's constraint soundness.
-/

module

public import LeanVM.Protocol.LeanIsa.Sound
public import LeanVM.Arithmetization.Soundness.Theorem

/-!
# The extracted stack has an execution

`execution_of_extracted`: a stack `q` satisfying `M3Holds` of the
leanISA instance at admissible sizes, for well-formed bytecode, carries a witness
(`witnessOf`, the adaptor's read-back) that represents a valid execution of the program on the
input. It composes `satisfiedBy_witnessOf` (the adaptor's soundness) with `constraintSoundness`
(`Arithmetization.Soundness.Theorem`). Nothing is transcribed. The witness is kept, as recursion
needs it.
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.LeanIsa

@[expose] public section

/-- **The extracted stack has an execution.** On admissible sizes and well-formed bytecode, a
stack satisfying the leanISA instance's relation reads back to a witness that represents a valid
execution of the program on the input. -/
theorem execution_of_extracted (F : FlockSpec) {prog : Program} {input : PublicInput}
    {s : Sizes} {q : Column (leanIsaμ prog s)} (hsafe : SentinelSafe prog)
    (hs : s.Admissible prog) (h : M3Holds (leanIsaInstance F prog s) input q) :
    ∃ t, AssignmentRepresents (witnessOf F prog s q) t ∧ ValidExecution prog input t :=
  constraintSoundness hsafe (satisfiedBy_witnessOf F prog s q hs h)

end
end LeanVM.Protocol.EndToEnd
