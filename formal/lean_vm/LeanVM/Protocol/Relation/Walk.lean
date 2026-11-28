/-
  LeanVM.Protocol.Relation.Walk

  The walk's normal form: `verify_execution` as the announced sizes, then a body whose ghost form
  returns the stacked opening's trace.
-/

module

public import LeanVM.Protocol.Relation.Front
public import LeanVM.Protocol.Whir.Sound.Spec

/-!
# The walk's normal form

`verifyExecution computedSplit` (`walk`, `lib.rs`) is the announced sizes, then the body `veBody`:
the stack's commitment and its out-of-domain sample, the front phases (`frontProg`), the placement
of `q_keccak`, ring switching, the memory term and the stacked opening (`verifyExecution_eq`).
`veBodyG` is the body returning the stacked opening's trace (`Whir.Sound.verifyStackedOpeningG`),
the trace dropped the body (`veBodyG_unit`): the ghost program the certificate is stated on.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-- The claims the stacked opening reads, after the ring claim: the memory term, every placed
column claim of the front phases, the out-of-domain claim. -/
def openOthers (layout : Layout) (memoryTerm : StackClaim) (link : LinkEnd)
    (pub outs : List ColumnClaim) (ood : StackClaim) : List StackClaim :=
  memoryTerm :: (linkColumnClaims link ++ pub ++ outs).filterMap (·.onStack layout) ++ [ood]

/-- `verify_execution` after the announced sizes, returning the stacked opening's trace. -/
def veBodyG (layout : Layout) (ρ : ℕ) (input : PublicInput) :
    VerifierProgram Whir.Sound.WhirTrace := do
  commitStack layout.stackLog ρ
  let ood ← readOod layout.stackLog
  let (link, pub, outs, keccakPoint, keccakSlices) ← frontProg layout input
  let qk ← liftOption (layout.placements.getD qkeccak none)
  let (ring, batching) ← ringSwitch [keccakRingClaim qk keccakPoint keccakSlices, link.ring]
  let memoryTerm ← memoryTermClaim layout link
  Whir.Sound.verifyStackedOpeningG layout.stackLog ρ
    (ring :: openOthers layout memoryTerm link pub outs ood) batching

/-- **The walk's normal form**: the announced sizes, then the ghost body, its trace dropped. -/
theorem verifyExecution_eq (bytecode : List K) (input : PublicInput) :
    verifyExecution computedSplit bytecode (publicInputDigest input) =
      (readAnnouncedSizes bytecode).bind fun a ↦
        (veBodyG a.1 a.2 input).bind fun _ ↦ VerifierProgram.ret () := by
  simp only [verifyExecution, veBodyG, frontProg, openOthers, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc, Whir.Sound.verifyStackedOpeningG_unit, VerifierProgram.ret_bind,
    VerifierProgram.pure_eq, List.cons_append, List.append_assoc]

end

end LeanVM.Protocol.Relation
