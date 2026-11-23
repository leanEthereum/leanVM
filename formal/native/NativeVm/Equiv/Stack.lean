module

public import NativeVm.Equiv.LayoutSpec
public import NativeVm.Equiv.Transcript
public import NativeVm.Model.Stack

/-!
# Phase 2: the stack's commitment and its out-of-domain sample

`Sim.commitStack`: the same ladder (`Whir.ladder`, the statement's), the same root shape
(`levelShape` is the statement's word for word), one commitment read. `Sim.readOod`: a grind, the
challenges, a scalar; the claim is the statement's (`StackClaimW.Rel`), its weight `eq z`
evaluating as `eqEval z` (`toE_eqEval`).
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- **`commitStack`**: the stack's root, read at level `0`'s shape. -/
theorem Sim.commitStack (logN logInvRate : ℕ) :
    Sim (Model.commitStack logN logInvRate) (Verifier.commitStack logN logInvRate)
      (fun _ _ ↦ True) := by
  unfold Model.commitStack Verifier.commitStack
  refine Sim.bind (Sim.liftOpt (R := Eq) ?_) fun c c' h ↦ ?_
  · rcases Whir.ladder logN logInvRate with _ | c
    · exact .none
    · exact .some rfl
  subst h
  rcases c with _ | ⟨level, _⟩
  · exact Sim.reject
  · exact Sim.readCommitment _ _

/-- **`readOod`**: the stack's out-of-domain claim, its weight `eqEval z`. -/
theorem Sim.readOod (stackLog : ℕ) :
    Sim (Model.readOod stackLog) (Verifier.readOod stackLog) StackClaimW.Rel := by
  unfold Model.readOod Verifier.readOod
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind (Sim.sampleChallenges _) fun z z' ⟨hz, _⟩ ↦ ?_
  refine Sim.bind Sim.readScalar fun v v' hv ↦ Sim.pure ⟨fun x ↦ ?_, hv⟩
  rw [← hz]
  exact toE_eqEval z x

end NativeVm.Equiv
