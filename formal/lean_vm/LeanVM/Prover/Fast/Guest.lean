import LeanVM.Prover.Fast.Prover
import Statement.LeanVmGuestProver

/-!
# The guest's prover, compiled with the fast prover

`LeanVM.Guest.guestProve` (`Statement/LeanVmGuestProver.lean`) copied word for word, so that its call of
`prove` compiles as `prove.fast` (`Fast/Prover.lean`), and `@[csimp]` by `rfl`: `guest-run --prove`
calls `guestProve` and runs this.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Node LeanVM.Prover

/-- `guestProve`, copied. -/
def guestProve.fast {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (guest : LeanIsaProgram) (s : NodeStatement) (w : NodeWitness) (ρ fuel : ℕ) :
    m (Option Proof) :=
  match guestExecution guest s w with
  | .ok t => prove π guest (PublicInput.ofDigest (statementDigest (deployedSeed guest) s)) t ρ fuel
  | .error _ => pure none

@[csimp] theorem guestProve.fast_eq : @guestProve = @guestProve.fast := rfl

end LeanVM.Guest
