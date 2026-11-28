module

public import Statement.Verifier.Layout
public import Statement.Verifier.Transcript

/-!
# Sumcheck rounds (`transcript.rs`)

A round polynomial of `count` coefficients is sent with one coefficient left out, which the
verifier derives from the running claim: in plain mode (`eq_factor = None`) `q(0) + q(1) = claim`
fixes `c1`; in equality mode (`eq_factor = r`) `(1 + r)·q(0) + r·q(1) = claim` fixes `c0`
(characteristic two). Each round's challenge follows a grind for the degree of the whole round
polynomial, the equality factor included: `grindingBits (count - 1 + [eq])`, zero bits up to
degree `8`. The link's rounds have up to `12` coefficients (`round_coefficients`, `link.rs`): its
row rounds grind one bit at pointer widths `21` to `24`, its pointer-column rounds at `23` and `24`.
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics
open LeanVM.Protocol.Compile

/-- Fail on `none`: a pure step that returns a `Result` in the Rust. -/
def liftOption {α : Type} : Option α → VerifierProgram α
  | none => VerifierProgram.fail
  | some a => VerifierProgram.ret a

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`: read a round polynomial of `count`
coefficients, deriving the one the claim fixes, then grind for its degree; its coefficients,
constant first (`transcript.rs`). -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → VerifierProgram (List E)
  | none => do
    let constant ← VerifierProgram.readScalar
    let tail ← VerifierProgram.readScalars (count - 2)
    VerifierProgram.grindProofOfWork (grindingBits (count - 1))
    return constant :: (claim + sumE tail) :: tail
  | some eqFactor => do
    let tail ← VerifierProgram.readScalars (count - 1)
    VerifierProgram.grindProofOfWork (grindingBits (count - 1 + 1))
    return (claim + eqFactor * sumE tail) :: tail

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry of `equalities`, each
reading its polynomial and sampling its challenge; the challenges in order, and the final claim
(`transcript.rs`). -/
def sumcheck (claim : E) (count : ℕ) : List (Option E) → VerifierProgram (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← VerifierProgram.sampleChallenge
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    return (challenge :: point, final)

end LeanVM.Protocol.Verifier

end
