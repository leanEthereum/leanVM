import Statement.Prover.Keccak

/-!
# Tests: the executable Keccak prover against the verifier

A toy `q_keccak` of `2^4` steps (`P = 0`, two packs): pseudo-random inputs (slots `0 .. 24`), the
middle state twelve rounds further (slots `25 .. 49`), zeros above; the output lanes' claims at a
point are the true ones. The verifier's own program `verifyKeccak` is run against the prover's
script with fixed challenges (`drive`): every read meets a scalar sent, every challenge is given
to both, and every check passes. Then the same with a wrong output claim: the verifier rejects.
-/

namespace LeanVMTests.Prover.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Prover.KeccakGkr

/-- The verifier program run against a prover script, the `n`-th challenge `chal n`: the
program's result if every read meets a send, every sample a sample and every grind a grind. -/
def drive {α β : Type} (chal : ℕ → E) : VerifierProgram α → Script β → ℕ → Option α
  | .ret a, _, _ => some a
  | .read k, .send x s, n => drive chal (k x) s n
  | .sample k, .sample s, n => drive chal (k (chal n)) (s (chal n)) (n + 1)
  | .grind _ k, .grind s, n => drive chal k s n
  | _, _, _ => none

/-- A pseudo-random element of `E`. -/
def el (n : ℕ) : E :=
  E.ofLimbs (K.ofBits (n * 2654435761 + 1)) (K.ofBits (n * 40503 + 5))

def chal (n : ℕ) : E := el (1000 + n)

/-- Step `x`'s input state. -/
def input (x : ℕ) : KeccakState :=
  Vector.ofFn fun l : Fin 25 ↦ (x * 6364136223846793005 + l.val * 1442695040888963407 + 3).toUInt64

/-- The column: inputs, the middle state, zeros. -/
def qk : Array K := Array.ofFn (n := 2 ^ 10) fun n ↦
  let x := n.val % 16
  let o := n.val / 16
  if o < 25 then K.ofLane (Keccak.lane (input x) o)
  else if o < 50 then K.ofLane (Keccak.lane (roundsOf 0 12 (input x)) (o - 25)) else 0

def col (n : ℕ) : K := qk.getD n 0

def inst : List E := [el 1, el 2, el 3, el 4]

/-- The output lanes' true claims at `inst`. -/
def output : List E := (List.range 25).map fun l ↦
  sumRange 16 fun x ↦ (eqKernel inst).getD x 0 * ofK (K.ofLane (Keccak.lane (keccakF1600 (input x)) l))

-- The verifier accepts the honest prover's proof.
#guard (drive chal (verifyKeccak 4 inst output) (keccakProve col 0 inst output) 0).isSome

-- The verifier rejects a wrong output claim.
#guard (drive chal (verifyKeccak 4 inst (output.set 3 0)) (keccakProve col 0 inst (output.set 3 0))
  0).isNone

end LeanVMTests.Prover.Keccak
