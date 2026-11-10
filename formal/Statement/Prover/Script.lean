module

public import Statement.LeanVmVerifier

/-!
# The prover's language

An honest prover written as a program of its own moves, in the order the verifier reads them:
send a scalar, receive a challenge, pass a proof of work, commit a matrix, receive the opened rows.
`Run.lean` runs a script against the verifier's program through the Fiat-Shamir sponge; a script
sees no hash or permutation answer but the challenges and its own matrices' rows.
-/

@[expose] public section

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

/-- A committed matrix: the row at each position; one of `2^height` rows is read at its first
`2^height` positions (`Transcript::merkle`, `crates/verifier/src/transcript.rs:157-186`). -/
abbrev Word : Type := ℕ → List K

end LeanVM.Protocol.Compile

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- An honest prover as a program of its own moves. -/
inductive Script (α : Type) : Type where
  /-- Stop with a value. -/
  | ret (a : α)
  /-- Send the scalar `x`. -/
  | send (x : E) (k : Script α)
  /-- Receive a challenge. -/
  | sample (k : E → Script α)
  /-- Pass a proof of work. -/
  | grind (k : Script α)
  /-- Commit a matrix. -/
  | commit (word : Word) (k : Script α)
  /-- Receive the opened rows. -/
  | query (k : List (List K) → Script α)

namespace Script

variable {α β : Type}

/-- Sequencing. -/
def bind : Script α → (α → Script β) → Script β
  | ret a, f => f a
  | send x k, f => send x (k.bind f)
  | sample k, f => sample fun c ↦ (k c).bind f
  | grind k, f => grind (k.bind f)
  | commit w k, f => commit w (k.bind f)
  | query k, f => query fun r ↦ (k r).bind f

instance : Monad Script where
  pure := ret
  bind := bind

/-- Send one scalar. -/
def sendE (x : E) : Script Unit := send x (ret ())

/-- Send a list of scalars, in order. -/
def sendList : List E → Script Unit
  | [] => ret ()
  | x :: xs => send x (sendList xs)

/-- Receive one challenge. -/
def sampleE : Script E := sample ret

/-- Receive `n` challenges, in order. -/
def sampleN : ℕ → Script (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← sampleE
    let xs ← sampleN n
    return x :: xs

/-- Pass a proof of work. -/
def grindS : Script Unit := grind (ret ())

/-- Pass a proof of work of `bits` bits: nothing at `0` bits, as the verifier's
`grindProofOfWork` and the Rust's `grind` (`crates/fiat_shamir/src/lib.rs:170-176`). -/
def grindBits (bits : ℕ) : Script Unit := if bits = 0 then ret () else grindS

/-- Commit a matrix. -/
def commitS (word : Word) : Script Unit := commit word (ret ())

/-- Receive opened rows. -/
def queryS : Script (List (List K)) := query ret

/-- **The script `S` beside the verifier's program `P`**: `S`'s moves, ending in `P`'s result,
which `P` computes from them; `default` where they are not `P`'s, which an honest script never
meets. A phase's prover hands the next phase the verifier's own values (claims, points). -/
def alongside {α : Type} [Inhabited α] : VerifierProgram α → Script β → Script α
  | .ret a, _ => ret a
  | .read k, send x S => send x (alongside (k x) S)
  | .sample k, sample S => sample fun c ↦ alongside (k c) (S c)
  | .grind _ k, grind S => grind (alongside k S)
  | .commit _ _ k, commit w S => commit w (alongside k S)
  | .query _ _ k, query S => query fun rows ↦ alongside (k rows) (S rows)
  | _, _ => ret default

end Script

/-! ## A sumcheck prover -/

/-- The coefficients the wire carries, as the verifier's `sumcheckRoundPoly` rebuilds them: all but
the linear one in plain mode (`none`), all but the constant one in equality mode (`some r`). -/
def wire : Option E → List E → List E
  | none, c => c.headD 0 :: c.drop 2
  | some _, c => c.drop 1

/-- The grind after a round polynomial of these coefficients in the round's mode, for its degree,
the equality factor included (`add_round_poly`, `crates/fiat_shamir/src/transcript.rs:93-104`). -/
def roundGrind (mode : Option E) (c : List E) : ℕ :=
  grindingBits (c.length - 1 + if mode.isSome then 1 else 0)

/-- **A stateful sumcheck prover**: per round the coefficients `round st` (constant first) on the
wire in the round's mode and the grind for their degree, then the challenge `c`, the state
becoming `fold st c`; the challenges in order, and the last state. -/
def sumcheckBy {σ : Type} (round : σ → List E) (fold : σ → E → σ) :
    List (Option E) → σ → Script (List E × σ)
  | [], st => .ret ([], st)
  | mode :: modes, st =>
    (Script.sendList (wire mode (round st))).bind fun _ ↦
    (Script.grindBits (roundGrind mode (round st))).bind fun _ ↦ Script.sampleE.bind fun c ↦
      (sumcheckBy round fold modes (fold st c)).bind fun r ↦ .ret (c :: r.1, r.2)

end LeanVM.Prover

end
