module

public import NativeVm.Model.Claims

/-!
# Phase 2: the stack's commitment and its out-of-domain sample

Models `commitStack` and `readOod` (`Statement/Verifier/Whir.lean`, `lib.rs`).

* `commitStack stackLog logInverseRate`: **reads** the stack's root (commitment `0`), its shape the
  one level `0` of the ladder (`Whir.ladder`, the statement's parameter table) opens it at;
  **returns** nothing, the root in the transcript's `roots`.
* `readOod stackLog`: a grind, `stackLog` challenges `z`, one scalar; **returns** the stack claim
  `⟨.eq z, value⟩`, the last of the stacked opening's claims.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `levelShape`: `2^(μ − fold + rate)` leaves of `width` words. -/
def levelShape (messageLogBefore : Nat) (level : Whir.Level) (width : Nat) : Nat × Nat :=
  (messageLogBefore - level.fold + level.logInvRate, width)

/-- **`commitStack`**: the stack's root, read at level `0`'s shape. -/
def commitStack (logN logInvRate : Nat) : VM Unit := do
  let config ← liftOpt (Whir.ladder logN logInvRate)
  match config with
  | [] => reject
  | level :: _ =>
    let (height, width) := levelShape logN level (2 ^ level.fold)
    readCommitment height width

/-- **`readOod`**: the stack commitment's out-of-domain claim. -/
def readOod (stackLog : Nat) : VM StackClaimW := do
  grind Whir.oodGrindingBits
  let z ← sampleChallenges stackLog
  let value ← readScalar
  pure ⟨.eq z, value⟩

end NativeVm.Model
