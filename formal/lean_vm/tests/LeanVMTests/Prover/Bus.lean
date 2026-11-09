/-
  LeanVMTests.Prover.Bus

  The executable batched GKR (`Statement/Prover/Gkr.lean`) run against the verifier's own
  program `verifyGkrGrandProducts`, on tiny trees: every `require` passes, and the verifier ends at
  the leaves' extensions at its point. Cheap checks of the array tables against the verifier's
  lists.
-/

import Statement.Prover.Bus
import Statement.Prover.Prove

namespace LeanVMTests.Prover.Bus

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover

/-- Run a verifier program against a prover script, the `i`-th challenge `eOfNat (7·i + 3)`: the
program's result, or `none` when it fails or the two disagree on the move. -/
def play {α β : Type} : ℕ → VerifierProgram α → Script β → ℕ → Option α
  | 0, _, _, _ => none
  | _ + 1, .ret a, _, _ => some a
  | _ + 1, .fail, _, _ => none
  | n + 1, .read k, .send x k', i => play n (k x) k' i
  | n + 1, .sample k, .sample k', i =>
    play n (k (eOfNat (7 * i + 3))) (k' (eOfNat (7 * i + 3))) (i + 1)
  | _ + 1, _, _, _ => none

/-- Leaves from words. -/
def leaves (l : List ℕ) : Array E := (l.map eOfNat).toArray

/-- The GKR on three trees of depth `D` (the second the first reversed), checked by the
verifier. -/
def gkrOk (D : ℕ) (a c : List ℕ) : Bool :=
  let L₀ := leaves a
  let L₁ := leaves a.reverse
  let L₂ := leaves c
  match play 10000 (verifyGkrGrandProducts D)
      (gkrA D (treeLayers D L₀) (treeLayers D L₁) (treeLayers D L₂)) 0 with
  | some (_, point, values) =>
    point.length == D &&
      values == [mleA L₀ point, mleA L₁ point, mleA L₂ point]
  | none => false

#guard gkrOk 1 [3, 5] [7, 9]
#guard gkrOk 2 [3, 5, 6, 11] [7, 9, 2, 4]
#guard gkrOk 3 [3, 5, 6, 11, 13, 17, 19, 23] [7, 9, 2, 4, 8, 10, 12, 14]
#guard gkrOk 4 ((List.range 16).map (· + 2)) ((List.range 16).map (· * 3 + 1))

-- A wrong shared root is caught.
#guard (play 10000 (verifyGkrGrandProducts 2)
    (gkrA 2 (treeLayers 2 (leaves [3, 5, 6, 11])) (treeLayers 2 (leaves [3, 5, 6, 12]))
      (treeLayers 2 (leaves [7, 9, 2, 4]))) 0).isNone

-- The array tables are the verifier's lists.
#guard (eqTable [eOfNat 3, eOfNat 5, eOfNat 9]).toList == eqKernel [eOfNat 3, eOfNat 5, eOfNat 9]
#guard mleA (leaves [3, 5, 6, 11, 13, 17, 19, 23]) [eOfNat 4, eOfNat 6, eOfNat 8] ==
  multilinearEval ([3, 5, 6, 11, 13, 17, 19, 23].map eOfNat) [eOfNat 4, eOfNat 6, eOfNat 8]
#guard (powsA gen 5).toList == (List.range 5).map (LeanVM.Protocol.Verifier.gpow ·)

end LeanVMTests.Prover.Bus
