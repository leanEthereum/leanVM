module

public import NativeVm.Model.Stack

/-!
# Phase 3a: the bus's GKR walk

Models `gkrStep`, `gkrLayers` and `verifyGkrGrandProducts` (`Statement/LeanVmVerifier.lean`,
`bus.rs`).

`verifyGkrGrandProducts depth` **reads** the shared and count roots, then walks the push, pull and
count trees `depth` layers down, one first when `depth` is odd, two at a time otherwise; each step
grinds, samples its combiner, runs an equality-mode sumcheck over the point so far, reads each
tree's `2^step` children and checks their products, grinds and samples `step` coordinates.
**Returns** `(countRoot, point, values)`: the count root, the GKR point (`depth` coordinates) and the
three trees' values there.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- The walk's state (`GkrState`): the three trees' values, at `point`. -/
structure GkrStateW where
  values : Array EW
  point : Array EW
  deriving Inhabited

/-- `gkrStep step last state`. -/
def gkrStep (step : Nat) (last : Bool) (state : GkrStateW) : VM GkrStateW := do
  grind (grindingBits (nTrees - 1))
  let combiner ← sampleChallenge
  let claim := polyEval state.values combiner
  let (x, claim) ← sumcheck claim (2 ^ step + 1) (state.point.map some)
  let child0 ← readScalars (2 ^ step)
  let child1 ← readScalars (2 ^ step)
  let child2 ← readScalars (2 ^ step)
  let children := #[child0, child1, child2]
  let products := children.map prodE
  require (claim == polyEval products combiner)
  grind (grindingBits (if last then 2 * step else step))
  let y ← sampleChallenges step
  let values := children.map (multilinearEval · y)
  pure ⟨values, y ++ x⟩

/-- `gkrLayers`: one level when the remaining depth is odd, two otherwise. -/
def gkrLayers : Nat → GkrStateW → VM GkrStateW
  | 0, s => pure s
  | 1, s => do
    let s ← gkrStep 1 true s
    gkrLayers 0 s
  | n + 2, s =>
    if n % 2 = 1 then do
      let s ← gkrStep 1 false s
      gkrLayers (n + 1) s
    else do
      let s ← gkrStep 2 (n = 0) s
      gkrLayers n s

/-- **`verifyGkrGrandProducts depth`**: the count root, the GKR point, the trees' values. -/
def verifyGkrGrandProducts (depth : Nat) : VM (EW × Array EW × Array EW) := do
  let shared ← readScalar
  let count ← readScalar
  let s ← gkrLayers depth ⟨#[shared, shared, count], #[]⟩
  pure (count, s.point, s.values)

end NativeVm.Model
