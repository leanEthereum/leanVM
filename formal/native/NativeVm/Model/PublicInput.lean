module

public import NativeVm.Model.Tables

/-!
# Phase 5: the public input

Models `publicInputPhase` (`Statement/LeanVmVerifier.lean`, `lib.rs`).

**Takes** the layout and the public input's four words `w`. **Samples** one challenge `c`, with no
grind; reads nothing. **Returns** the two memory columns' claims at `(c, 0, …, 0)` (the memory's
log-size coordinates): limb `l`'s value is the line through `w[l]` and `w[2 + l]` at `c`,
`multilinearEval [w[l], w[2 + l]] [c]` (`digestHalves`: the halves are `E(w0, w1)`, `E(w2, w3)`).
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- **Phase 5** (`publicInputPhase`). -/
def publicInputPhase (layout : LayoutW) (publicInput : Vector UInt64 4) :
    VM (Array ColumnClaimW) := do
  let publicChallenge ← sampleChallenge
  let publicLimbs := #[0, 1].map fun limb ↦
    multilinearEval #[EW.ofK publicInput[limb]!, EW.ofK publicInput[2 + limb]!] #[publicChallenge]
  let publicPoint := #[publicChallenge] ++
    Array.replicate ((layout.placement memory0).variableCount - 1) 0
  pure #[⟨memory0, publicPoint, publicLimbs.getD 0 0⟩, ⟨memory1, publicPoint, publicLimbs.getD 1 0⟩]

end NativeVm.Model
