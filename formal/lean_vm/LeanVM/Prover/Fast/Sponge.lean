import Statement.Verifier.Lib

/-!
# The sponge's permutation input, compiled once per permutation

`duplexInput` reads each of the sixteen rate lanes from the list of the waiting scalars' lanes,
rebuilt for each; `duplexInput.fast` builds it once, as an array. `packedInput.fast` does the same
for a packed chunk's lanes.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics

/-- `duplexInput`, the waiting scalars' lanes built once. -/
def duplexInput.fast (sp : Sponge) : KeccakState :=
  let lanes := (pendingLanes sp.pending).toArray
  Vector.ofFn fun i ↦ if i.val < 16 then lanes.getD i 0 else Keccak.lane sp.state i

/-- **`duplexInput` compiles with the lanes built once.** -/
@[csimp] theorem duplexInput.fast_eq : @duplexInput = @duplexInput.fast := by
  funext sp
  simp [duplexInput, duplexInput.fast, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- `packedInput`, the chunk's lanes built once. -/
def packedInput.fast (state : KeccakState) (chunk : List E) : KeccakState :=
  let lanes := (chunk.flatMap fun x ↦ [(x.limb 0).lane, (x.limb 1).lane]).toArray
  Vector.ofFn fun i ↦ if i.val < 16 then lanes.getD i 0 else Keccak.lane state i

/-- **`packedInput` compiles with the lanes built once.** -/
@[csimp] theorem packedInput.fast_eq : @packedInput = @packedInput.fast := by
  funext state chunk
  simp [packedInput, packedInput.fast, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

end LeanVM.Protocol.Compile
