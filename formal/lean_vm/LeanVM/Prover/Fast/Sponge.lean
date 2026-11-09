import Statement.LeanVmVerifier

/-!
# The sponge's permutation input, compiled once per permutation

`duplexInput` reads each of the sixteen rate lanes from the list of the waiting scalars' lanes,
rebuilt for each; `duplexInput.fast` builds it once, as an array.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Semantics

/-- `duplexInput`, the waiting scalars' lanes built once. -/
def duplexInput.fast (sp : Sponge) : KeccakState :=
  let lanes := (pendingLanes sp.pending).toArray
  Vector.ofFn fun i ↦ if i.val < 16 then lanes.getD i 0 else Keccak.lane sp.state i

/-- **`duplexInput` compiles with the lanes built once.** -/
@[csimp] theorem duplexInput.fast_eq : @duplexInput = @duplexInput.fast := by
  funext sp
  simp [duplexInput, duplexInput.fast, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

end LeanVM.Protocol.Compile
