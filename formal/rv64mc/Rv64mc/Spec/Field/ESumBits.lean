/-
  Rv64mc.Spec.Field.ESumBits

  The contract of `E::sum` over `(lo..hi).filter(|b| e >> b & 1 == 1).map(|b| powers[b])`, the sum
  `instance_weights` takes per entry of `RMFE_EMBED` (`keccak.rs`): the iterator at `a0`, a `Map<Filter<Range<usize>,
  _>, _>` whose closures capture `&e` (a `u32`) and `&powers` (an `[E; 24]`). Its layout is not among the generated
  ones (closure captures are not printed): the filter's capture at `0`, the range's `start` and `end` at `8` and `16`,
  the map's capture at `24`, as the compiled callee reads them. The sum's limbs, `Model.sumRust`'s, in `a0`, `a1`;
  an index past `24` panics, so the contract asks `hi ≤ 24`. A leaf without a frame.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.KeccakGkr

namespace Rv64mc.Spec.Field.ESumBits

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- The sum over the bits `b ∈ [lo, hi)` set in `e` of `xs[b]`. -/
def sumBits (e : BitVec 32) (xs : List E) (lo hi : Nat) : E :=
  Model.sumRust (((List.range' lo (hi - lo)).filter fun b => Model.bit32 e b).map fun b => xs.getD b 0)

def Pre (e : BitVec 32) (xs : List E) (lo hi : Nat) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x10).toNat + 32 < 2 ^ 64 ∧ m.getWord32 (m.getMem (regs .x10)) = e ∧
    m.getMem (regs .x10 + 8#64) = BitVec.ofNat 64 lo ∧ m.getMem (regs .x10 + 16#64) = BitVec.ofNat 64 hi ∧
    lo ≤ hi ∧ hi ≤ 24 ∧ xs.length = 24 ∧ EListAt m (m.getMem (regs .x10 + 24#64)) (xs.map Model.limbs)

def Post (e : BitVec 32) (xs : List E) (lo hi : Nat) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word)
    (_m' : MachineState) : Prop :=
  r' .x10 = (Model.limbs (sumBits e xs lo hi)).1 ∧ r' .x11 = (Model.limbs (sumBits e xs lo hi)).2

/-- **The contract of the bit-filtered sum**, function `i` of `p` with `need` bytes of stack (it has no frame; it
    calls only `panic_bounds_check`, past index `24`), for every `u32`, powers and range. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ e xs lo hi, Holds env p i need (Pre e xs lo hi) (Post e xs lo hi)

end Rv64mc.Spec.Field.ESumBits
