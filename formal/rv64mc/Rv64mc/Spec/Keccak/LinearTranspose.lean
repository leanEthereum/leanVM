/-
  Rv64mc.Spec.Keccak.LinearTranspose

  The contract of `verifier::keccak::linear_transpose::<E>(w: &[E]) -> Vec<E>`: the result's slot (`sret`) in `a0`,
  the slice `w` as a pointer and a length in `a1`, `a2`, its elements' limbs in the heap (`EListAt`, `Live`). Where
  `Model.linearTransposeRust` has a value (`w` has `1600` elements; otherwise `assert_eq!` does not return), the
  slot holds a `Vec` of its limbs, in a buffer the call allocated. The call writes the slot (`Out`). The stack
  pointer is 8-aligned (the ABI's 16 is more): the column sums are zeroed by `memset`, whose contract is on bytes,
  and read back by doublewords.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.KeccakGkr

namespace Rv64mc.Spec.Keccak.LinearTranspose

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

def Pre (env : Env) (ws : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs EListAt m (regs .x11) (regs .x12) (ws.map Model.limbs) ∧
    env.Live m (regs .x11) (Layouts.E.byteSize * ws.length) ∧
    env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ (regs .x2).toNat % 8 = 0

def Post (env : Env) (ws : List E) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  ∀ v, Model.linearTransposeRust ws = some v → ∃ ptr cap,
    VecAt EListAt m' (regs .x10) ptr cap (v.map Model.limbs) ∧ env.Fresh m m' ptr (Layouts.E.byteSize * cap)

/-- What it writes besides its stack and allocations: the result's slot. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Vec.byteSize b

/-- **The contract of `linear_transpose::<E>`**, function `i` of `p` with `need` bytes of stack (its frame is
    `30816` bytes; it calls `memset`, `alloc`, `Vec::<E>::reserve` and three that do not return), for every slice. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ws, Holds env p i need (Pre env ws) (Post env ws) Out

end Rv64mc.Spec.Keccak.LinearTranspose
