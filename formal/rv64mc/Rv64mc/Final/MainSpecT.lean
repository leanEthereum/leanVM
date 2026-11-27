/-
  Rv64mc.Final.MainSpecT

  The total contract of the guest's `main(len)` (`guest/src/main.rs`) that `HaltsSafely`'s end
  theorem takes: called as `MainSpec`'s contract is (`MainPre`: the input words at `inputBase`,
  their number in `a0`, `NEXT` at the heap's start), on an input of fewer than `maxInputWords`
  words, `main` returns `0` (`ACCEPT`) or `1` (`REJECT`), or ends the run at the halting `ECALL`
  with `a0 = 2` (`halt(ABORT)`: malformed input, the allocator out of heap, a panic); every load
  and store it makes lies in a window, and it does not trap or run forever (`HoldsT`). With
  `HoldsT`'s calling convention, stack bound and frame, as `MainSpec` has them, and `HoldsT`'s
  `Windows`: it is asked of every stack top at most the stack window's end (`_start` calls it at
  `stackTop`) and every code map between the windows (the loaded image's). It says nothing of
  which verdict: `MainSpec` keeps that, for a return with `0`.
-/

import Rv64mc.Final.MainSpec
import Rv64mc.Core.HoldsT

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- `main`'s total postcondition: it returns `0` or `1`. -/
def MainPostT (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = 0 ∨ r' .x10 = 1

/-- Where `main` may end the run: at the halting `ECALL`, in an accepting state with a nonempty
    stack, with `a0 = 2`. -/
def MainStopT (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = 2

/-- **`main`'s total contract**, for every input of fewer than `maxInputWords` words: function `i` of `p`, with
    `need` bytes of stack. -/
def MainSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ words : List Word, words.length < maxInputWords →
    HoldsT env p i need (MainPre env words) MainPostT (Stop := MainStopT)

end Rv64mc
