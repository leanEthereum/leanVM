/-
  Rv64mc.Final.MainSpec

  The contract of the guest's `main(len)` (`guest/src/main.rs`) that the end theorem takes: called with the input
  words at `inputBase` and their number in `a0`, and `NEXT` at the heap's start, if it returns `0` then the input
  decodes to a proof the verifier accepts (`Verdict`). With the calling convention, the stack bound and the frame
  of every contract (`Holds`). It says nothing of a return with another value, which is a rejection.
-/

import Rv64mc.Core.Holds
import Rv64mc.Bridge

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The heap's first address (`HEAP_START`, `guest/src/main.rs`): the initial value of `NEXT`. -/
def heapStart : Word := 0x20000000

/-- The stack top `_start` gives `main` (`li sp, 0xbffffff0`). -/
def stackTop : Word := 0xbffffff0

/-- `main`'s precondition on the input `words`: their number in `a0`, no more than fit below the heap, each at its
    place from `inputBase`, and `NEXT` at the heap's start. -/
def MainPre (env : Env) (words : List Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  regs .x10 = BitVec.ofNat 64 words.length ∧ words.length ≤ inputCapacity ∧
    (∀ i (h : i < words.length), m.getMem (inputBase + BitVec.ofNat 64 (8 * i)) = words[i]) ∧
    env.next m = heapStart

/-- `main`'s postcondition: a return with `a0 = 0` read an input that decodes to an accepted proof. -/
def MainPost (words : List Word) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  r' .x10 = 0 → Verdict words

/-- **`main`'s contract**, for every input: function `i` of `p`, with `need` bytes of stack. -/
def MainSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ words, Holds env p i need (MainPre env words) (MainPost words)

end Rv64mc
