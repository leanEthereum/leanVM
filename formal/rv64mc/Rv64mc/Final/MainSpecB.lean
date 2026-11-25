/-
  Rv64mc.Final.MainSpecB

  The total contract of the guest's `main(len)` that `BoolVerdict`'s end theorem takes:
  `MainSpecT` with the stopping set narrowed to the inputs that do not decode. Called as
  `MainSpecT`'s contract is, on an input of fewer than `maxInputWords` words, `main` returns `0`
  or `1`, or ends the run at the halting `ECALL` with `a0 = 2` and then `decodeInput words =
  none`: on a well-formed input it never aborts, so the allocator never runs out of heap, no
  panic is reached, and no `halt(ABORT)` of `main` is taken (`guest/src/main.rs`: input
  exhausted in `Input::word` or `Input::words`, input left over). It implies `MainSpecT`.

  ## Main definitions

  * `MainStopB`, `MainSpecB`

  ## Main results

  * `MainSpecB.mainSpecT`
-/

import Rv64mc.Final.MainSpecT

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- Where `main` may end the run on the input `words`: at the halting `ECALL`, in an accepting state with a nonempty
    stack, with `a0 = 2`, and only if `words` does not decode. -/
def MainStopB (words : List Word) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  r' .x10 = 2 ∧ decodeInput words = none

/-- **`main`'s total contract with abort only on malformed input**, for every input of fewer than `maxInputWords`
    words: function `i` of `p`, with `need` bytes of stack. -/
def MainSpecB (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ words : List Word, words.length < maxInputWords →
    HoldsT env p i need (MainPre env words) MainPostT (Stop := MainStopB words)

/-- `MainSpecB` implies `MainSpecT`: its stopping set is smaller. -/
theorem MainSpecB.mainSpecT {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : MainSpecB env p i need) :
    MainSpecT env p i need :=
  fun words hw => (h words hw).mono_stop fun _ _ _ _ _ hs => hs.1

end Rv64mc
