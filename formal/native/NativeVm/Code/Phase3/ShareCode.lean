module

public import NativeVm.Code.Phase3.Common
public import NativeVm.Field.Mle

/-!
# The bytecode share: the code

`shareCode` runs `bytecodeShare` (`Model/Bus.lean`): the share read into `shareR`, the
plain-mode sumcheck's four rounds (`sumcheckPlain share 3 busBits`: each reads the constant and
the quadratic coefficient, whose grind has `0` bits, samples the challenge into `slotR` and
moves the claim, in `tmpR`, to the round polynomial's value there), the value read into `valueR`,
then the check `claim = dot (eqKernel slot) weights · value`, the dot product being the weights'
multilinear extension at the slot (`emle`, its work area in `tmpR`).

Registers of the rounds' loop: `r13` the rounds left, `r14` the next challenge's address; both kept
by the transcript's gadgets.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Field NativeVm.Transcript NativeVm.Code

/-- The running claim, in `tmpR`. -/
def shClaimR : Region := sreg 2048 2
/-- A round's constant coefficient. -/
def shConstR : Region := sreg 2050 2
/-- A round's quadratic coefficient. -/
def shTailR : Region := sreg 2052 2
/-- `emle`'s work area, `16` words. -/
def shFoldR : Region := sreg 2056 16

/-- The words of those regions. -/
abbrev shClaimW : Nat := shClaimR.off
abbrev shConstW : Nat := shConstR.off
abbrev shTailW : Nat := shTailR.off
abbrev shFoldW : Nat := shFoldR.off

/-- A round after its challenge's store: `B := x`, `A := ((t·x + claim) + t)·x + c` into the claim,
`r14` to the next challenge, `r13` counted down. -/
def shRoundTail : List Stmt := [
  I (.mov .r11 .r9), I (.mov .r12 .r10),
  I (.load .rsi (cw ctxWork)),
  I (.load .r9 (at_ .rsi (wdisp shTailW))), I (.load .r10 (at_ .rsi (wdisp (shTailW + 1)))),
  emul,
  I (.load .rax (at_ .rsi (wdisp shClaimW))), I (.xor .r9 .rax),
  I (.load .rax (at_ .rsi (wdisp (shClaimW + 1)))), I (.xor .r10 .rax),
  I (.load .rax (at_ .rsi (wdisp shTailW))), I (.xor .r9 .rax),
  I (.load .rax (at_ .rsi (wdisp (shTailW + 1)))), I (.xor .r10 .rax),
  emul,
  I (.load .rax (at_ .rsi (wdisp shConstW))), I (.xor .r9 .rax),
  I (.load .rax (at_ .rsi (wdisp (shConstW + 1)))), I (.xor .r10 .rax),
  I (.store (at_ .rsi (wdisp shClaimW)) .r9), I (.store (at_ .rsi (wdisp (shClaimW + 1))) .r10),
  I (.addi .r14 16), I (.subi .r13 1)]

/-- One round: the two coefficients, the challenge at `r14`, the claim moved to the round
polynomial's value there. -/
def shRound : Stmt := blk (readTo shConstW :: readTo shTailW :: Transcript.sampleChallenge ::
  I (.store (at_ .r14 0) .r9) :: I (.store (at_ .r14 8) .r10) :: shRoundTail)

/-- The share into `shareR` and the claim. -/
def shStart : Stmt := blk [
  readTo shareR.off,
  I (.load .r11 (cw ctxWork)),
  I (.load .r9 (at_ .r11 (wdisp shareR.off))), I (.load .r10 (at_ .r11 (wdisp (shareR.off + 1)))),
  I (.store (at_ .r11 (wdisp shClaimW)) .r9), I (.store (at_ .r11 (wdisp (shClaimW + 1))) .r10),
  I (.movi .r13 4), I (.lea .r14 (at_ .r11 (wdisp slotR.off)))]

/-- The check: the weights' extension at the slot times the value against the claim. -/
def shCheck : Stmt := blk [
  I (.load .r11 (cw ctxWork)),
  I (.lea .r13 (at_ .r11 (wdisp wR.off))), I (.lea .r14 (at_ .r11 (wdisp shFoldW))),
  I (.lea .rsi (at_ .r11 (wdisp slotR.off))), I (.movi .r15 16),
  emle,
  I (.load .rsi (cw ctxWork)),
  I (.load .r11 (at_ .rsi (wdisp valueR.off))), I (.load .r12 (at_ .rsi (wdisp (valueR.off + 1)))),
  emul,
  I (.load .rax (at_ .rsi (wdisp shClaimW))), failIf (.cmp .ne .r9 (.reg .rax)),
  I (.load .rax (at_ .rsi (wdisp (shClaimW + 1)))), failIf (.cmp .ne .r10 (.reg .rax))]

/-- **`bytecodeShare`.** -/
def shareCode : Stmt := blk [
  shStart,
  .loop (.cmp .ne .r13 (.imm 0)) shRound,
  readTo valueR.off,
  shCheck]

end NativeVm.Code.P3
