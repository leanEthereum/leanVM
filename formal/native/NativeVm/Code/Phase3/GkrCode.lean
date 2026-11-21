module

public import NativeVm.Code.Phase3.GkrBase

/-!
# The GKR walk's code

`gkrCode`: `Model.verifyGkrGrandProducts depth`, `depth` at `depthR`. It reads the shared root into
`treeR`'s first element and the count root into `countR`, lays out the trees' values
`[shared, shared, count]` at `treeR`, four ones at `gOnes` and the remaining depth `rem := depth` at
`gRem`; then steps while `rem ≠ 0` (`stepC`), `step = 1` when `rem` is odd, `2` otherwise
(`gkrLayers`), each step's grinds of `0` bits (no code):

| block | model | does |
|---|---|---|
| `setStepC` | | `step` at `gStep`, `2^step = 2·step` at `gN` |
| `combC` | `sampleChallenge`, `polyEval` | the combiner at `gComb`, the claim at `gClaim`, the rounds' index and count |
| `roundsC` | `sumcheck` in equality mode | per coordinate `e` of the point: `2^step` scalars read, the message `claim + e·Σ tail :: tail`, a challenge `c` (at `e`'s place), the claim `polyEval message c` |
| `childC` | `childM` | three children read at `gChild j`, their products (`eeqEval` against ones) checked against the claim |
| `yC` | `sampleChallenges step`, `multilinearEval` | `y` at `gY`, the trees' values at `treeR`, `y` before the point, `rem -= step` |

The point is kept at `pointR` from element `rem` on, so that `y ++ x` lands in place.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Transcript NativeVm.Field

/-- Word `k` of the working area from `r`. -/
abbrev gwa (r : Reg64) (k : Nat) : Addr := at_ r (wdisp k)

/-- Word `k` of the working area from `r`, plus `8 · ix`. -/
abbrev gwx (r ix : Reg64) (k : Nat) : Addr := { base := r, idx := some (ix, .W64), disp := wdisp k }

/-- `step` and `2^step` from `rem`. -/
def setStepC : Stmt := blk [
  I (.load .rsi (cw ctxWork)), I (.load .rax (gwa .rsi gRem)),
  I (.andi .rax 1), I (.movi .rdx 2), I (.sub .rdx .rax),
  I (.store (gwa .rsi gStep) .rdx), I (.add .rdx .rdx), I (.store (gwa .rsi gN) .rdx)]

/-- The claim `polyEval values comb` from the values at `treeR` and the combiner at `gComb`. -/
def claimC : Stmt := blk [
  I (.load .r13 (cw ctxWork)), I (.load .r11 (gwa .r13 gComb)), I (.load .r12 (gwa .r13 (gComb + 1))),
  I (.addi .r13 (wdisp gTr)), I (.movi .r15 3), epolyEval,
  I (.load .rsi (cw ctxWork)), I (.store (gwa .rsi gClaim) .r9), I (.store (gwa .rsi (gClaim + 1)) .r10),
  I (.load .rax (gwa .rsi gRem)), I (.mov .rdx .rax), I (.add .rdx .rax), I (.store (gwa .rsi gPI) .rdx),
  I (.load .r14 (gwa .rsi gD)), I (.sub .r14 .rax), I (.store (gwa .rsi gCnt) .r14)]

/-- The combiner and the claim; the rounds' index and count (also in `r14`). -/
def combC : Stmt := blk [sampleTo gComb, claimC]

/-- A round's message: its tail read at `gTail`, its head `claim + e · Σ tail` at `gMsg`. -/
def msgC : Stmt := blk [
  I (.load .rsi (cw ctxWork)), I (.load .r12 (gwa .rsi gN)), readsTo gTail,
  I (.load .r13 (cw ctxWork)), I (.mov .r14 .r13), I (.load .r15 (gwa .r13 gN)),
  I (.addi .r13 (wdisp gTail)), I (.addi .r14 (wdisp gOnes)), edot,
  I (.load .rsi (cw ctxWork)), I (.load .rdx (gwa .rsi gPI)),
  I (.load .r11 (gwx .rsi .rdx gP)), I (.load .r12 (gwx .rsi .rdx (gP + 1))), emul,
  I (.load .rsi (cw ctxWork)),
  I (.load .r11 (gwa .rsi gClaim)), I (.xor .r9 .r11),
  I (.load .r11 (gwa .rsi (gClaim + 1))), I (.xor .r10 .r11),
  I (.store (gwa .rsi gMsg) .r9), I (.store (gwa .rsi (gMsg + 1)) .r10)]

/-- A round's end: the claim `polyEval message c`, `c` at the coordinate's place, the next round. -/
def nextC : Stmt := blk [
  I (.load .r13 (cw ctxWork)), I (.load .r11 (gwa .r13 gChal)), I (.load .r12 (gwa .r13 (gChal + 1))),
  I (.load .r15 (gwa .r13 gN)), I (.addi .r15 1), I (.addi .r13 (wdisp gMsg)), epolyEval,
  I (.load .rsi (cw ctxWork)), I (.store (gwa .rsi gClaim) .r9), I (.store (gwa .rsi (gClaim + 1)) .r10),
  I (.load .rdx (gwa .rsi gPI)),
  I (.store (gwx .rsi .rdx gP) .r11), I (.store (gwx .rsi .rdx (gP + 1)) .r12),
  I (.addi .rdx 2), I (.store (gwa .rsi gPI) .rdx),
  I (.load .r14 (gwa .rsi gCnt)), I (.subi .r14 1), I (.store (gwa .rsi gCnt) .r14)]

/-- A sumcheck round. -/
def roundC : Stmt := blk [msgC, sampleTo gChal, nextC]

/-- The sumcheck's rounds, their count in `r14`. -/
def roundsC : Stmt := .loop (.cmp .ne .r14 (.imm 0)) roundC

/-- Child `j` read. -/
def rdChildC (j : Nat) : Stmt :=
  blk [I (.load .rsi (cw ctxWork)), I (.load .r12 (gwa .rsi gN)), readsTo (gChild j)]

/-- Child `j`'s product at `gProd + 2 j`. -/
def prodC (j : Nat) : Stmt := blk [
  I (.load .r13 (cw ctxWork)), I (.mov .r14 .r13), I (.load .r15 (gwa .r13 gN)),
  I (.addi .r13 (wdisp (gChild j))), I (.addi .r14 (wdisp gOnes)), eeqEval,
  I (.load .rsi (cw ctxWork)), I (.store (gwa .rsi (gProd + 2 * j)) .r9),
  I (.store (gwa .rsi (gProd + 2 * j + 1)) .r10)]

/-- The check `claim == polyEval products comb`. -/
def checkC : Stmt := blk [
  I (.load .r13 (cw ctxWork)), I (.load .r11 (gwa .r13 gComb)), I (.load .r12 (gwa .r13 (gComb + 1))),
  I (.addi .r13 (wdisp gProd)), I (.movi .r15 3), epolyEval,
  I (.load .rsi (cw ctxWork)), I (.load .rax (gwa .rsi gClaim)), failIf (.cmp .ne .r9 (.reg .rax)),
  I (.load .rax (gwa .rsi (gClaim + 1))), failIf (.cmp .ne .r10 (.reg .rax))]

/-- The children and their check. -/
def childC : Stmt := blk [rdChildC 0, rdChildC 1, rdChildC 2, prodC 0, prodC 1, prodC 2, checkC]

/-- Child `j`'s value at `y`, at `treeR`'s element `j`. -/
def mleC (j : Nat) : Stmt := blk [
  I (.load .r13 (cw ctxWork)), I (.mov .r14 .r13), I (.mov .rsi .r13), I (.load .r15 (gwa .r13 gN)),
  I (.addi .r13 (wdisp (gChild j))), I (.addi .r14 (wdisp gMle)), I (.addi .rsi (wdisp gY)), emle,
  I (.load .rsi (cw ctxWork)), I (.store (gwa .rsi (gTr + 2 * j)) .r9),
  I (.store (gwa .rsi (gTr + 2 * j + 1)) .r10)]

/-- `rem -= step`, and `y` before the point. -/
def copyC : Stmt := blk [
  I (.load .rsi (cw ctxWork)), I (.load .rax (gwa .rsi gRem)), I (.load .rcx (gwa .rsi gStep)),
  I (.sub .rax .rcx), I (.store (gwa .rsi gRem) .rax), I (.add .rax .rax),
  I (.load .rdx (gwa .rsi gY)), I (.store (gwx .rsi .rax gP) .rdx),
  I (.load .rdx (gwa .rsi (gY + 1))), I (.store (gwx .rsi .rax (gP + 1)) .rdx),
  .ite (.cmp .eq .rcx (.imm 2)) (blk [
    I (.load .rdx (gwa .rsi (gY + 2))), I (.store (gwx .rsi .rax (gP + 2)) .rdx),
    I (.load .rdx (gwa .rsi (gY + 3))), I (.store (gwx .rsi .rax (gP + 3)) .rdx)]) .skip]

/-- `y`, the trees' values at it, the point. -/
def yC : Stmt := blk [
  I (.load .rsi (cw ctxWork)), I (.load .r12 (gwa .rsi gStep)), samplesTo gY,
  mleC 0, mleC 1, mleC 2, copyC]

/-- A step of the walk. -/
def stepC : Stmt := blk [setStepC, combC, roundsC, childC, yC]

/-- The trees' first values, the ones, `rem := depth` (also in `r14`). -/
def initC : Stmt := blk [
  I (.load .rsi (cw ctxWork)),
  I (.load .rax (gwa .rsi gTr)), I (.store (gwa .rsi (gTr + 2)) .rax),
  I (.load .rax (gwa .rsi (gTr + 1))), I (.store (gwa .rsi (gTr + 3)) .rax),
  I (.load .rax (gwa .rsi gCt)), I (.store (gwa .rsi (gTr + 4)) .rax),
  I (.load .rax (gwa .rsi (gCt + 1))), I (.store (gwa .rsi (gTr + 5)) .rax),
  I (.storei (gwa .rsi gOnes) 1), I (.storei (gwa .rsi (gOnes + 1)) 0),
  I (.storei (gwa .rsi (gOnes + 2)) 1), I (.storei (gwa .rsi (gOnes + 3)) 0),
  I (.storei (gwa .rsi (gOnes + 4)) 1), I (.storei (gwa .rsi (gOnes + 5)) 0),
  I (.storei (gwa .rsi (gOnes + 6)) 1), I (.storei (gwa .rsi (gOnes + 7)) 0),
  I (.load .r14 (gwa .rsi gD)), I (.store (gwa .rsi gRem) .r14)]

/-- The walk's loop. -/
def layersC : Stmt := .loop (.cmp .ne .r14 (.imm 0))
  (blk [stepC, I (.load .rsi (cw ctxWork)), I (.load .r14 (gwa .rsi gRem))])

/-- **`Model.verifyGkrGrandProducts depth`**, `depth` at `depthR`. -/
def gkrCode : Stmt := blk [readTo gTr, readTo gCt, initC, layersC]

end NativeVm.Code.P3
