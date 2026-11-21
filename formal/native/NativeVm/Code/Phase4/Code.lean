module

public import NativeVm.Code.Data
public import NativeVm.Transcript.Code
public import NativeVm.Field.Arrays
public import NativeVm.Field.Powers

/-!
# Phase 4's code

The code of `Model.tablePhase` and `tableColumnClaims`, in blocks, each proved in a module of its
own (`NativeVm.Code.Phase4.*`):

| block | model | does |
|---|---|---|
| `xiC` | `sampleChallenge` | `ξ` |
| `targetC` | `powers`, `dot` | `ξ`'s five powers at `oXP`, the target `dot formPowers totals` at `oCLM` |
| `roundsC` | `sumcheckPlain target 4 nRounds` | the rounds' count, then each round: three scalars read (`readN`), the message, `r`, the claim `polyEval` |
| `weightsC` | `tableWeights` | each table's weight at `oWT` |
| `termsC` | `tableTerms`' loop | per table: its point and its evaluations at `evalsR`, its weighted terms added to `oFIN` |
| `checkC` | `require (final == claim)` | |
| `claimsC` | `tableColumnClaims` | the column claims appended at `claimsR` |

The grinds before `ξ` and in the rounds are of `grindingBits 4 = grindingBits 3 = 0` bits: no
code. A challenge `r_k` of round `k` goes to the point's entry `nRounds - 1 - k`, so the point
(`challenges.reverse`) is in order at `oPT`.

**Registers.** The transcript's gadgets write `Transcript.clobbers` only, so the rounds keep the
work area's address in `rbp` and the rounds left in `r14`; the field kernels write nearly every
register, so the tables' loop keeps its state in the scratch words (`oTIX`, `oFPTR`, `oEPTR`) and
reloads the work area's address from the context (`ctxWork`).
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Transcript NativeVm.Field

/-! ## The words

Offsets in the working area, as numerals (`Phase4.Words` proves them the regions'). -/

/-- `layoutR`'s first word. -/
abbrev oL : Nat := 69
/-- `busR`'s first word. -/
abbrev oB : Nat := 622
/-- The bus's GKR point (`busPointOff`). -/
abbrev oBP : Nat := oB + 13338
/-- The bus's totals (`busTotalsOff`). -/
abbrev oBT : Nat := oB + 13465
/-- `evalsR`'s first word. -/
abbrev oE : Nat := 14093
/-- `claimsR`'s first word. -/
abbrev oC : Nat := 15569
/-- The scratch region's first word. -/
abbrev oS : Nat := 52670
/-- `ξ`'s five powers: the constraints' two, then the forms' three. -/
abbrev oXP : Nat := oS
/-- The sumcheck's running claim. -/
abbrev oCLM : Nat := oS + 10
/-- The tables' running sum `final`. -/
abbrev oFIN : Nat := oS + 12
/-- A round's message, four coefficients. -/
abbrev oMSG : Nat := oS + 14
/-- The point, at most `tablePointCap` coordinates. -/
abbrev oPT : Nat := oS + 22
/-- The six tables' weights. -/
abbrev oWT : Nat := oS + 82
/-- `JUMP`'s two constraints. -/
abbrev oCV : Nat := oS + 94
/-- A table's term. -/
abbrev oTOT : Nat := oS + 98
/-- A form's running sum. -/
abbrev oSUM : Nat := oS + 100
/-- The rounds' count. -/
abbrev oNR : Nat := oS + 102
/-- The tables' loop: the table. -/
abbrev oTIX : Nat := oS + 103
/-- The tables' loop: the table's forms' address. -/
abbrev oFPTR : Nat := oS + 104
/-- The tables' loop: the table's entry of `evalsR`'s address. -/
abbrev oEPTR : Nat := oS + 105
/-- The tables' widths, six words. -/
abbrev oWID : Nat := oS + 106

/-- The scratch words phase 4 uses. -/
abbrev scratchUsed : Nat := 112

/-- The words of a form (`formWords`). -/
abbrev fW : Nat := 741
/-- The words of a table's three forms. -/
abbrev formsStride : Nat := 3 * fW
/-- The words of a table's entry of `evalsR` (`evalStride`). -/
abbrev eS : Nat := 246
/-- Where a table's evaluations start in its entry of `evalsR` (`vecWords tablePointCap`). -/
abbrev evOff : Nat := 61
/-- The words of a column claim (`claimWords`). -/
abbrev cW : Nat := 76
/-- Where a column claim's value is (`1 + vecWords pointCap`). -/
abbrev cV : Nat := 74

/-- The tables' widths (`tableWidths`). -/
def widths : List Nat := [13, 13, 7, 14, 14, 92]

/-- `JUMP`'s table, and its columns `v_cond`, `w`, `b`. -/
abbrev tJump : Nat := 4
abbrev cCond : Nat := 5
abbrev cInv : Nat := 12
abbrev cFlag : Nat := 13

/-- Word `k` of the working area from `r`. -/
abbrev wa (r : Reg64) (k : Nat) : Addr := at_ r (wdisp k)

/-- Word `k` of the working area from `r`, plus `8 · ix`. -/
abbrev wx (r ix : Reg64) (k : Nat) : Addr := { base := r, idx := some (ix, .W64), disp := wdisp k }

/-! ## Reading scalars into memory -/

/-- `readScalars r13` to the elements from `r12` on. -/
def readN : Stmt := .loop (.test false .r13 (.reg .r13)) (blk [
  readScalar,
  I (.store (at_ .r12 0) .r9), I (.store (at_ .r12 8) .r10),
  I (.addi .r12 16), I (.subi .r13 1)])

/-! ## `ξ` and the target -/

/-- `ξ`. -/
def xiC : Stmt := sampleChallenge

/-- `ξ`'s powers at `oXP` (`ξ` in `A`), then `dot formPowers totals` at `oCLM`. -/
def targetC : Stmt := blk [
  I (.mov .r11 .r9), I (.mov .r12 .r10),
  I (.load .r14 (cw ctxWork)), I (.addi .r14 (wdisp oXP)),
  I (.movi .r15 5),
  epowers,
  I (.load .r13 (cw ctxWork)), I (.addi .r13 (wdisp (oXP + 4))),
  I (.load .r14 (cw ctxWork)), I (.addi .r14 (wdisp oBT)),
  I (.movi .r15 3),
  edot,
  I (.load .rax (cw ctxWork)),
  I (.store (wa .rax oCLM) .r9), I (.store (wa .rax (oCLM + 1)) .r10)]

/-! ## The rounds -/

/-- The largest log-height into `r14`, the work area's address in `rbp`. -/
def maxC : Stmt := blk [
  I (.load .rbp (cw ctxWork)),
  I (.movi .r14 0), I (.movi .rcx 0),
  .loop (.cmp .ltu .rcx (.imm 6)) (blk [
    I (.load .rax (wx .rbp .rcx (oL + 4))),
    .ite (.cmp .ltu .r14 (.reg .rax)) (I (.mov .r14 .rax)) .skip,
    I (.addi .rcx 1)]),
  I (.store (wa .rbp oNR) .r14)]

/-- The message from the three scalars at its entries `1 .. 3`: entry `0` the first, entry `1`
the claim plus the other two. -/
def msgC : Stmt := blk [
  I (.load .rax (wa .rbp (oMSG + 2))), I (.store (wa .rbp oMSG) .rax),
  I (.load .rax (wa .rbp (oMSG + 3))), I (.store (wa .rbp (oMSG + 1)) .rax),
  I (.load .rax (wa .rbp oCLM)), I (.load .rcx (wa .rbp (oMSG + 4))), I (.xor .rax .rcx),
  I (.load .rcx (wa .rbp (oMSG + 6))), I (.xor .rax .rcx), I (.store (wa .rbp (oMSG + 2)) .rax),
  I (.load .rax (wa .rbp (oCLM + 1))), I (.load .rcx (wa .rbp (oMSG + 5))), I (.xor .rax .rcx),
  I (.load .rcx (wa .rbp (oMSG + 7))), I (.xor .rax .rcx), I (.store (wa .rbp (oMSG + 3)) .rax)]

/-- The challenge in `A` to the point's entry `r14 - 1`. -/
def storeChC : Stmt := blk [
  I (.mov .rax .r14), I (.subi .rax 1), I (.shli .rax 4), I (.add .rax .rbp),
  I (.store (wa .rax oPT) .r9), I (.store (wa .rax (oPT + 1)) .r10)]

/-- The claim: the message at the challenge in `A`. -/
def claimC : Stmt := blk [
  I (.mov .r11 .r9), I (.mov .r12 .r10),
  I (.lea .r13 (wa .rbp oMSG)), I (.movi .r15 4),
  epolyEval,
  I (.store (wa .rbp oCLM) .r9), I (.store (wa .rbp (oCLM + 1)) .r10)]

/-- One round, `r14` rounds left. -/
def roundC : Stmt := blk [
  I (.lea .r12 (wa .rbp (oMSG + 2))), I (.movi .r13 3),
  readN,
  msgC,
  sampleChallenge,
  storeChC,
  claimC,
  I (.subi .r14 1)]

/-- The rounds. -/
def roundsC : Stmt := blk [maxC, .loop (.test false .r14 (.reg .r14)) roundC]

/-! ## The weights -/

/-- The factor of coordinate `r14` for a table of log-height `r15`, into `B`. -/
def factorC : Stmt := blk [
  I (.mov .rax .r14), I (.shli .rax 4), I (.add .rax .rbp),
  I (.load .r11 (wa .rax oPT)), I (.load .r12 (wa .rax (oPT + 1))),
  .ite (.cmp .ltu .r14 (.reg .r15)) (blk [
    I (.xori .r11 1),
    I (.load .rcx (wa .rbp oBP)),
    .ite (.cmp .ltu .r14 (.reg .rcx)) (blk [
      I (.mov .rax .r14), I (.shli .rax 4), I (.add .rax .rbp),
      I (.load .rcx (wa .rax (oBP + 1))), I (.xor .r11 .rcx),
      I (.load .rcx (wa .rax (oBP + 2))), I (.xor .r12 .rcx)]) .skip]) .skip]

/-- Table `r13`'s weight, to its entry of `oWT`. -/
def weightC : Stmt := blk [
  I (.load .r15 (wx .rbp .r13 (oL + 4))),
  I (.movi .r9 1), I (.movi .r10 0), I (.movi .r14 0),
  .loop (.cmp .ltu .r14 (.reg .rsi)) (blk [factorC, emul, I (.addi .r14 1)]),
  I (.mov .rax .r13), I (.shli .rax 4), I (.add .rax .rbp),
  I (.store (wa .rax oWT) .r9), I (.store (wa .rax (oWT + 1)) .r10),
  I (.addi .r13 1)]

/-- The weights. -/
def weightsC : Stmt := blk [
  I (.load .rbp (cw ctxWork)), I (.load .rsi (wa .rbp oNR)), I (.movi .r13 0),
  .loop (.cmp .ltu .r13 (.imm 6)) weightC]

/-! ## The tables -/

/-- A form's value on a row: the form at `r13`, the row's elements at `r14`, its width in `r15`;
the value in `A`, the running sum at `oSUM`. -/
def colC : Stmt := blk [
  I (.load .rax (wx .r13 .rbp 1)),
  .ite (.cmp .ltu .rax (.reg .r15))
    (blk [I (.shli .rax 4), I (.add .rax .r14), I (.load .r11 (wa .rax 0)),
      I (.load .r12 (wa .rax 1))])
    (blk [I (.movi .r11 0), I (.movi .r12 0)]),
  emul,
  I (.addi .rbp 1), I (.load .rcx (wa .r13 0))]

/-- One term: its coefficient times its columns, added to `oSUM`. -/
def termC : Stmt := blk [
  I (.load .r9 (wa .r13 3)), I (.load .r10 (wa .r13 4)),
  I (.movi .rbp 0), I (.load .rcx (wa .r13 0)),
  .loop (.cmp .ltu .rbp (.reg .rcx)) colC,
  I (.load .rax (cw ctxWork)),
  I (.load .rcx (wa .rax oSUM)), I (.xor .rcx .r9), I (.store (wa .rax oSUM) .rcx),
  I (.load .rcx (wa .rax (oSUM + 1))), I (.xor .rcx .r10), I (.store (wa .rax (oSUM + 1)) .rcx),
  I (.addi .r13 (wdisp 5)), I (.subi .rsi 1)]

/-- `FormW.evaluate`: the form at `r13`, the row at `r14`, `r15` wide. -/
def formC : Stmt := blk [
  I (.load .rsi (wa .r13 0)), I (.addi .r13 (wdisp 1)),
  I (.load .rax (cw ctxWork)),
  I (.storei (wa .rax oSUM) 0), I (.storei (wa .rax (oSUM + 1)) 0),
  .loop (.test false .rsi (.reg .rsi)) termC,
  I (.load .rax (cw ctxWork)),
  I (.load .r9 (wa .rax oSUM)), I (.load .r10 (wa .rax (oSUM + 1)))]

/-- Side `j`'s form's value times `formPowers[j]`, added to `oTOT`. -/
def sideC (j : Nat) : Stmt := blk [
  I (.load .rbp (cw ctxWork)),
  I (.load .r13 (wa .rbp oFPTR)), I (.addi .r13 (wdisp (fW * j))),
  I (.load .r14 (wa .rbp oEPTR)), I (.addi .r14 (wdisp (evOff + 1))),
  I (.load .rax (wa .rbp oTIX)), I (.load .r15 (wx .rbp .rax oWID)),
  formC,
  I (.load .rbp (cw ctxWork)),
  I (.load .r11 (wa .rbp (oXP + 4 + 2 * j))), I (.load .r12 (wa .rbp (oXP + 5 + 2 * j))),
  emul,
  I (.load .rax (wa .rbp oTOT)), I (.xor .rax .r9), I (.store (wa .rbp oTOT) .rax),
  I (.load .rax (wa .rbp (oTOT + 1))), I (.xor .rax .r10), I (.store (wa .rbp (oTOT + 1)) .rax)]

/-- `JUMP`'s constraints dotted with the constraints' powers, into `oTOT`. -/
def jumpC : Stmt := blk [
  I (.load .rbp (cw ctxWork)), I (.load .r14 (wa .rbp oEPTR)),
  I (.load .r9 (wa .r14 (evOff + 1 + 2 * cCond))),
  I (.load .r10 (wa .r14 (evOff + 2 + 2 * cCond))),
  I (.load .r11 (wa .r14 (evOff + 1 + 2 * cInv))),
  I (.load .r12 (wa .r14 (evOff + 2 + 2 * cInv))),
  emul,
  I (.load .rax (wa .r14 (evOff + 1 + 2 * cFlag))), I (.xor .r9 .rax),
  I (.load .rax (wa .r14 (evOff + 2 + 2 * cFlag))), I (.xor .r10 .rax),
  I (.store (wa .rbp oCV) .r9), I (.store (wa .rbp (oCV + 1)) .r10),
  I (.load .r9 (wa .r14 (evOff + 1 + 2 * cFlag))), I (.xori .r9 1),
  I (.load .r10 (wa .r14 (evOff + 2 + 2 * cFlag))),
  I (.load .r11 (wa .r14 (evOff + 1 + 2 * cCond))),
  I (.load .r12 (wa .r14 (evOff + 2 + 2 * cCond))),
  emul,
  I (.store (wa .rbp (oCV + 2)) .r9), I (.store (wa .rbp (oCV + 3)) .r10),
  I (.lea .r13 (wa .rbp oXP)), I (.lea .r14 (wa .rbp oCV)), I (.movi .r15 2),
  edot,
  I (.load .rbp (cw ctxWork)),
  I (.store (wa .rbp oTOT) .r9), I (.store (wa .rbp (oTOT + 1)) .r10)]

/-- Copy `r15` elements from `r13` to `r12`. -/
def copyC : Stmt := .loop (.test false .r15 (.reg .r15)) (blk [
  I (.load .rax (wa .r13 0)), I (.store (wa .r12 0) .rax),
  I (.load .rax (wa .r13 1)), I (.store (wa .r12 1) .rax),
  I (.addi .r13 (wdisp 2)), I (.addi .r12 (wdisp 2)), I (.subi .r15 1)])

/-- The table's point (its first log-height coordinates) to its entry of `evalsR`, its
evaluations' count after it; `r12`, `r13` set for `readN`. -/
def rowPreC : Stmt := blk [
  I (.load .rbp (cw ctxWork)),
  I (.load .rax (wa .rbp oTIX)), I (.load .r15 (wx .rbp .rax (oL + 4))),
  I (.load .r14 (wa .rbp oEPTR)),
  I (.store (wa .r14 0) .r15),
  I (.lea .r13 (wa .rbp oPT)), I (.lea .r12 (wa .r14 1)),
  copyC,
  I (.load .rax (wa .rbp oTIX)), I (.load .r13 (wx .rbp .rax oWID)),
  I (.store (wa .r14 evOff) .r13),
  I (.lea .r12 (wa .r14 (evOff + 1)))]

/-- The table's point, then its evaluations read. -/
def readRowC : Stmt := blk [rowPreC, readN]

/-- The table's term: `JUMP`'s constraints, its forms; times its weight, added to `oFIN`. -/
def termsC1 : Stmt := blk [
  I (.load .rbp (cw ctxWork)),
  I (.storei (wa .rbp oTOT) 0), I (.storei (wa .rbp (oTOT + 1)) 0),
  I (.load .rax (wa .rbp oTIX)),
  .ite (.cmp .eq .rax (.imm (Int64.ofNat tJump))) jumpC .skip,
  sideC 0, sideC 1, sideC 2,
  I (.load .rbp (cw ctxWork)),
  I (.load .rax (wa .rbp oTIX)), I (.shli .rax 4), I (.add .rax .rbp),
  I (.load .r11 (wa .rax oWT)), I (.load .r12 (wa .rax (oWT + 1))),
  I (.load .r9 (wa .rbp oTOT)), I (.load .r10 (wa .rbp (oTOT + 1))),
  emul,
  I (.load .rax (wa .rbp oFIN)), I (.xor .rax .r9), I (.store (wa .rbp oFIN) .rax),
  I (.load .rax (wa .rbp (oFIN + 1))), I (.xor .rax .r10), I (.store (wa .rbp (oFIN + 1)) .rax)]

/-- The next table: its index, its forms' and its entry's addresses; the index in `rcx`. -/
def nextC : Stmt := blk [
  I (.load .rbp (cw ctxWork)),
  I (.load .rax (wa .rbp oFPTR)), I (.addi .rax (wdisp formsStride)),
  I (.store (wa .rbp oFPTR) .rax),
  I (.load .rax (wa .rbp oEPTR)), I (.addi .rax (wdisp eS)),
  I (.store (wa .rbp oEPTR) .rax),
  I (.load .rcx (wa .rbp oTIX)), I (.addi .rcx 1), I (.store (wa .rbp oTIX) .rcx)]

/-- One table. -/
def tableC : Stmt := blk [readRowC, termsC1, nextC]

/-- The loop's start: `final = 0`, the widths, the first table's addresses. -/
def termsInitC : Stmt := blk [
  I (.load .rbp (cw ctxWork)),
  I (.storei (wa .rbp oFIN) 0), I (.storei (wa .rbp (oFIN + 1)) 0),
  I (.storei (wa .rbp oWID) 13), I (.storei (wa .rbp (oWID + 1)) 13),
  I (.storei (wa .rbp (oWID + 2)) 7), I (.storei (wa .rbp (oWID + 3)) 14),
  I (.storei (wa .rbp (oWID + 4)) 14), I (.storei (wa .rbp (oWID + 5)) 92),
  I (.lea .rax (wa .rbp oB)), I (.store (wa .rbp oFPTR) .rax),
  I (.lea .rax (wa .rbp oE)), I (.store (wa .rbp oEPTR) .rax),
  I (.movi .rcx 0), I (.store (wa .rbp oTIX) .rcx)]

/-- The tables. -/
def termsC : Stmt := blk [termsInitC, .loop (.cmp .ltu .rcx (.imm 6)) tableC]

/-- `require (final == claim)`. -/
def checkC : Stmt := blk [
  I (.load .rbp (cw ctxWork)),
  I (.load .rax (wa .rbp oFIN)), I (.load .rcx (wa .rbp oCLM)), failIf (.cmp .ne .rax (.reg .rcx)),
  I (.load .rax (wa .rbp (oFIN + 1))), I (.load .rcx (wa .rbp (oCLM + 1))),
  failIf (.cmp .ne .rax (.reg .rcx))]

/-! ## The column claims -/

/-- One claim: the column `r13`, the point at `r14`, the value at `r10`, to `r12`. -/
def claimOneC : Stmt := blk [
  I (.store (wa .r12 0) .r13),
  I (.load .rcx (wa .r14 0)), I (.store (wa .r12 1) .rcx),
  I (.lea .r8 (wa .r14 1)), I (.lea .r9 (wa .r12 2)), I (.shli .rcx 1),
  .loop (.test false .rcx (.reg .rcx)) (blk [
    I (.load .rax (wa .r8 0)), I (.store (wa .r9 0) .rax),
    I (.addi .r8 (wdisp 1)), I (.addi .r9 (wdisp 1)), I (.subi .rcx 1)]),
  I (.load .rax (wa .r10 0)), I (.store (wa .r12 cV) .rax),
  I (.load .rax (wa .r10 1)), I (.store (wa .r12 (cV + 1)) .rax),
  I (.addi .r10 (wdisp 2)), I (.addi .r12 (wdisp cW)), I (.addi .r13 1), I (.subi .r11 1)]

/-- One table's claims, its entry of `evalsR` at `r14`. -/
def claimTableC : Stmt := blk [
  I (.load .r11 (wa .r14 evOff)), I (.lea .r10 (wa .r14 (evOff + 1))),
  .loop (.test false .r11 (.reg .r11)) claimOneC,
  I (.addi .r14 (wdisp eS)), I (.subi .r15 1)]

/-- The tables' column claims after the `count` claims there: claim `count + i` at word
`1 + claimWords · (count + i)`, of the column `globalColumnCount + i`. -/
def claimsC : Stmt := blk [
  I (.load .rbp (cw ctxWork)),
  I (.load .rax (wa .rbp oC)),
  I (.mov .rcx .rax), I (.shli .rcx 9), I (.mov .rdx .rax), I (.shli .rdx 6), I (.add .rcx .rdx),
  I (.mov .rdx .rax), I (.shli .rdx 5), I (.add .rcx .rdx), I (.add .rcx .rbp),
  I (.lea .r12 (wa .rcx (oC + 1))),
  I (.movi .r13 5), I (.lea .r14 (wa .rbp oE)), I (.movi .r15 6),
  .loop (.test false .r15 (.reg .r15)) claimTableC,
  I (.load .rax (wa .rbp oC)), I (.add .rax .r13), I (.subi .rax 5),
  I (.store (wa .rbp oC) .rax)]

/-- **Phase 4**. -/
def phase4Code : Stmt := blk [xiC, targetC, roundsC, weightsC, termsC, checkC, claimsC]

end NativeVm.Code.P4
