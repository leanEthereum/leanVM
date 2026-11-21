module

public import NativeVm.Code.Phase3.Common
public import NativeVm.Code.Phase3.FormsDataDefs
public import Native.Keccak

/-!
# The bus forms of a side: the code

`accumulateSide`'s forms (`sideFold`), for one side whose table blocks are the literal data `D`
(`FormsData*`). The code works in `formTmpR` (word offsets from the working area's start):

* `padOff`: the padding row `P`, word `i` the lane of column `i` of `KECCAK`'s padding row (zero
  outside its output lanes `40 .. 65`): zeroed, `Keccak.permute` run with `rdi` at `P + 40`, then the
  permutation's other scratch words zeroed again (`padCode`);
* `fOff`: the block form `F`, at most `fCap` terms, in `FormAt`'s format with unused column words
  zero;
* `wvOff`, `bvOff`: the count side's slot weight `1` and `β = 0`;
* `vCur`, `vSel`, `vRem`, `vG`: the loop's state (the next block's data, the next selector, the blocks
  left, the owner's form);
* `dOff`: the data, `encode side D`: per block the owner's form's offset and the entry count, then
  per entry the monomial's key (degree, two columns) and the slot and coefficient (`dataCode`).

Per block (`blockCode`): `F := const β`, then for each entry `F.addTerm m (w_slot · c)` (`buildCode`);
the padding rows' term `sel · pw · (F.evaluate P + 1)` added into `sumR side` (`evalCode`); then for
each term of `F`, `G.addTerm m (sel · c)` into the owner's form `G` in `busR` (`accCode`).
`atCode` is `FormW.addTerm`: the form at `r13`, the key at `r12`, the coefficient in `(r9, r10)`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

/-! ## The scratch's words -/

/-- `formTmpR`'s first word. -/
def ftOff : Nat := formTmpR.off
/-- The padding row (`124` words: the permutation's scratch from word `40`). -/
def padOff : Nat := ftOff
/-- The block form. -/
def fOff : Nat := ftOff + 128
/-- The block form's capacity. -/
def fCap : Nat := 32
/-- The count side's slot weight. -/
def wvOff : Nat := ftOff + 320
/-- The count side's `β`. -/
def bvOff : Nat := ftOff + 352
/-- The next block's data. -/
def vCur : Nat := ftOff + 300
/-- The next block's selector. -/
def vSel : Nat := ftOff + 301
/-- The blocks left. -/
def vRem : Nat := ftOff + 302
/-- The owner's form. -/
def vG : Nat := ftOff + 303
/-- The data. -/
def dOff : Nat := ftOff + 512

/-! ## The data's words -/

/-- An entry: the monomial's degree and columns (zero past the degree), the slot, the coefficient. -/
def encEnt (e : DEnt) : List Nat := [e.2.1.length, e.2.1.getD 0 0, e.2.1.getD 1 0, e.1, e.2.2]

/-- A block: the owner's form's word, the entry count, the entries. -/
def encBlk (side : Nat) (b : DBlk) : List Nat :=
  (busR.off + formOff b.1 side) :: b.2.length :: b.2.flatMap encEnt

/-- The data's words. -/
def encode (side : Nat) (D : List DBlk) : List Nat := D.flatMap (encBlk side)

/-! ## Code -/

/-- `r11 :=` the working area. -/
def wk : Stmt := I (.load .r11 (cw ctxWork))

/-- Word `k` of the working area, at `r11`. -/
abbrev aw (k : Nat) : Addr := at_ .r11 (wdisp k)

/-- Element `rax / 2` of the array at `b` (`rax` twice the index), limb `l`. -/
abbrev aix (b : Reg64) (l : Nat) : Addr := { base := b, idx := some (.rax, .W64), disp := wdisp l }

/-- The stores of words `ws` from word `k`. -/
def storeL : Nat → List Nat → List Stmt
  | _, [] => []
  | k, w :: ws => I (.storei (aw k) (Int64.ofNat w)) :: storeL (k + 1) ws

/-- **`FormW.addTerm`**: the form at `r13`, the monomial's key (degree, two columns) at `r12`, the
coefficient in `(r9, r10)`. The terms are searched for the key (`rdx` the term, `rsi` the terms
left, `rcx` set when found): a match gets the coefficient added, else the term is appended. -/
def atCode : Stmt := blk [
  I (.load .rsi (at_ .r13 (wdisp 0))), I (.lea .rdx (at_ .r13 (wdisp 1))), I (.movi .rcx 0),
  .loop (.cmp .ne .rsi (.imm 0)) (blk [
    I (.load .rax (at_ .rdx (wdisp 0))), I (.load .rbx (at_ .r12 (wdisp 0))), I (.xor .rax .rbx),
    I (.load .rbx (at_ .rdx (wdisp 1))), I (.load .r8 (at_ .r12 (wdisp 1))), I (.xor .rbx .r8), I (.or .rax .rbx),
    I (.load .rbx (at_ .rdx (wdisp 2))), I (.load .r8 (at_ .r12 (wdisp 2))), I (.xor .rbx .r8), I (.or .rax .rbx),
    .ite (.cmp .eq .rax (.imm 0))
      (blk [I (.load .rax (at_ .rdx (wdisp 3))), I (.xor .rax .r9), I (.store (at_ .rdx (wdisp 3)) .rax),
        I (.load .rax (at_ .rdx (wdisp 4))), I (.xor .rax .r10), I (.store (at_ .rdx (wdisp 4)) .rax),
        I (.movi .rcx 1), I (.movi .rsi 0)])
      (blk [I (.addi .rdx 40), I (.subi .rsi 1)])]),
  .ite (.cmp .eq .rcx (.imm 0))
    (blk [I (.load .rax (at_ .r12 (wdisp 0))), I (.store (at_ .rdx (wdisp 0)) .rax),
      I (.load .rax (at_ .r12 (wdisp 1))), I (.store (at_ .rdx (wdisp 1)) .rax),
      I (.load .rax (at_ .r12 (wdisp 2))), I (.store (at_ .rdx (wdisp 2)) .rax),
      I (.store (at_ .rdx (wdisp 3)) .r9), I (.store (at_ .rdx (wdisp 4)) .r10),
      I (.load .rax (at_ .r13 (wdisp 0))), I (.addi .rax 1), I (.store (at_ .r13 (wdisp 0)) .rax)])
    .skip]

/-- The entries' loop: `r12` the entry, `r14` the end, `r13` the block form, `r15` the slot
weights. -/
def entLoop : Stmt :=
  .loop (.cmp .ne .r12 (.reg .r14)) (blk [
    I (.load .rax (at_ .r12 (wdisp 3))), I (.shli .rax 1),
    I (.load .r9 (aix .r15 0)), I (.load .r10 (aix .r15 1)),
    I (.load .r11 (at_ .r12 (wdisp 4))), escale, atCode, I (.addi .r12 40)])

/-- The block form's start: the owner's form's address to `vG`, `F := const β`; the first entry in
`r12`, the end in `r14`, the block form in `r13`, the slot weights (at word `wOff`) in `r15`. -/
def buildPre (wOff bOff : Nat) : Stmt := blk [
  wk, I (.load .r12 (aw vCur)),
  I (.load .rax (at_ .r12 (wdisp 0))), I (.shli .rax 3), I (.add .rax .r11), I (.store (aw vG) .rax),
  I (.storei (aw fOff) 1), I (.storei (aw (fOff + 1)) 0), I (.storei (aw (fOff + 2)) 0),
  I (.storei (aw (fOff + 3)) 0),
  I (.load .rax (aw bOff)), I (.store (aw (fOff + 4)) .rax),
  I (.load .rax (aw (bOff + 1))), I (.store (aw (fOff + 5)) .rax),
  I (.load .r14 (at_ .r12 (wdisp 1))), I (.mov .rax .r14), I (.shli .r14 5), I (.shli .rax 3),
  I (.add .r14 .rax), I (.addi .r12 16), I (.add .r14 .r12),
  I (.lea .r13 (aw fOff)), I (.lea .r15 (aw wOff))]

/-- **The block form**: `buildPre`, the entries added; the next block's data to `vCur`. The slot
weights at word `wOff`, `β` at `bOff`. -/
def buildCode (wOff bOff : Nat) : Stmt := blk [buildPre wOff bOff, entLoop, wk, I (.store (aw vCur) .r12)]

/-- `A := A · P[column]`, the column at word `k` of the term at `rsi`, the padding row at `rbp`. -/
def scaleCol (k : Nat) : Stmt := blk [
  I (.load .rax (at_ .rsi (wdisp k))), I (.load .r11 (aix .rbp 0)), escale]

/-- A term's monomial on the padding row, times `A` (its coefficient): by its degree in `rax`. -/
def tvCode : Stmt :=
  .ite (.cmp .eq .rax (.imm 0)) .skip (blk [
    scaleCol 1, I (.load .rax (at_ .rsi (wdisp 0))),
    .ite (.cmp .eq .rax (.imm 1)) .skip (scaleCol 2)])

/-- The terms' loop of `F.evaluate P`: `rsi` the term, `rdx` the end, `rbp` the padding row, the sum
in `(r14, r15)`. -/
def evLoop : Stmt :=
  .loop (.cmp .ne .rsi (.reg .rdx)) (blk [
    I (.load .r9 (at_ .rsi (wdisp 3))), I (.load .r10 (at_ .rsi (wdisp 4))),
    I (.load .rax (at_ .rsi (wdisp 0))), tvCode,
    I (.xor .r14 .r9), I (.xor .r15 .r10), I (.addi .rsi 40)])

/-- The loop's start: the first term, the end, the sum `0`, the padding row. -/
def evPre : Stmt := blk [
  wk, I (.lea .rsi (aw (fOff + 1))), I (.load .rdx (aw fOff)), I (.mov .rax .rdx),
  I (.shli .rdx 5), I (.shli .rax 3), I (.add .rdx .rax), I (.add .rdx .rsi),
  I (.movi .r14 0), I (.movi .r15 0), I (.lea .rbp (aw padOff))]

/-- `sumR side += sel · pw · (r14, r15 + 1)`, the selector at `vSel`, its padding weight `102` words
on. -/
def evPost (side : Nat) : Stmt := blk [
  I (.xori .r14 1),
  wk, I (.load .rbp (aw vSel)),
  I (.load .r9 (at_ .rbp (wdisp 0))), I (.load .r10 (at_ .rbp (wdisp 1))),
  I (.load .r11 (at_ .rbp (wdisp 102))), I (.load .r12 (at_ .rbp (wdisp 103))),
  emul, I (.mov .r11 .r14), I (.mov .r12 .r15), emul,
  wk, I (.load .rax (aw (sumR side).off)), I (.xor .rax .r9), I (.store (aw (sumR side).off) .rax),
  I (.load .rax (aw ((sumR side).off + 1))), I (.xor .rax .r10),
  I (.store (aw ((sumR side).off + 1)) .rax)]

/-- **The padding rows' term**: `sumR side += sel · pw · (F.evaluate P + 1)`. -/
def evalCode (side : Nat) : Stmt := blk [evPre, evLoop, evPost side]

/-- The terms' loop of `G.addScaled F sel`: `r14` the term, `r15` the end, `r13` the owner's form,
`rbp` the selector. -/
def acLoop : Stmt :=
  .loop (.cmp .ne .r14 (.reg .r15)) (blk [
    I (.load .r9 (at_ .rbp (wdisp 0))), I (.load .r10 (at_ .rbp (wdisp 1))),
    I (.load .r11 (at_ .r14 (wdisp 3))), I (.load .r12 (at_ .r14 (wdisp 4))),
    emul, I (.mov .r12 .r14), atCode, I (.addi .r14 40)])

/-- The loop's start: the owner's form, the selector, the first term, the end. -/
def accPre : Stmt := blk [
  wk, I (.load .r13 (aw vG)), I (.load .rbp (aw vSel)),
  I (.lea .r14 (aw (fOff + 1))), I (.load .r15 (aw fOff)), I (.mov .rax .r15),
  I (.shli .r15 5), I (.shli .rax 3), I (.add .r15 .rax), I (.add .r15 .r14)]

/-- The next selector, one block fewer (left in `rax`). -/
def accPost : Stmt := blk [
  wk, I (.load .rax (aw vSel)), I (.addi .rax 16), I (.store (aw vSel) .rax),
  I (.load .rax (aw vRem)), I (.subi .rax 1), I (.store (aw vRem) .rax)]

/-- **The owner's form**: `G := G.addScaled F sel`; the next selector, one block fewer. -/
def accCode : Stmt := blk [accPre, acLoop, accPost]

/-- One block. -/
def blockCode (side wOff bOff : Nat) : Stmt :=
  blk [buildCode wOff bOff, evalCode side, accCode]

/-- `rcx` words from `rax` zeroed. -/
def zeroLoop : Stmt :=
  .loop (.cmp .ne .rcx (.imm 0)) (blk [
    I (.storei (at_ .rax (wdisp 0)) 0), I (.addi .rax 8), I (.subi .rcx 1)])

/-- **The padding row**: `124` words zeroed, `Keccak.permute` on the `84` from word `40`, the words
from `65` zeroed again. -/
def padCode : Stmt := blk [
  wk, I (.lea .rax (aw padOff)), I (.movi .rcx 124), zeroLoop,
  I (.mov .r15 .rdi), I (.lea .rdi (aw (padOff + 40))), Keccak.permute, I (.mov .rdi .r15),
  wk, I (.lea .rax (aw (padOff + 65))), I (.movi .rcx 59), zeroLoop]

/-- **The data** to `dOff`. -/
def dataCode (side : Nat) (D : List DBlk) : Stmt := blk (wk :: storeL dOff (encode side D))

/-- The sum, the count side's weight and `β`, the loop's state. -/
def initCode (side : Nat) (D : List DBlk) : Stmt := blk [
  wk,
  I (.storei (aw (sumR side).off) 0), I (.storei (aw ((sumR side).off + 1)) 0),
  I (.storei (aw wvOff) 1), I (.storei (aw (wvOff + 1)) 0),
  I (.storei (aw bvOff) 0), I (.storei (aw (bvOff + 1)) 0),
  I (.lea .rax (aw dOff)), I (.store (aw vCur) .rax),
  I (.lea .rax (aw (tselR side).off)), I (.store (aw vSel) .rax),
  I (.storei (aw vRem) (Int64.ofNat D.length))]

/-- The blocks' loop. -/
def loopCode (side wOff bOff : Nat) : Stmt := blk [
  wk, I (.load .rax (aw vRem)),
  .loop (.cmp .ne .rax (.imm 0)) (blockCode side wOff bOff)]

/-- The side's slot weights: `wR`, the count side's `1`. -/
def wSrc (side : Nat) : Nat := if side = 2 then wvOff else wR.off

/-- The side's `β`: `betaR`, the count side's `0`. -/
def bSrc (side : Nat) : Nat := if side = 2 then bvOff else betaR.off

/-- **The forms of a side** whose blocks are the data `D`. -/
def formsWith (side : Nat) (D : List DBlk) : Stmt :=
  blk [padCode, dataCode side D, initCode side D, loopCode side (wSrc side) (bSrc side)]

end NativeVm.Code.P3
