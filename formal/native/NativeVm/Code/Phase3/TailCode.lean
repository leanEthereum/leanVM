module

public import NativeVm.Code.Phase3.Claims
public import NativeVm.Code.Phase3.BusInit
public import NativeVm.Code.Phase3.Totals
public import NativeVm.Code.Phase3.Forms
public import NativeVm.Code.Phase3.SelSpec

/-!
# Phase 3's code after the transcript

What `verifyBusBalance` computes once the transcript is read: the two point lengths (`lensCode`),
the constants (`constOps`), `indexMle` of the memory's and the bytecode's prefixes of the GKR point
(`imleAt`), `g^(2^logBytecode − 1)` (`pcCode`), the push and pull sides' fingerprints (`fpOps`), the
column claims (`claimsCode`), the empty forms (`formsInit`), each side's selectors, forms and total
(`selCode`, `formsCode`, `totalCode`), the point and the totals into `busR` (`busTail`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

/-- The working area's address into `r14`. -/
def ldWork : Stmt := I (.load .r14 (cw ctxWork))

/-- `indexMle` of the first `lenW i` coordinates of the GKR point into `dst`. -/
def imleAt (i dst : Nat) : Stmt := blk [
  ldWork, I (.load .r15 (at_ .r14 (wdisp (lenW i)))), I (.mov .r13 .r14),
  I (.addi .r13 (wdisp pointR.off)), imleCode dst]

/-- A side's selectors, forms and total. -/
def sideCode (side : Nat) : Stmt := blk [selCode side, formsCode side, totalCode side]

/-- **The values, the claims, the forms and the totals.** -/
def tailCode : Stmt := blk [
  lensCode, ldWork, opsCode constOps, imleAt 0 sIm, imleAt 1 sIb, ldWork, pcCode,
  ldWork, opsCode (fpOps sOne sOne sOne fpPush), ldWork, opsCode (fpOps sPc 52844 52846 fpPull),
  claimsCode, formsInit, sideCode 0, sideCode 1, sideCode 2, busTail]

end NativeVm.Code.P3
