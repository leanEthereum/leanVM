module

public import NativeVm.Transcript.Layout
public import NativeVm.Model.Verify
public import NativeVm.Wire.Layout

/-!
# The caller's working-area size
-/

@[expose] public section

namespace NativeVm.Entry

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

def vecWords (cap : Nat) : Nat := 1 + 2 * cap

def wvecWords (cap : Nat) : Nat := 1 + cap

def stackCap : Nat := Whir.maxLogStack

def tablePointCap : Nat := 30

def pointCap : Nat := tablePointCap + qkeccakSlotBits

def busPointCap : Nat := 63

def widthCap : Nat := 92

def formCap : Nat := 148

def monoCap : Nat := 2

def busClaimCount : Nat := 4

def tableClaimCount : Nat := tableWidths.sum

def publicClaimCount : Nat := 2

def keccakClaimCount : Nat := 1

def claimCap : Nat := busClaimCount + tableClaimCount + publicClaimCount + keccakClaimCount

def stackClaimCap : Nat := claimCap + 2

def ringCoeffCount : Nat := ringMapWidth * ringMapWidth

def queryCap : Nat := 230

def levelCap : Nat := 6

def gluedCap : Nat := 2 * (levelCap - 1)

def roundCap : Nat := Whir.initialFold

def rowsWords : Nat := LeanVM.Protocol.Compile.wireMaxQueries * LeanVM.Protocol.Compile.wireMaxLeafWords

def scratchWords : Nat := 32768

def layoutWords : Nat := 4 + 2 * 6 + 3 * columnCount

def eqClaimWords : Nat := vecWords stackCap + 2

def claimWords : Nat := 1 + vecWords pointCap + 2

def claimsWords : Nat := 1 + claimWords * claimCap

def termWords : Nat := 1 + monoCap + 2

def formWords : Nat := 1 + termWords * formCap

def busPointOff : Nat := formWords * (3 * nTables)

def busTotalsOff : Nat := busPointOff + vecWords busPointCap

def busWords : Nat := busTotalsOff + 2 * nTrees

def evalStride : Nat := vecWords tablePointCap + vecWords widthCap

def evalsWords : Nat := evalStride * nTables

def keccakWords : Nat := vecWords pointCap + 2 * kBits

def ringWords : Nat := 2 + 2 * ringCoeffCount

def basisWords : Nat := vecWords stackClaimCap

def gluedQOff : Nat := 5 + vecWords stackCap

def gluedWOff : Nat := gluedQOff + wvecWords queryCap

def gluedWords : Nat := gluedWOff + vecWords queryCap

def whirGluedOff : Nat := 2 + vecWords stackCap

def whirWords : Nat := whirGluedOff + 1 + gluedWords * gluedCap

def roundsWords : Nat := 1 + 4 * roundCap

structure Region where
  off : Nat
  size : Nat
  deriving DecidableEq, Repr

def Region.stop (r : Region) : Nat := r.off + r.size

def Region.next (r : Region) (size : Nat) : Region := ⟨r.stop, size⟩

def layoutR : Region := ⟨Transcript.workWords, layoutWords⟩

def oodR : Region := layoutR.next eqClaimWords

def busR : Region := oodR.next busWords

def evalsR : Region := busR.next evalsWords

def claimsR : Region := evalsR.next claimsWords

def keccakR : Region := claimsR.next keccakWords

def ringR : Region := keccakR.next ringWords

def basisR : Region := ringR.next basisWords

def whirR : Region := basisR.next whirWords

def roundsR : Region := whirR.next roundsWords

def queriesR : Region := roundsR.next (wvecWords queryCap)

def rowsR : Region := queriesR.next rowsWords

def scratchR : Region := rowsR.next scratchWords

def dataEnd : Nat := scratchR.stop

def workWords (n : Nat) : Nat := max (max Wire.workWords (n + 2)) dataEnd

theorem dataEnd_val : dataEnd = 85438 := by decide

end NativeVm.Entry
