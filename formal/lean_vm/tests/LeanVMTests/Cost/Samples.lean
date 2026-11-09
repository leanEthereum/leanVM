import LeanVMTests.Cost.Samples.AddRaw
import LeanVMTests.Cost.Samples.CommittedLeaves
import LeanVM.Cost.Extractor.Roots

/-!
# Tests: the compiled samples run

The program of the samples' bodies (at the indices the compiler gave them) computes the samples'
values.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Cost.Library LeanVMTests.Cost.Samples LeanVM.Parameters

def polyA : CompPoly.CPolynomial.Raw K := #[K.ofBits 3, K.ofBits 5, K.ofBits 7]
def polyB : CompPoly.CPolynomial.Raw K := #[K.ofBits 1, K.ofBits 6]

#guard (evaluateFunctionBody (MachineProgram.ofList addRawK.costDeps) 100 addRawK.costIdx
    [MachineEncoding.encodeValue polyA, MachineEncoding.encodeValue polyB]).map (·.1) ==
  some (MachineEncoding.encodeValue (CompPoly.CPolynomial.Raw.addRaw polyA polyB))

/-! ## The committed leaves -/

section
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
attribute [local instance] lexOrd

/-- A tree of height 1 and width 1: a root over two leaves of 8 bytes. -/
def leafL : Bytes := (List.range 8).map (·.toUInt8)
def leafR : Bytes := (List.range 8).map (· + 100 |>.toUInt8)
def digL : Digest := #v[1, 2, 3, 4]
def digR : Digest := #v[5, 6, 7, 8]
def rootD : Digest := #v[9, 9, 9, 9]
def nodeBytes : Bytes := digestBytes digL ++ digestBytes digR
def toyIndex : SortedMap (List UInt64 × ℕ) Hits :=
  preimageIndex [(leafL, digL), (leafR, digR), (nodeBytes, rootD)]

#guard committedLeavesFast toyIndex 1 1 rootD == #[bytesWords 1 leafL, bytesWords 1 leafR]
#guard (evaluateFunctionBody (MachineProgram.ofList committedLeavesC.costDeps) 1000 (committedLeavesC.costIdx)
    [MachineEncoding.encodeValue toyIndex, MachineEncoding.encodeValue (1 : ℕ), MachineEncoding.encodeValue (1 : ℕ), MachineEncoding.encodeValue rootD]).map (·.1) ==
  some (MachineEncoding.encodeValue (committedLeavesFast toyIndex 1 1 rootD))

end

end LeanVMTests.Cost
