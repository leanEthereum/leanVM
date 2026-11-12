import LeanVM.Cost.Extractor.PMFFT
import LeanVMTests.Runs

/-!
# Tests: the additive-FFT product's transform branch, compiled

`mulViaFFT` (`Cost/Extractor/PMFFT.lean`) on the cost machine at its transform branch's least size
(a factor above the schedule's `4096`, the other above `32`, `2^13` points) is the product: a
module of its own, apart from `PMChain.lean`, the slowest of its runs; compiled (`lake exe test-runs`).
-/

namespace LeanVMTests.Cost.PMChainFFT

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Parameters CompPoly MachineEncoding

def rnd (s : ℕ) : K := K.ofBits ((s * 2654435761 + 12345) % 4294967291)

/-- A pseudo-random polynomial of `d` coefficients (`PMChain.poly`). -/
def poly (s d : ℕ) : CPolynomial K := CPolynomial.ofArray (Array.ofFn fun j : Fin d ↦ rnd (s * 1000 + j.val))

test_runs runs := [
  ("mulViaFFTC's transform branch is the product", fun _ ↦
    (evaluateFunctionBody (MachineProgram.ofList mulViaFFTC.costDeps) 1000000000 mulViaFFTC.costIdx
        [encodeValue (poly 1 4097), encodeValue (poly 2 33)]).map (·.1) ==
      some (encodeValue (poly 1 4097 * poly 2 33)))]

end LeanVMTests.Cost.PMChainFFT
