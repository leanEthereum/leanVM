import Whir.ShoupTraceExtraction
import Whir.ConcreteRowExtraction
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Executable
import ArkLib.Data.CodingTheory.GuruswamiSudan.Correctness

/-! Executable list decoding on the actual WHIR base-domain nodes. This adapter supplies a real non-enumerating E root provider, dense interpolation and Roth–Ruckenstein, followed by guarded novel-basis base-word projection. Radius and integer interpolation-capacity hypotheses are explicit. They are not replaced by PCS soundness, and verifier acceptance alone is not asserted to imply them. -/
namespace Whir.PCSListExtraction
open Concrete CompPoly
local instance : Field E := ExtractionField.field

/-- The complete root backend is instantiated, rather than supplied as an unimplemented oracle. -/
def context : CompPoly.GuruswamiSudan.GSFilteredCoreContext E :=
  CompPoly.GuruswamiSudan.filteredCoreContextOfInterpRootContexts
    (CompPoly.GuruswamiSudan.denseInterpContext E)
    (CompPoly.GuruswamiSudan.rothRuckensteinRootContext E
      (ShoupTraceExtraction.fieldRootContext CPolynomial.Raw.MulContext.naive
        CPolynomial.Raw.ModContext.naive))

/-- Only N explicitly provided received values are read. No public root preimage is consulted. -/
def receivedWord (depth : Nat) (received : Fin (2 ^ depth) → E) :
    CompPoly.GuruswamiSudan.GSReceivedWord E where
  points := Array.ofFn fun i => (E.ofK (UInt64.ofNat i.val), received i)

/-- The caller's finite integer parameters are computational inputs; certificates are erased proofs. -/
def listPolynomials (depth : Nat) (params : CompPoly.GuruswamiSudan.GSExecParams)
    (received : Fin (2 ^ depth) → E) : Array (CPolynomial E) :=
  CompPoly.GuruswamiSudan.decodeWithParams context params (receivedWord depth received)

def listWords (n rate : Nat) (params : CompPoly.GuruswamiSudan.GSExecParams)
    (received : Fin (2 ^ (n + rate)) → E) : Array (Array K) :=
  (listPolynomials (n + rate) params received).filterMap (ConcreteRowExtraction.baseWords n)

theorem listPolynomials_complete (n rate : Nat) (noWrap : n + rate ≤ 64)
    (params : CompPoly.GuruswamiSudan.GSExecParams) (errors : Nat)
    (certificate : _root_.GuruswamiSudan.GSParamCert (2 ^ n) (2 ^ (n + rate)) errors params)
    (received : Fin (2 ^ (n + rate)) → E) (polynomial : Polynomial E)
    (degree : polynomial.degree < (2 ^ n : Nat))
    (distance : hammingDist received
      (fun i => polynomial.eval (E.ofK (UInt64.ofNat i.val))) ≤ errors) :
    ∃ candidate ∈ (listPolynomials (n + rate) params received).toList,
      candidate.toPoly = polynomial := by
  exact (_root_.GuruswamiSudan.mem_decodeWithParams_iff_degree_and_distance
    context params certificate
    (ωs := AdditiveCode.concreteDomain (n + rate) noWrap)
    (w := receivedWord (n + rate) received) (by rfl)).mpr ⟨degree, distance⟩

theorem listWords_complete (n rate : Nat) (noWrap : n + rate ≤ 64)
    (params : CompPoly.GuruswamiSudan.GSExecParams) (errors : Nat)
    (certificate : _root_.GuruswamiSudan.GSParamCert (2 ^ n) (2 ^ (n + rate)) errors params)
    (received : Fin (2 ^ (n + rate)) → E) (words : Array K)
    (shape : words.size = 2 ^ n)
    (distance : hammingDist received
      (fun i => (AdditiveCode.concretePolynomial n (words.map E.ofK)).eval
        (E.ofK (UInt64.ofNat i.val))) ≤ errors) :
    words ∈ (listWords n rate params received).toList := by
  have small : n ≤ 64 := by omega
  obtain ⟨candidate, member, polynomial⟩ := listPolynomials_complete n rate noWrap params errors
    certificate received (AdditiveCode.concretePolynomial n (words.map E.ofK))
    (AdditiveCode.concrete_polynomial_degree_lt n small _) distance
  have projected := ConcreteRowExtraction.baseWords_recovers n small words shape candidate polynomial
  simp only [listWords, Array.toList_filterMap, List.mem_filterMap]
  exact ⟨candidate, member, projected⟩

#print axioms context
#print axioms listPolynomials_complete
#print axioms listWords_complete
end Whir.PCSListExtraction
