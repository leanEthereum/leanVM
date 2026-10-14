import Whir.TraceBasisExtraction
import Whir.FrobeniusExtraction
import CompPoly.Univariate.Roots.Shoup.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField

/-! Source-extension root extraction without field enumeration. Scalar Frobenius powers are obtained from the bounded squaring ladder, not the canonical scalar natural-power recursion. The executable wrapper is proved equal to the certified Shoup algorithm; the global source field dictionaries are unchanged. These are root-backend correctness results, not a full PCS knowledge theorem or a full coefficient-operation bound. -/
namespace Whir.ShoupTraceExtraction
open Concrete CompPoly CompPoly.CPolynomial.Roots.FiniteField TraceExtraction TraceBasisExtraction
set_option maxRecDepth 8192
local instance : Field E := ExtractionField.field

abbrev MulBackend := CPolynomial.Raw.MulContext E
abbrev ModBackend := CPolynomial.Raw.ModContext E

/-- Scalar Frobenius powers are shared: 191 squarings for the entire trace coordinate. Modular polynomial powers use the certified bounded modular-power implementation. -/
def traceCoordinate (M : MulBackend) (D : ModBackend) (modulus : CPolynomial E) (beta : E) :
    CPolynomial E :=
  let scalars := FrobeniusExtraction.powers 192 beta
  (List.range 192).foldl (fun total i => total +
    CPolynomial.C scalars[i]! * xPowModWith M D modulus (2 ^ i)) 0

theorem traceCoordinate_eq (M : MulBackend) (D : ModBackend) (modulus : CPolynomial E) (beta : E) :
    traceCoordinate M D modulus beta = traceCoordinatePolynomialWith M D traceContext modulus beta := by
  simp only [traceCoordinate, traceCoordinatePolynomialWith, traceContext,
    FrobeniusExtraction.powers_value]
  apply List.foldl_ext
  intro total i member
  have bound : i < 192 := List.mem_range.mp member
  simp [getElem!_pos, bound]

/-- The source-specialized refinement is deliberately direct: only the expensive scalar-power call is replaced, and the certified polynomial backend remains unchanged. -/
def refineFactor (M : MulBackend) (D : ModBackend) (beta : E) (factor : CPolynomial E) :
    Array (CPolynomial E) :=
  let factor := CPolynomial.monicNormalize factor
  if factor == 0 || factor == 1 then #[]
  else if isRepresentedLinearFactor factor then #[factor]
  else
    let tracePoly := traceCoordinate M D factor beta
    traceContext.baseConstants.foldl (fun children constant =>
      let child := CPolynomial.monicNormalize
        (CPolynomial.gcdMonic factor (tracePoly - CPolynomial.C constant))
      pushNontrivialChild children child) #[]

theorem refineFactor_eq (M : MulBackend) (D : ModBackend) (beta : E) (factor : CPolynomial E) :
    refineFactor M D beta factor = shoupRefineFactorWith M D traceContext beta factor := by
  simp only [refineFactor, shoupRefineFactorWith, traceCoordinate_eq]

def refineFactors (M : MulBackend) (D : ModBackend) (beta : E) (factors : Array (CPolynomial E)) :
    Array (CPolynomial E) :=
  factors.foldl (fun out factor => out ++ refineFactor M D beta factor) #[]

theorem refineFactors_eq (M : MulBackend) (D : ModBackend) (beta : E) (factors : Array (CPolynomial E)) :
    refineFactors M D beta factors = shoupRefineFactorsWith M D traceContext beta factors := by
  simp only [refineFactors, shoupRefineFactorsWith, refineFactor_eq]

def splitCandidates (M : MulBackend) (D : ModBackend) (polynomial : CPolynomial E) :
    Array (CPolynomial E) :=
  let polynomial := CPolynomial.monicNormalize polynomial
  if polynomial == 0 || polynomial == 1 then #[]
  else if isRepresentedLinearFactor polynomial then #[polynomial]
  else traceContext.basis.foldl (fun factors beta => refineFactors M D beta factors) #[polynomial]

theorem splitCandidates_eq (M : MulBackend) (D : ModBackend) (polynomial : CPolynomial E) :
    splitCandidates M D polynomial = shoupSplitCandidatesWith M D traceContext polynomial := by
  simp only [splitCandidates, shoupSplitCandidatesWith, refineFactors_eq]

def splitter (M : MulBackend) (D : ModBackend) : LinearFactorProductSplitter E where
  splitLinearFactors _ polynomial := representedLinearFactorsOnly (splitCandidates M D polynomial)
  validInput _ polynomial := shoupSplitterInput traceContext polynomial
  sound := by
    intro q polynomial factor member
    rw [splitCandidates_eq] at member
    exact shoupSplitLinearFactorsWith_sound M D traceContext member
  complete := by
    intro q polynomial root valid nonzero isRoot
    simpa only [splitCandidates_eq, shoupSplitLinearFactorsWith] using
      shoupSplitLinearFactorsWith_complete M D traceContext valid nonzero isRoot

/-- Establish validity with the field-size parameter opaque; this avoids normalizing the dense specification X^(2^192) during source-instance elaboration. The runtime still computes only modular powers. -/
private def rootContextFromShoup {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmallPrimeTraceContext F) : GuruswamiSudan.FieldRootContext F :=
  GuruswamiSudan.finiteFieldRootContextWith F M D ctx.toFiniteFieldContext
    (shoupLinearFactorProductSplitterWith M D ctx) (by
      intro polynomial nonzero
      exact ⟨finiteFieldRootProductWith_ne_zero_of_ne_zero M D ctx.toFiniteFieldContext nonzero,
        finiteFieldRootProductWith_dvd_frobenius M D ctx nonzero⟩)

theorem roots_eq (M : MulBackend) (D : ModBackend) (polynomial : CPolynomial E) :
    rootsInFiniteFieldWith M D traceContext.toFiniteFieldContext (splitter M D) polynomial =
      (rootContextFromShoup M D traceContext).rootsInField polynomial := by
  simp only [rootContextFromShoup, GuruswamiSudan.finiteFieldRootContextWith,
    rootsInFiniteFieldWith, splitter, shoupLinearFactorProductSplitterWith,
    splitCandidates_eq, shoupSplitLinearFactorsWith]

/-- A real complete univariate root provider for source E, using the certified root-product reduction and source binary trace splitter. -/
def fieldRootContext (M : MulBackend) (D : ModBackend) :
    GuruswamiSudan.FieldRootContext E where
  rootsInField := rootsInFiniteFieldWith M D traceContext.toFiniteFieldContext (splitter M D)
  sound := by
    intro polynomial root member
    rw [roots_eq] at member
    exact (rootContextFromShoup M D traceContext).sound polynomial root member
  complete := by
    intro polynomial root nonzero isRoot
    rw [roots_eq]
    exact (rootContextFromShoup M D traceContext).complete polynomial root nonzero isRoot
 
#print axioms roots_eq

#print axioms traceCoordinate_eq
#print axioms refineFactor_eq
#print axioms refineFactors_eq
#print axioms splitCandidates_eq
#print axioms splitter
#print axioms fieldRootContext
end Whir.ShoupTraceExtraction
