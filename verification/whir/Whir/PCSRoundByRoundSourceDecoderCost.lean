import Whir.PCSRoundByRoundSourceDecoder

/-! Value-connected full-root field/resource accounting. Field operations use
actual Gao and dense encoder counters and the actual original-check counters.
The additional charge is a conservative reservation for physical root scanning,
lane-vector construction, common-coordinate comparisons, and witness assembly.
It does not charge a quadratic record lookup: no such operation exists here. -/
namespace Whir.PCSRoundByRoundSource
open Concrete Protocol CausalGame KnowledgeExtraction SupportedCandidateExtraction
set_option maxHeartbeats 4000000
attribute [local irreducible] ParameterBounds.config

/-- Word slots, reads, comparisons and loop visits outside the counted algebra
backends. A charge is reserved even when a guard short-circuits. -/
def rootTableCharge (c : Config) (lanes : Nat) : Nat :=
  16 * (blockLength c + 1) * (laneCount c + 1) +
  16 * (lanes + 1) * (blockLength c + width c + 1)

/-- The instrumented counterpart runs each backend only once. Its first
projection is exactly `run`, including every malformed/original/support guard. -/
def countedRun {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle) :
    Option (Witness (ParameterBounds.config profile) lanes) × Nat :=
  let c := ParameterBounds.config profile
  if m ≤ 2^64 ∧ points.size ≤ 2^64 ∧ FullRoot c lanes root then
    let prep := OriginalClaimsChecker.countedPrepare c lanes family points anchorPoint anchorValue
    match prep.1 with
    | none => (none, prep.2.total + rootTableCharge c lanes)
    | some prepared =>
      let input : Public := ⟨c, lanes, root, #[]⟩
      let decoded := decodeRoot input (InitialCandidates.production_initial_facts profile).2.2.1
      match decoded.1 with
      | none => (none, prep.2.total + decoded.2 + rootTableCharge c lanes)
      | some w =>
        let support := countedSupport input w
        let checked := OriginalClaimsChecker.countedCheck prepared w
        (if ParameterBounds.threshold c 0 ≤ support.1 ∧ checked.1 = true then some w else none,
          prep.2.total + decoded.2 + support.2 + checked.2.total + rootTableCharge c lanes)
  else (none, 16)

 theorem countedRun_value {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle) :
    (countedRun profile lanes family points anchorPoint anchorValue root).1 =
      run profile lanes family points anchorPoint anchorValue root := by
  unfold countedRun run runForConfig
  dsimp only
  split
  · rw [OriginalClaimsChecker.countedPrepare_value]
    cases hp : OriginalClaimsChecker.prepare (ParameterBounds.config profile) lanes family points anchorPoint anchorValue
    · simp
    · simp only [Option.bind_some]
      split <;> simp_all only [Option.bind_none, Option.bind_some,
        OriginalClaimsChecker.countedCheck_value]
  · rfl

/-- Explicit polynomial in block length, full lane count, occupied lane count,
original families and points. The Gao term is degree seven. -/
def resourcePolynomial (nodes fullLanes lanes families points : Nat) : Nat :=
  lanes * ConcreteRowExtraction.rowArithmeticPolynomial nodes +
  fullLanes * nodes * (16576 + 5 * nodes) +
  OriginalClaimsChecker.preparationPolynomial (fullLanes * nodes) families points +
  OriginalClaimsChecker.checkPolynomial (fullLanes * nodes) families points +
  16 * (nodes + 1) * (fullLanes + 1) + 16 * (lanes + 1) * (2 * nodes + 1) + 16

 theorem countedRun_polynomial_cost {m : Nat} (profile : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E) (root : BaseOracle) :
    (countedRun profile lanes family points anchorPoint anchorValue root).2 ≤
      resourcePolynomial (blockLength (ParameterBounds.config profile))
        (laneCount (ParameterBounds.config profile)) lanes m points.size := by
  let c := ParameterBounds.config profile
  have noWrap := (InitialCandidates.production_initial_facts profile).2.2.1
  have redundancy := (PCSRewindExtractor.production_heavy_static profile).2.1
  have widthBound : width c ≤ blockLength c := redundancy.le
  have cube : 2^c.logN ≤ laneCount c * blockLength c := by
    have exactCube : 2^c.logN = laneCount c * width c := by
      unfold laneCount width
      rw [← Nat.pow_add, Nat.add_sub_of_le (InitialCandidates.production_initial_facts profile).2.1]
    rw [exactCube]
    exact Nat.mul_le_mul_left _ widthBound
  have prep := OriginalClaimsChecker.countedPrepare_total c lanes family points anchorPoint anchorValue
  have prepBound : (OriginalClaimsChecker.countedPrepare c lanes family points anchorPoint anchorValue).2.total ≤
      OriginalClaimsChecker.preparationPolynomial (laneCount c * blockLength c) m points.size := by
    apply prep.trans
    unfold OriginalClaimsChecker.preparationPolynomial
    gcongr
  have tableBound : rootTableCharge c lanes ≤
      16 * (blockLength c + 1) * (laneCount c + 1) + 16 * (lanes + 1) * (2 * blockLength c + 1) := by
    unfold rootTableCharge
    gcongr
    omega
  have encodeBound : CountedCandidateCheck.encoderBound c ≤
      laneCount c * blockLength c * (16576 + 5 * blockLength c) := by
    simpa [CountedCandidateCheck.checkerBound, CountedCandidateCheck.checkerPolynomial] using
      CountedCandidateCheck.checkerBound_polynomial (⟨c, lanes, #[], #[]⟩ : Public) noWrap
  unfold countedRun
  dsimp only
  split
  · split
    · dsimp only
      unfold resourcePolynomial
      change _ ≤ lanes * _ + _ + _ + _ + _ + _ + 16
      dsimp only [c] at prepBound tableBound
      omega
    · rename_i prepared hp
      have decodeBound := decodeRoot_cost (⟨c, lanes, root, #[]⟩ : Public) noWrap redundancy
      split
      · dsimp only
        unfold resourcePolynomial
        dsimp only [c] at prepBound tableBound decodeBound
        omega
      · rename_i w hw
        have supportBound : (countedSupport ⟨c, lanes, root, #[]⟩ w).2 ≤
            laneCount c * blockLength c * (16576 + 5 * blockLength c) :=
          (CountedCandidateCheck.countedEncodedLanes_cost c _).trans encodeBound
        have checkBound := OriginalClaimsChecker.countedCheck_total prepared w
        have checkBound' : (OriginalClaimsChecker.countedCheck prepared w).2.total ≤
            OriginalClaimsChecker.checkPolynomial (laneCount c * blockLength c) m points.size :=
          checkBound.trans (by unfold OriginalClaimsChecker.checkPolynomial; gcongr)
        dsimp only
        unfold resourcePolynomial
        dsimp only [c] at prepBound tableBound decodeBound supportBound checkBound'
        omega
  · dsimp only
    unfold resourcePolynomial
    omega

#print axioms decodeRoot_cost
#print axioms countedRun_value
#print axioms countedRun_polynomial_cost
end Whir.PCSRoundByRoundSource
