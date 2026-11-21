module

public import Quantum.StdModel.Qrom.Tcr
public import Quantum.StdModel.Xmss.Costs
public import Quantum.StdModel.Xmss.PropsIn

@[expose] public section

/-!
# The leanXMSS SM-TCR-C instance of the QROM bound

The obligations of `Quantum.StdModel.Qrom.Tcr` at leanXMSS's restricted SM-TCR-C game
`smTcrIn romWorld xmssTcrC xmssTcrD TcrInKind` played by B4 (`tcrRed`):

* `xmss_gSep`: an input of `xmssTcrC` with the bytes of an in-kind input has its parameter and
  tweak (`xmssTcrC_param_tweak_eq`);
* `card_truncateHash_fiber_le`: `2^128` digests per truncation;
* `chalFirst_tcrPre`: B4's setup makes no hash call of its own, so every challenger query comes
  before one (`cost_tcrPre`);
* `cost_tcrSigner_chalW`, `cost_tcrPost_chalW`: B4's handler and output make no challenger
  query.
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common
open Quantum.StdModel.Qrom.Tcr (GSep chalW chalCan chalCost ChalFirst)

-- A bound on a whole tree is otherwise unfolded by `whnf`.
attribute [local irreducible] QueryCostAtMost Gen.treeNode grind preTrees sequenceFin walkChain
  foldPath

/-! ## Layout obligations -/

theorem xmss_gSep : GSep xmssTcrC TcrInKind :=
  fun _ P _ m _ _ _ _ hG h ↦ xmssTcrC_param_tweak_eq hG P m h

theorem card_bitVec_eq (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- **`2^128` digests per truncation**: a digest is its truncation and its upper half. -/
theorem card_truncateHash_fiber_le (o : Digest) :
    (Finset.univ.filter fun y : HashOutput ↦ xmssTcrC.trunc y = o).card ≤ 2 ^ 128 := by
  classical
  refine (Finset.card_le_card (t := Finset.univ.image (hashJoin o)) fun y hy ↦ ?_).trans
    (Finset.card_image_le.trans ?_)
  · have hy : truncateHash y = o := (Finset.mem_filter.1 hy).2
    exact Finset.mem_image.2 ⟨upperHalfOfHash y, Finset.mem_univ _, by
      rw [← hy]
      exact hashJoin_halves y⟩
  · rw [Finset.card_univ, card_bitVec_eq]
    rfl

/-! ## Challenger queries -/

section Chal

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}

/-- Every computation has weight `0` under the zero weight. -/
theorem cost_zero {α : Type} (oa : OracleComp spec α) :
    QueryCostAtMost oa (fun _ ↦ 0) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isWeightBound_pure _ _ _
  | query_bind t k ih => exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨le_rfl, ih⟩

end Chal

/-- A program of the world, as a program of B4, makes no challenger query. -/
theorem cost_tcrLift_chalW {α : Type} (oa : OracleComp romWorld.Oracles α) :
    QueryCostAtMost (tcrLift romWorld oa) (chalW (Q' := TcrQ)) 0 :=
  isWeightBound_simulateQ _ (fun _ ↦ 0) chalW
    (fun t ↦ isWeightBound_query (chalW (Q' := TcrQ)) (.inl t)) (cost_zero oa)

theorem kindBound_tcrHash_chalW :
    KindBound (tcrHash romWorld) (chalW (Q' := TcrQ)) zeroKinds :=
  ⟨fun _ _ _ _ _ _ ↦ cost_tcrLift_chalW _, fun _ _ _ _ ↦ cost_tcrLift_chalW _,
    fun _ _ _ _ _ ↦ cost_tcrLift_chalW _, fun _ _ _ _ _ ↦ cost_tcrLift_chalW _⟩

theorem opsBound_signOps_chalW (d : TcrData) :
    OpsBound (signOps romWorld d) (chalW (Q' := TcrQ)) (sKinds zeroKinds) where
  chain l e i μ hμ := (cost_chainWalk kindBound_tcrHash_chalW d.P l e i 0 μ _).mono
    (Nat.mul_le_mul_right _ hμ)
  leaf _ _ _ := isWeightBound_pure _ _ _
  node _ _ _ _ _ := isWeightBound_pure _ _ _
  encode e M := cost_grind kindBound_tcrHash_chalW d.P _ e M _ _ _

/-- **B4's handler makes no challenger query.** -/
theorem cost_tcrSigner_chalW (s : TcrSt) (r : SigningRequest) :
    QueryCostAtMost (tcrSigner romWorld s r) (chalW (Q' := TcrQ)) 0 := by
  unfold tcrSigner
  exact (cost_bind_pure (cost_sign (opsBound_signOps_chalW s.1) _ _)).mono (by decide)

/-- **B4's output makes no challenger query.** -/
theorem cost_tcrPost_chalW (d : TcrData) (F : Forgery) (s : TcrSt) :
    QueryCostAtMost (tcrPost romWorld d F s) (chalW (Q' := TcrQ)) 0 := by
  unfold tcrPost
  exact ((cost_map_iff _ _ _ _).mpr (cost_postCands kindBound_tcrHash_chalW
    (fun _ _ _ _ ↦ (cost_tcrLift_chalW (romWorld.hash _)).mono (Nat.zero_le _)) d.P F)).mono
      (by decide)

/-- A reduction's program with no hash call of its own makes every challenger query first. -/
theorem chalFirst_of_cost {Q' : Type} {R' : OracleSpec.{0, 0} Q'} {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) (h : QueryCostAtMost oa (sumCost romWorld.cost) 0) :
    ChalFirst oa := by
  unfold ChalFirst
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    refine (isQueryBound_query_bind_iff _ _ _ _ _).mpr ?_
    rcases t with (n | x) | q
    · exact ⟨trivial, fun u ↦ ih u (h.2 u)⟩
    · exact absurd h.1 (by simp [sumCost, romWorld, Qrom.hashCallCost])
    · exact ⟨rfl, fun u ↦ ih u (h.2 u)⟩

/-- **B4's setup makes every challenger query first**: it hashes nothing itself. -/
theorem chalFirst_tcrPre : ChalFirst (tcrPre romWorld) :=
  chalFirst_of_cost _ (cost_tcrPre (w := romWorld.cost) romWorld_coinsFree)

end Quantum.StdModel.Xmss

end
