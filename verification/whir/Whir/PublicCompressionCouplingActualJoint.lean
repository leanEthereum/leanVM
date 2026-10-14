import Whir.PublicCompressionCouplingJoint
import Whir.PublicCompressionCouplingCausalRisk
import Whir.RawOracleProvenance

/-! Explicit shared-answer coupling marginals for the actual full-public-View
real and pinned ideal games. No observer, chosen-CV, or adversary restriction is
added. Good-cache alignment is proved in `PublicCompressionCouplingSourceStream`. -/
namespace Whir.PublicCompressionCouplingActualJoint
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler (Sampling)
open RawOracleCoupling PublicCompressionCouplingJoint

private theorem average_fintype {T : Type} (old new : Fintype T) (f : T → ℚ) :
    @average T old f = @average T new f := by
  cases Subsingleton.elim old new
  rfl

private theorem average_product {X Y : Type} [Fintype X] [Fintype Y] (f : X × Y → ℚ) :
    average f = average (fun x => average (fun y => f (x,y))) := by
  classical
  simp only [average,Fintype.sum_prod_type,Finset.sum_div,Fintype.card_prod,Nat.cast_mul,div_div]
  rw [mul_comm]

open Classical in
noncomputable def actualJoint {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) :=
  joint (PublicCompressionProgram.compile iv p Q counted) (fun _ => none)
    (PublicCompressionCouplingMixed.causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none)

open Classical in
 theorem actual_joint_real {AdvCoins R : Type} [Fintype AdvCoins]
    (Q : Nat) (iv : Digest32) (adversary : AdvCoins → Program R)
    (counted : ∀ a, Counts Q (adversary a)) (D : View R → Bool) :
    average (fun a => Sampling.expectation
      (fun pair => if D pair.1.1.view then (1:ℚ) else 0)
      (actualJoint Q iv (adversary a) (counted a))) = realProbability iv adversary D := by
  unfold realProbability
  rw [distinguish_average (inferInstance : Fintype (PrimitiveOracle × AdvCoins)),
    average_product,average_comm]
  apply congrArg average
  funext a
  rw [actualJoint,joint_first (PublicCompressionProgram.compile iv (adversary a) Q (counted a))
    (fun _ => none) (PublicCompressionCouplingMixed.causalCompile Q iv [] (adversary a)
      Q (by rfl) (counted a)) (fun _ => none)
    (fun result => if D result.1.view then (1:ℚ) else 0),
    ← empty_table_eq_memo (PublicCompressionProgram.compile iv (adversary a) Q (counted a))
      (fun result => if D result.view then (1:ℚ) else 0)]
  let canonical : Fintype PrimitiveOracle := inferInstance
  conv_lhs => rw [average_fintype _ canonical]
  conv_rhs => rw [average_fintype _ canonical]
  apply congrArg (@average PrimitiveOracle canonical)
  funext C
  simp only [PublicCompressionProgram.compile_eval]

open Classical in
 theorem actual_joint_ideal {AdvCoins R : Type} [Fintype AdvCoins]
    (Q : Nat) (iv : Digest32) (adversary : AdvCoins → Program R)
    (counted : ∀ a, Counts Q (adversary a)) (D : View R → Bool) :
    letI := DuplexPublicSimulator.seedFintype
    average (fun a => Sampling.expectation
      (fun pair => if D pair.2.1.1 then (1:ℚ) else 0)
      (actualJoint Q iv (adversary a) (counted a))) =
      idealProbability (DuplexPublicSimulator.simulator Q) iv adversary counted D := by
  let := DuplexPublicSimulator.seedFintype
  let := rawOracleFintype Q
  let := PublicCompressionCouplingMixed.mixedKeyFintype Q
  have marginal (a : AdvCoins) :
      Sampling.expectation (fun pair => if D pair.2.1.1 then (1:ℚ) else 0)
        (actualJoint Q iv (adversary a) (counted a)) =
      average (fun table : PublicCompressionCouplingMixed.Key Q → Digest32 =>
        if D (Sampling.eval table (PublicCompressionCouplingMixed.causalCompile Q iv []
          (adversary a) Q (by rfl) (counted a))).1 then (1:ℚ) else 0) := by
    rw [actualJoint,joint_second (PublicCompressionProgram.compile iv (adversary a) Q (counted a))
      (fun _ => none) (PublicCompressionCouplingMixed.causalCompile Q iv [] (adversary a)
        Q (by rfl) (counted a)) (fun _ => none)
      (fun result => if D result.1.1 then (1:ℚ) else 0),
      ← empty_table_eq_memo (PublicCompressionCouplingMixed.causalCompile Q iv []
        (adversary a) Q (by rfl) (counted a)) (fun result => if D result.1 then (1:ℚ) else 0)]
  simp_rw [marginal]
  rw [average_comm]
  rw [← average_product
    (fun coins : (PublicCompressionCouplingMixed.Key Q → Digest32) × AdvCoins =>
      if D (Sampling.eval coins.1 (PublicCompressionCouplingMixed.causalCompile Q iv []
        (adversary coins.2) Q (by rfl) (counted coins.2))).1 then (1:ℚ) else 0)]
  let e : (PublicCompressionCouplingMixed.Key Q → Digest32) × AdvCoins ≃
      (RawKey Q → Digest32) × DuplexPublicSimulator.Seed × AdvCoins :=
    (Equiv.prodCongr ((PublicCompressionCouplingMixed.tableEquiv Q).trans
      (Equiv.prodComm DuplexPublicSimulator.Seed (RawKey Q → Digest32))) (Equiv.refl AdvCoins)).trans
      (Equiv.prodAssoc (RawKey Q → Digest32) DuplexPublicSimulator.Seed AdvCoins)
  have eq := average_equiv e
    (fun coins : (RawKey Q → Digest32) × DuplexPublicSimulator.Seed × AdvCoins =>
      if D (runIdeal (DuplexPublicSimulator.simulator Q) coins.1 iv
        ((DuplexPublicSimulator.simulator Q).initial coins.2.1) (adversary coins.2.2)
        Q (by rfl) (counted coins.2.2)).view then (1:ℚ) else 0)
  unfold idealProbability
  rw [distinguish_average (inferInstance : Fintype
    ((RawKey Q → Digest32) × DuplexPublicSimulator.Seed × AdvCoins))]
  apply Eq.trans _ eq
  apply congrArg (fun f : ((PublicCompressionCouplingMixed.Key Q → Digest32) × AdvCoins) → ℚ => average f)
  funext coins
  rcases coins with ⟨table,a⟩
  have image : e (table,a) = ((fun key => table (.inr key)),(fun n => table (.inl n)),a) := rfl
  rw [image]
  have oracleEq : PublicCompressionCouplingMixed.oracle
      (fun n => table (.inl n)) (fun key => table (.inr key)) = table := by
    funext key
    cases key <;> rfl
  have viewEq := PublicCompressionCouplingMixed.causalCompile_public Q iv (adversary a)
    (counted a) (fun n => table (.inl n)) (fun key => table (.inr key))
  rw [oracleEq] at viewEq
  exact congrArg (fun view => if D view then (1:ℚ) else 0) viewEq

#print axioms actual_joint_real
#print axioms actual_joint_ideal
end Whir.PublicCompressionCouplingActualJoint
