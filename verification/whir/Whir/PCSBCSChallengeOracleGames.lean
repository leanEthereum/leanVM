import Whir.PCSBCSChallengeOraclePackets
import Whir.PCSBCSChallengeOracleCanonical

/-! Whole-public-view transport to the first-disclosure challenge experiment.
This is the actual #552 history-RO adapter. It does not assert book hash-chain
compiler equality, a concrete hash assumption, or whole-system lambda security. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle
open Concrete FiatShamirGame DuplexModeGame TypedOracleCompiler RawOracleCoupling

private theorem average_product {X Y : Type} [Fintype X] [Fintype Y] (f : X × Y → ℚ) :
    average f = average (fun x => average (fun y => f (x,y))) := by
  classical
  simp only [average,Fintype.sum_prod_type,Finset.sum_div,Fintype.card_prod,Nat.cast_mul,div_div]
  simp only [mul_comm]

open Classical in
noncomputable def atomicIdealProbability {Packet : Type} [Fintype Packet] [DecidableEq Packet]
    {Block : Packet → Type} [∀ p, Fintype (Block p)] {Q : Nat}
    (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
    {AdvCoins R : Type} [Fintype AdvCoins] (iv : Digest32)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (D : View R → Bool) : ℚ :=
  letI : DecidableEq (PublicCompressionCouplingMixed.Key Q) := Classical.decEq _
  average (fun a => Sampling.expectation (fun result => if D result.1 then (1:ℚ) else 0)
    (RawOracleCoupling.memo
      (Atomic.program part (PublicCompressionCouplingMixed.compile Q iv [] (adversary a)
        Q (by rfl) (counted a))) (fun _ => none)))

open Classical in
/-- Equality for EVERY whole-view observer, including all public Merkle and
chosen-CV observations. A uniform full packet is allocated at its first
physical or simulator query; later projections do not introduce fresh coins. -/
theorem atomic_ideal_probability_eq {Packet : Type} [Fintype Packet] [DecidableEq Packet]
    {Block : Packet → Type} [∀ p, Fintype (Block p)] {Q : Nat}
    (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
    {AdvCoins R : Type} [Fintype AdvCoins] (iv : Digest32)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (D : View R → Bool) :
    letI := DuplexPublicSimulator.seedFintype
    atomicIdealProbability part iv adversary counted D =
      idealProbability (DuplexPublicSimulator.simulator Q) iv adversary counted D := by
  let : DecidableEq (PublicCompressionCouplingMixed.Key Q) := Classical.decEq _
  let := DuplexPublicSimulator.seedFintype
  let := rawOracleFintype Q
  let := PublicCompressionCouplingMixed.mixedKeyFintype Q
  unfold atomicIdealProbability
  have marginal (a : AdvCoins) := actual_ideal_eq_atomic_packets part iv
    (adversary a) (counted a) (fun view => if D view then (1:ℚ) else 0)
  simp_rw [← marginal]
  rw [average_comm]
  rw [← average_product
    (fun coins : (PublicCompressionCouplingMixed.Key Q → Digest32) × AdvCoins =>
      if D (runIdeal (DuplexPublicSimulator.simulator Q) (fun k => coins.1 (.inr k))
        iv ⟨(fun n => coins.1 (.inl n)),[]⟩ (adversary coins.2) Q (by rfl) (counted coins.2)).view
          then (1:ℚ) else 0)]
  let e : (PublicCompressionCouplingMixed.Key Q → Digest32) × AdvCoins ≃
      (RawKey Q → Digest32) × DuplexPublicSimulator.Seed × AdvCoins :=
    (Equiv.prodCongr ((PublicCompressionCouplingMixed.tableEquiv Q).trans
      (Equiv.prodComm DuplexPublicSimulator.Seed (RawKey Q → Digest32))) (Equiv.refl AdvCoins)).trans
      (Equiv.prodAssoc (RawKey Q → Digest32) DuplexPublicSimulator.Seed AdvCoins)
  have equality := RawOracleCoupling.average_equiv e
    (fun coins : (RawKey Q → Digest32) × DuplexPublicSimulator.Seed × AdvCoins =>
      if D (runIdeal (DuplexPublicSimulator.simulator Q) coins.1 iv
        ((DuplexPublicSimulator.simulator Q).initial coins.2.1) (adversary coins.2.2)
        Q (by rfl) (counted coins.2.2)).view then (1:ℚ) else 0)
  unfold idealProbability
  rw [distinguish_average (inferInstance : Fintype
    ((RawKey Q → Digest32) × DuplexPublicSimulator.Seed × AdvCoins))]
  exact equality

open Classical in
/-- Exact aggregate-Q source-to-atomic challenge game bound. Only the proven
256-bit mode loss is used here. A separate 192-bit hash-chain collision term is
NOT silently added, since no book hash-chain/source correspondence is asserted. -/
theorem actual_source_atomic_game_bound {Packet : Type} [Fintype Packet] [DecidableEq Packet]
    {Block : Packet → Type} [∀ p, Fintype (Block p)] {Q : Nat}
    (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
    {AdvCoins R : Type} [Fintype AdvCoins] (iv : Digest32)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (D : View R → Bool) :
    |realProbability iv adversary D - atomicIdealProbability part iv adversary counted D| ≤
      duplexModeLoss Q := by
  let := DuplexPublicSimulator.seedFintype
  rw [atomic_ideal_probability_eq]
  exact PublicCompressionCouplingActualJoint.actual_modeAdv_le_duplexModeLoss Q iv adversary counted D

open Classical in
/-- The complete, literal source domain instantiates the game theorem without
an arbitrary packet-family completeness or equal-distribution premise. -/
theorem canonical_source_atomic_game_bound {AdvCoins R : Type} [Fintype AdvCoins]
    (profile : ParameterBounds.Profile) (Qcompression : Nat) (iv : Digest32)
    (entry : FramedHistory) (adversary : AdvCoins → Program R)
    (counted : ∀ a, Counts Qcompression (adversary a)) (D : View R → Bool) :
    |realProbability iv adversary D -
      atomicIdealProbability
        (CanonicalPacket.partition (p := profile) (Q := Qcompression) (iv := iv) (entry := entry))
        iv adversary counted D| ≤ duplexModeLoss Qcompression :=
  actual_source_atomic_game_bound _ iv adversary counted D

#print axioms atomic_ideal_probability_eq
#print axioms actual_source_atomic_game_bound
end Whir.PCSBCSChallengeOracle
