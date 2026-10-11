import Whir.PublicCompressionCouplingResidual
import Whir.PublicCompressionCouplingStreams

/-! Exact residual disintegration of the second marginal of the actual
shared-answer coupling. Domination is checked only on operationally reachable
joint results, and averages every completion of their actual final cache. -/
namespace Whir.PublicCompressionCouplingJoint
open FiatShamirGame TypedFiatShamirGame RawOracleCoupling
open TypedOracleCompiler (Sampling)

variable {A B R S : Type} [DecidableEq A] [DecidableEq B] [Fintype B]

/-- The untouched coordinates remain uniform after the adaptive second run. -/
theorem joint_second_residual {n m : Nat} (p : Computation A R n) (pc : Cache A)
    (q : Computation B S m) (qc : Cache B)
    (payoff : (S × Cache B) → (B → Digest32) → ℚ) :
    Sampling.expectation (fun pair => average (fun table : B → Digest32 =>
      payoff pair.2 (overlay pair.2.2 table))) (joint p pc q qc) =
    average (fun table : B → Digest32 =>
      payoff (Sampling.eval (overlay qc table) (memo q qc)) (overlay qc table)) := by
  rw [joint_second p pc q qc (fun result => average (fun table : B → Digest32 =>
    payoff result (overlay result.2 table)))]
  exact (PublicCompressionCouplingResidual.memo_residual q qc payoff).symm

/-- Reachability-aware monotonicity needs no condition on unused result values. -/
theorem expectation_mono_runs {K T : Type} {n : Nat}
    (p : Sampling K (fun _ => Digest32) T n) (f g : T → ℚ)
    (bound : ∀ trace result, Sampling.Runs p trace result → f result ≤ g result) :
    Sampling.expectation f p ≤ Sampling.expectation g p := by
  induction p with
  | ret result => exact bound [] result (.ret result)
  | draw key next ih =>
    apply average_mono
    intro answer
    apply ih answer
    intro trace result execution
    apply bound (⟨key,answer⟩::trace) result
    exact @Sampling.Runs.draw K (fun _ => Digest32) T _ key next trace result answer execution

/-- A pointwise bound for every residual completion lifts to the exact second
marginal, without sampling a transcript certificate or restricting an observer. -/
theorem joint_residual_domination {n m : Nat} (p : Computation A R n) (pc : Cache A)
    (q : Computation B S m) (qc : Cache B)
    (f : ((R × Cache A) × (S × Cache B)) → ℚ)
    (payoff : (S × Cache B) → (B → Digest32) → ℚ)
    (bound : ∀ trace pair, Sampling.Runs (joint p pc q qc) trace pair →
      ∀ table : B → Digest32, f pair ≤ payoff pair.2 (overlay pair.2.2 table)) :
    Sampling.expectation f (joint p pc q qc) ≤
      average (fun table : B → Digest32 =>
        payoff (Sampling.eval (overlay qc table) (memo q qc)) (overlay qc table)) := by
  rw [← joint_second_residual p pc q qc payoff]
  apply expectation_mono_runs
  intro trace pair execution
  calc
    f pair = average (fun _ : B → Digest32 => f pair) := (average_const _).symm
    _ ≤ average (fun table : B → Digest32 => payoff pair.2 (overlay pair.2.2 table)) :=
      average_mono (bound trace pair execution)

#print axioms joint_second_residual
#print axioms joint_residual_domination
end Whir.PublicCompressionCouplingJoint
