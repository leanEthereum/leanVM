import Whir.PublicCompressionCoupling

/-! Exact disintegration of an actual uniform finite table after an adaptive
public computation. It leaves a uniformly sampled completion behind the real
memo cache; this is what justifies private, post-public prefix inspection. -/
namespace Whir.PublicCompressionCouplingResidual
open FiatShamirGame TypedOracleCompiler TypedFiatShamirGame RawOracleCoupling

variable {K R : Type} [DecidableEq K] [Fintype K]
abbrev D := Digest32
abbrev Table (K : Type) := K → D

 theorem table_residual {n : Nat} (p : Sampling K (fun _ => D) R n)
    (cache : K → Option D) (payoff : R → Table K → ℚ) :
    average (fun table : Table K =>
      payoff (Sampling.eval (overlay cache table) p) (overlay cache table)) =
    Sampling.expectation (fun result => average (fun table : Table K =>
      payoff result.1 (overlay result.2 table))) (memo p cache) := by
  induction p generalizing cache with
  | ret r => rfl
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      simp only [memo,hit,Sampling.expectation_pad]
      rw [← ih answer cache]
      apply congrArg average
      funext table
      simp [Sampling.eval,overlay,hit]
    | none =>
      rw [overlay_average cache key hit
        (fun table => payoff (Sampling.eval table (.draw key next)) table)]
      simp only [memo,hit,Sampling.expectation]
      apply congrArg average
      funext answer
      rw [← ih answer (put cache key answer)]
      apply congrArg average
      funext table
      simp [Sampling.eval,overlay]


/-- The residual completion is conditional on the actual completed memo cache,
not an assumed transcript certificate. -/
theorem memo_residual {n : Nat} (p : Sampling K (fun _ => D) R n)
    (cache : K → Option D) (payoff : (R × (K → Option D)) → Table K → ℚ) :
    average (fun table : Table K =>
      payoff (Sampling.eval (overlay cache table) (memo p cache)) (overlay cache table)) =
    Sampling.expectation (fun result => average (fun table : Table K =>
      payoff result (overlay result.2 table))) (memo p cache) := by
  induction p generalizing cache with
  | ret r => rfl
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      simp only [memo,hit,Sampling.expectation_pad,Sampling.eval_pad]
      exact ih answer cache
    | none =>
      rw [overlay_average cache key hit
        (fun table => payoff (Sampling.eval table (memo (.draw key next) cache)) table)]
      simp only [memo,hit,Sampling.expectation]
      apply congrArg average
      funext answer
      rw [← ih answer (put cache key answer)]
      apply congrArg average
      funext table
      simp [Sampling.eval,overlay]

#print axioms memo_residual
#print axioms table_residual
end Whir.PublicCompressionCouplingResidual
