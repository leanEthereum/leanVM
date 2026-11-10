module

public import Qrom.Sphincs.Security
public import Qrom.Sphincs.Bound.LamCov

@[expose] public section

/-!
# The numbers

With the cover probability bounded (`Qrom.Sphincs.lamF_le`), the forgery bound is explicit
(`Qrom.Sphincs.winProb_le_lamS`). For the parameters of `FORS.h26_layered` (`h = 26`, `d = 3`,
`k = 24`, `a = 10`, `1,182,000,000` signatures), `λ_full ≤ 9 · 2^-130` (`Qrom.Sphincs.lamS_h26`) and
a win in the hidden game weighs at most
`(13 · 2^-130 (√6 (n + 1 + verifyQueries) + 2 verifyQueries)² + 879 · 2^-128) tr ρ`
(`Qrom.Sphincs.winProb_le_h26`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

section generic

variable [Params]

/-- The weight of a win in the hidden game, with the cover probability bounded. -/
def epsB (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * searchK n) +
    ENNReal.ofReal lamS * ENNReal.ofReal (searchK n)) * ENNReal.ofReal t

theorem epsHid_le (n : ℕ) (t : ℝ) : epsHid n t ≤ epsB n t := by
  unfold epsHid epsB
  gcongr
  exact lamF_le

/-- **leanSPHINCS in the QROM, explicitly**: an adversary making at most `n` calls in all forges with
probability at most `(√ε + (n + 1 + verifyQueries) √(4 · 2^-128 tr ρ))²`, where `ε` is `epsB`. -/
theorem winProb_le_lamS {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ (epsB n ρ.matrix.trace.re ^ (2⁻¹ : ℝ) + ((1 + n + verifyQueries : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (winProb_le adv hadv ρ).trans ?_
  gcongr
  exact epsHid_le n _

end generic

/-- The parameters of `FORS.h26_layered`. -/
abbrev params26 : Params :=
  .layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10) (N := 1_182_000_000)

section h26

local instance : Params := params26

theorem lamS_h26 : lamS ≤ 9 * (2 : ℝ)⁻¹ ^ 130 := by
  have h : lamS ≤ ((9 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ 130 := lamS_le (by
    simp only [Fintype.card_fun, Fintype.card_fin, ← stirRow_getD]
    decide +kernel)
  simpa using h

theorem verifyQueries_h26 : verifyQueries = 879 := by decide

/-- **leanSPHINCS in the QROM, for the parameters of `FORS.h26_layered`.** An adversary from the
register `A` in the state `ρ`, making at most `n` calls in all (hash queries, quantum or classical,
and signing requests), forges with probability at most
`(√((13 · 2^-130 (√6 (n + 880) + 1758)² + 879 · 2^-128) tr ρ) + (n + 880) √(4 · 2^-128 tr ρ))²`. -/
theorem winProb_le_h26 {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ ((ENNReal.ofReal (13 * (2 : ℝ)⁻¹ ^ 130 * (√6 * (n + 880) + 1758) ^ 2 +
        879 * (2 : ℝ)⁻¹ ^ 128) *
        ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) + ((n + 880 : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (winProb_le_lamS adv hadv ρ).trans ?_
  have hN : (1 + n + verifyQueries : ℕ) = n + 880 := by rw [verifyQueries_h26]; omega
  rw [hN]
  gcongr
  set K := searchK n
  have hK : K = (√6 * (n + 880) + 1758) ^ 2 := by
    simp only [K, searchK, verifyQueries_h26]
    push_cast
    ring_nf
  have hK0 : 0 ≤ K := sq_nonneg _
  unfold epsB
  gcongr ?_ * _
  calc ENNReal.ofReal (verifyQueries * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * K) +
        ENNReal.ofReal lamS * ENNReal.ofReal K ≤
      ENNReal.ofReal (879 * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * K) +
        ENNReal.ofReal (9 * (2 : ℝ)⁻¹ ^ 130 * K) := by
        rw [verifyQueries_h26]
        push_cast
        gcongr
        rw [ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact lamS_h26
    _ = ENNReal.ofReal (879 * (2 : ℝ)⁻¹ ^ 128 + (2 : ℝ)⁻¹ ^ 128 * K + 9 * (2 : ℝ)⁻¹ ^ 130 * K) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        rw [← hK]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        have h1 : (2 : ℝ)⁻¹ ^ 128 = 4 * (2 : ℝ)⁻¹ ^ 130 := by norm_num
        rw [h1]
        ring

end h26

end Qrom.Sphincs
