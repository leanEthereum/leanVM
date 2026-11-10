module

public import Qrom.Sphincs.Security
public import Qrom.Sphincs.Bound.LamCov

@[expose] public section

/-!
# The numbers

With the cover probability bounded (`Qrom.Sphincs.lamCov_le`), the forgery bound is explicit
(`Qrom.Sphincs.winProb_le_lamB`). For the parameters of `FORS.h26_layered` (`h = 26`, `d = 3`,
`k = 24`, `a = 10`, `1,182,000,000` signatures), `λ_cov ≤ 2^-98` (`Qrom.Sphincs.lamB_h26`) and a win
in the hidden game weighs at most `(2^-97 (√6 (n + 1 + verifyQueries) + 2 verifyQueries)² + 2^-68) tr ρ`
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
    ENNReal.ofReal badB + ENNReal.ofReal lamB * ENNReal.ofReal (searchK n)) * ENNReal.ofReal t

theorem epsHid_le (hmd : mdBytes ≤ 32) (n : ℕ) (t : ℝ) : epsHid n t ≤ epsB n t := by
  unfold epsHid epsB
  gcongr
  exact lamCov_le hmd

/-- **leanSPHINCS in the QROM, explicitly**: when the FORS leaves fit the first digest call, an
adversary making at most `n` calls in all forges with probability at most
`(√ε + (n + 1 + verifyQueries) √(4 · 2^-128 tr ρ))²`, where `ε` is `epsB`. -/
theorem winProb_le_lamB (hmd : mdBytes ≤ 32) {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ (epsB n ρ.matrix.trace.re ^ (2⁻¹ : ℝ) + ((1 + n + verifyQueries : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (winProb_le adv hadv ρ).trans ?_
  gcongr
  exact epsHid_le hmd n _

end generic

/-- The parameters of `FORS.h26_layered`. -/
abbrev params26 : Params :=
  .layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10) (N := 1_182_000_000)

theorem mdBytes_h26 : @mdBytes params26 ≤ 32 := by decide

theorem lamB_h26 : @lamB params26 ≤ (2 : ℝ)⁻¹ ^ 98 := by
  unfold lamB
  simp only [Fintype.card_fun, Fintype.card_fin]
  norm_num [Finset.prod_range_succ, signatureLimit, forsTrees, totalHeight, forsHeight]

section h26

local instance : Params := params26

theorem verifyQueries_h26 : verifyQueries = 879 := by decide

theorem badB_h26 : badB = 3 * (2 : ℝ)⁻¹ ^ 70 := by
  unfold badB
  norm_num [totalHeight, numLayers, counterBits]

/-- **leanSPHINCS in the QROM, for the parameters of `FORS.h26_layered`.** An adversary from the
register `A` in the state `ρ`, making at most `n` calls in all (hash queries, quantum or classical,
and signing requests), forges with probability at most
`(√((2^-97 (√6 (n + 880) + 1758)² + 2^-68) tr ρ) + (n + 880) √(4 · 2^-128 tr ρ))²`. -/
theorem winProb_le_h26 {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    winProb adv ρ ≤ ((ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 97 * (√6 * (n + 880) + 1758) ^ 2 + (2 : ℝ)⁻¹ ^ 68) *
        ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) + ((n + 880 : ℕ) : ℝ≥0∞) *
      (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (winProb_le_lamB mdBytes_h26 adv hadv ρ).trans ?_
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
        ENNReal.ofReal badB + ENNReal.ofReal lamB * ENNReal.ofReal K ≤
      ENNReal.ofReal (879 * (2 : ℝ)⁻¹ ^ 128) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 * K) +
        ENNReal.ofReal (3 * (2 : ℝ)⁻¹ ^ 70) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 98 * K) := by
        rw [verifyQueries_h26, badB_h26]
        push_cast
        gcongr
        rw [ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact lamB_h26
    _ = ENNReal.ofReal (879 * (2 : ℝ)⁻¹ ^ 128 + (2 : ℝ)⁻¹ ^ 128 * K + 3 * (2 : ℝ)⁻¹ ^ 70 +
          (2 : ℝ)⁻¹ ^ 98 * K) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        rw [← hK]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (2 : ℝ)⁻¹ ^ 128 + (2 : ℝ)⁻¹ ^ 98 ≤ (2 : ℝ)⁻¹ ^ 97 := by norm_num
        have h2 : 879 * (2 : ℝ)⁻¹ ^ 128 + 3 * (2 : ℝ)⁻¹ ^ 70 ≤ (2 : ℝ)⁻¹ ^ 68 := by norm_num
        have h3 := mul_le_mul_of_nonneg_right h1 hK0
        linarith

end h26

end Qrom.Sphincs
