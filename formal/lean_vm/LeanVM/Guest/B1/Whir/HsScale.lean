/-
  LeanVM.Guest.B1.Whir.HsScale

  The high parts' normalizers the template bakes are `hsNorm`'s: the inverses of the subspace
  roots over a coefficient's bits, at the mid levels times `W_μ(β_μ)⁻¹`.
-/

module

public import LeanVM.Guest.B1.Whir.HsScaleCert
public import LeanVM.Guest.B1.Opening.NovelEval

/-!
# The normalizers' values

* `ofBits_hsScaleM`: `hsScaleM` multiplies `init` by the inverses' words over `c`'s bits;
* `ofBits_hsScale_norm`: where the tables hold the roots (`vanishOk v (μ + 1)`) and the fold
  agrees with `hsScaleM`, `hsScale v bits c init` is `init · hsNorm μ bits c`;
* `hsScale_mid` (`osHsMid`): a mid level's normalizer is `W_μ(β_μ)⁻¹ · hsNorm μ highBits c`,
  `μ = logCols`, and `highBits ≤ μ + 1` (`hsMid_bits`);
* `hsScale_final` (`osHsFinal`): the final lane's is `hsNorm yrLog (yrLog + 1) c`, and the final
  level's tables hold `yrLog + 1` roots (`hsFinal_vanishOk`).

With `NovelEval.residual_high_eq` and `NovelEval.novelSum_eq_novelEval` these turn the guest's
`novel_eval` into the verifier's `novelEval`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Protocol LeanVM.Guest.B1

@[expose] public section

theorem ofBits_hsScaleM (v c init : ℕ) : ∀ bits : ℕ,
    K.ofBits (hsScaleM v bits c init) = K.ofBits init *
      ∏ i ∈ Finset.range bits, if c.testBit i then K.ofBits (vanishInv (v + i)) else 1
  | 0 => by simp [hsScaleM]
  | b + 1 => by
    have ih := ofBits_hsScaleM v c init b
    unfold hsScaleM at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.prod_range_succ]
    split
    · rw [Pow.ofBits_mulN, ih]; ring
    · rw [ih, mul_one]

/-- **A normalizer's value**, where the tables hold the roots and `kmulN` agrees with `mulN`. -/
theorem ofBits_hsScale_norm {v mu bits c init : ℕ} (hv : vanishOk v (mu + 1) = true)
    (hb : bits ≤ mu + 1) (he : hsScale v bits c init = hsScaleM v bits c init) :
    K.ofBits (hsScale v bits c init) = K.ofBits init * hsNorm mu bits c := by
  rw [he, ofBits_hsScaleM, hsNorm]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [vanish_inv hv i (by have := Finset.mem_range.1 hi; omega)]

theorem hsScaleOk_mid {m l : ℕ} (hm : m < ligNSizes) (hl : l < osNLevels m) : hsMidOk m l = true := by
  have h := hsScale_all m hm
  simp only [hsScaleOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.1 l hl

/-- A mid level's high bits are at most `logCols + 1`. -/
theorem hsMid_bits {m l : ℕ} (hm : m < ligNSizes) (hl : l < osNLevels m) :
    (osLv m l).highBits ≤ (osLv m l).logCols + 1 := by
  have h := hsScaleOk_mid hm hl
  simp only [hsMidOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- **A mid level's normalizer** (`osHsMid`): `W_μ(β_μ)⁻¹ · hsNorm μ highBits c`, `μ = logCols`. -/
theorem hsScale_mid {m l c : ℕ} (hm : m < ligNSizes) (hl : l < osNLevels m) (hc : c < (osLv m l).folds) :
    K.ofBits (hsScale (osLv m l).vanish (osLv m l).highBits c
        (vanishInv ((osLv m l).vanish + (osLv m l).logCols))) =
      ((Verifier.subspaceRoots (osLv m l).logCols).getD (osLv m l).logCols 0)⁻¹ *
        hsNorm (osLv m l).logCols (osLv m l).highBits c := by
  have h := hsScaleOk_mid hm hl
  simp only [hsMidOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  have hv := vanish_all m hm l hl
  rw [ofBits_hsScale_norm hv h.1 (h.2 c hc), vanish_inv hv _ le_rfl]

/-- The final level's row. -/
abbrev osLvFin (m : ℕ) : OsLv := osLv m (osCfg m).yrLevel

theorem hsScaleOk_fin {m : ℕ} (hm : m < ligNSizes) : hsFinOk m (osLvFin m) = true := by
  have h := hsScale_all m hm
  simp only [hsScaleOk, Bool.and_eq_true] at h
  exact h.2

/-- The final level's tables hold `yrLog + 1` roots. -/
theorem hsFinal_vanishOk {m : ℕ} (hm : m < ligNSizes) :
    vanishOk (osLvFin m).vanish ((osCfg m).yrLog + 1) = true := by
  have h := hsScaleOk_fin hm
  simp only [hsFinOk, Bool.and_eq_true] at h
  exact h.1

/-- **The final lane's normalizer** (`osHsFinal`): `hsNorm yrLog (yrLog + 1) c`. -/
theorem hsScale_final {m c : ℕ} (hm : m < ligNSizes) (hc : c < (osCfg m).yrLen + (osLvFin m).folds) :
    K.ofBits (hsScale (osLvFin m).vanish ((osCfg m).yrLog + 1) c 1) =
      hsNorm (osCfg m).yrLog ((osCfg m).yrLog + 1) c := by
  have h := hsScaleOk_fin hm
  simp only [hsFinOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [ofBits_hsScale_norm h.1 le_rfl (h.2 c hc), show K.ofBits 1 = 1 from rfl, one_mul]

end
end LeanVM.Guest.B1.Whir
