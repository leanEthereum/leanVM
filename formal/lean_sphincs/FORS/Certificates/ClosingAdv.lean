module

public import FORS.Certificates.Closing
public import FORS.Certificates.VerifyCost
public import FORS.SmallBudget.BridgeH
public import FORS.LargeBudget.HeavyRouteH

@[expose] public section

/-! **127 bits at the adversary's own count.** The certificates of `Closing.lean`, read at the budget
`q = keygenHashCost + qA + V` of an adversary making at most `qA` hash calls against a verifier making
at most `V`: the honest signer's small route (`det_smallF`, its program bridge `smallBridgeH_holds`)
and large routes (`forgeAdvantage_le_largeWH`, `forgeAdvantage_le_largeHH`) close as the charged ones
do, and the forging chance is at most `(qA + keygenHashCost + V) / 2^127`. -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
  FORS.Base.Domination
open HiddenBridge PotentialA

set_option maxRecDepth 100000 in
/-- **127 bits at the adversary's own count**, from the certificates and a verifier making
at most `V` hash calls on every path. -/
theorem det_bitsF (hb0 : 0 < keptHeight topLayer) (H b k a K N : ℕ) (hH : totalHeight = H)
    (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a)
    (hK : Prefix.keygenHashCost = K) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true)
    (hrt : H0.checkRate H b N qh t = true) (ho : H0.checkOpt H b k a t o = true)
    (hon : H0.checkOptN H k a t on = true)
    (hsmall : checkSmallF H b a N qh ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true)
    (covers heavy : List H0.CoverW) (hcov : checkCoversH H b k a K N (qh + 1) covers heavy = true)
    (V : ℕ) (hV : ∀ pk message signature,
      (Concrete.verify pk message signature : OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) V)
    (adversary : Adversary) (qA : ℕ) (hqA : ∀ pk, (adversary.main pk).IsQueryBoundP AdvCount.AdvHash qA) :
    forgeAdvantage adversary ≤ ((qA : ℝ≥0∞) + ((K + V : ℕ) : ℝ≥0∞)) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  obtain ⟨hnum, hqh, hN70, hcthr, hB, hc, hpayR, hcheck⟩ := checkSmallF_sound hsmall
  have hN70' : signatureLimit ≤ 2 ^ 70 := hN ▸ hN70
  set c : ℚ := (2 ^ b * on.En : ℚ) / 2 with hcdef
  set κ : ℚ := 2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) / (2 ^ b * 2 ^ a) with hκdef
  have hκR : (κ : ℝ) = 2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) / (2 ^ b * 2 ^ a) := by
    rw [hκdef]
    push_cast
    ring
  have hκ0 : 0 ≤ κ := by
    have hR : (0 : ℝ) ≤ (κ : ℝ) := by
      rw [hκR]
      have h1 : (ρ : ℝ) ≤ 2 := hnum.high
      have h2 : (0 : ℝ) ≤ (qh : ℝ) / 2 ^ 128 := by positivity
      have h3 : (0 : ℝ) ≤ (N : ℝ) / (2 ^ b * 2 ^ a) := by positivity
      linarith
    exact_mod_cast hR
  have hκ1 : κ ≤ 1 := by
    have hR : (κ : ℝ) ≤ 1 := by
      rw [hκR]
      linarith
    exact_mod_cast hR
  have hc2 : (0 : ℚ) ≤ κ * c := mul_nonneg hκ0 hc
  have hcheck' : (ρ : ℝ) + 2 ^ 128 * (o.B : ℝ) +
      (2 * (H0.scanM : ℝ) - 1) * (qh : ℝ) / ((H0.scanM : ℝ) * 2 ^ 129) +
      qh * ((κ * c : ℚ) : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
    rw [Rat.cast_mul, hκR, ← H0.scanMb_eq H b hH hb]
    refine le_of_eq_of_le ?_ hcheck
    ring
  have hkg : keygenCost = K := hK
  set q : ℕ := Prefix.keygenHashCost + qA + V with hqdef
  have hrhs : (qA : ℝ≥0∞) + ((K + V : ℕ) : ℝ≥0∞) = (q : ℝ≥0∞) := by
    rw [hqdef, ← hK]
    push_cast
    ring
  rw [hrhs]
  have hq1 : 1 ≤ q := by
    have := one_le_keygenCostF
    omega
  by_cases hbig : 2 ^ 127 ≤ q
  · refine le_trans (prEvent_le_one _) ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hbig
  have hq127 : q < 2 ^ 127 := Nat.lt_of_not_le hbig
  by_cases hs : q - keygenCost ≤ qh
  · have hx : ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 ≤ (qh : ℝ) / 2 ^ 128 :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)
    have hnum' : Numeric (ρ : ℝ) (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) :=
      numeric_monoF hnum hx (by positivity)
    have hκq : 2 - (ρ : ℝ) + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
        (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) ≤ (κ : ℝ) := by
      have he : (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) =
          (N : ℝ) / (2 ^ b * 2 ^ a) := by
        rw [hb, ha, hN]
        field_simp
      rw [hκR, he]
      linarith
    refine le_trans (det_smallF adversary qA V hqA hV
      (fun steps => smallBridgeH_holds hb0 _ q (by omega) steps) (ρ : ℝ) hnum' κ hκ0 hκ1 hκq
      H b k a N hH hb hk ha hN t o on hpt qh hrt hs ho hon hcthr) ?_
    exact small_closeFF q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (κ * c) hB hc2 hcheck'
  · have hKq : keygenCost ≤ q := by omega
    have e1 : (q - keygenCost) + Prefix.keygenHashCost = q - keygenCost + keygenCost :=
      rfl
    rcases checkCoversH_sound H b k a K N heavy covers (qh + 1) hcov (q - keygenCost)
      (by omega) (by rw [← hkg]; omega) with ⟨cover, -, qs, hcv, hqs, hqt⟩ | ⟨cover, -, qs, hcv, hqs, hqt⟩
    · have hcovb := H0.h0W_bound_of_cover H b k a K N qs cover hcv hH hb hk ha hK hN (q - keygenCost) hqs hqt
      have hfairq := H0.fair_of_cover H b k a K N qs cover hcv hH hb (q - keygenCost) hqt
      have h := forgeAdvantage_le_largeWH hb0 hN70' adversary qA V hqA hV q hqdef hq127 hfairq (by
        rw [e1] at hcovb
        exact hcovb)
      refine le_trans h (le_of_eq ?_)
      rw [Nat.cast_pow, Nat.cast_ofNat]
    · have hcovb := H0.h0H_bound_of_cover H b k a K N qs cover hcv hH hb hk ha hK hN (q - keygenCost) hqs hqt
      have hfairq := H0.fair_of_coverH H b k a K N qs cover hcv hH hb (q - keygenCost) hqt
      have h := forgeAdvantage_le_largeHH hb0 adversary qA V hqA hV q hqdef hq127 (H0.wbarH (q - keygenCost))
        (H0.LmaxOf (q - keygenCost)) (H0.fair_ofH (q - keygenCost) hfairq) (lam_start_leF (q - keygenCost)) (by
        rw [e1] at hcovb
        exact hcovb)
      refine le_trans h (le_of_eq ?_)
      rw [Nat.cast_pow, Nat.cast_ofNat]

end FORS.Security.ForsPotential
