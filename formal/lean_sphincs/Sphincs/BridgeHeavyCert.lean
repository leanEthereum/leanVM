import Sphincs.BridgeDetCloseF
import Sphincs.BridgeHeavyRoutes

/-! **The certificate of the large route with one heavy message.** The heavy coin `wbarH q` pays the
rate at `q / 2` cached digests (`fair_ofH`); a heavy cover (`checkCoverH`) is a light cover checked
with `N + 1` signatures and the heavy coin, and bounds the large-route term with the spare slot
(`startExcessH`) at every budget it covers. A chain of light covers followed by heavy covers
(`checkCoversH`) gives the deterministic signer at 127 bits (`det_bitsFH`). -/

open ENNReal NNReal

namespace Sphincs.Security.H0

open Concrete ForestPrice ForsPotential SphincsFors.Security.H0 SphincsFors.Security.Domination

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

/-! ### The checker -/

/-- The identity mass of a group under the heavy coin, times `2^128`, at subtree height `b` and
budget `q`. -/
def denHB (b q : ℕ) : ℕ := 2 ^ 128 - (q / 2 + (scanMb b - 1) * lmaxB b q)

/-- The heavy coin is fair up to the budget `qtop`, and the table rate covers `N + 1` signatures and
the creations of the scan signer under the heavy coin at every budget `q ≤ qtop`. -/
def checkRateH (b N qtop : ℕ) (t : PoisT) : Bool :=
  decide (qtop / 2 + (scanMb b - 1) * lmaxB b qtop + (2 * scanMb b - 1) ≤ 2 ^ 128) &&
    decide (((N : ℚ) + 1) / 2 ^ b +
      ((2 * scanMb b - 1 : ℕ) : ℚ) * qtop / (scanMb b * denHB b qtop * 2 ^ b) ≤ t.mu)

/-- A heavy cover of every budget `qstart ≤ q ≤ qtop`. -/
def checkCoverH (b N qstart : ℕ) (c : CoverW) : Bool :=
  checkRateH b N c.qtop c.tab && checkPT c.tab && c.opts.all (checkOptF b c.tab) &&
    chainF b N c.qtop c.opts qstart c.entries

variable [Params]

/-! ### The heavy coin -/

/-- The mass that the group of a message keeps on the identity, times `2^128`, with at most `q / 2`
cached digests. -/
def denH (q : ℕ) : ℕ := 2 ^ 128 - (q / 2 + (scanM - 1) * LmaxOf q)

/-- Coin probability of the scan signer with one heavy message at budget `q` (with `Cmax = q / 2`,
`Lmax = LmaxOf q`). -/
noncomputable def wbarH (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 * (scanM : ℝ) - 1) / (denH q : ℝ))

/-- **The coin of the scan signer is fair for any cap `C` on the cached digests and `L` on the landed
pairs** whose identity mass pays it. -/
theorem fair_gen (C L : ℕ) (hq : C + (scanM - 1) * L + (2 * scanM - 1) ≤ 2 ^ 128) :
    FairS (ENNReal.ofReal ((2 * (scanM : ℝ) - 1) / ((2 ^ 128 - (C + (scanM - 1) * L) : ℕ) : ℝ))) C L := by
  set D : ℕ := 2 ^ 128 - (C + (scanM - 1) * L) with hDdef
  have hM : (1 : ℝ) ≤ (scanM : ℝ) := by exact_mod_cast scanM_pos
  have hD : D + (C + (scanM - 1) * L) = 2 ^ 128 := by omega
  have hDge : 2 * scanM - 1 ≤ D := by omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    have : 0 < D := by have := scanM_pos; omega
    exact_mod_cast this
  have hDr : (D : ℝ) = 2 ^ 128 - ((C : ℝ) + ((scanM : ℝ) - 1) * (L : ℝ)) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hD
    push_cast [Nat.cast_sub scanM_pos] at h
    linarith
  have hDger : 2 * (scanM : ℝ) - 1 ≤ (D : ℝ) := by
    have h : ((2 * scanM - 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDge
    have h2 : ((2 * scanM - 1 : ℕ) : ℝ) = 2 * (scanM : ℝ) - 1 := by
      rw [Nat.cast_sub (by have := scanM_pos; omega)]; push_cast; ring
    linarith
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one hDpos).2 hDger)
  · have hc : (Fintype.card Randomness : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ 128) := by
      rw [GraphView.card_randomness, one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
      congr 1
      rw [← ENNReal.ofReal_natCast]
      congr 1
      norm_num
    have hl1 : (1 : ℝ≥0∞) - landing = ENNReal.ofReal (1 - 1 / (scanM : ℝ)) := by
      rw [landing_eq_M, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    have hnat : ∀ n : ℕ, (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := fun n => (ENNReal.ofReal_natCast n).symm
    have h1M : (0 : ℝ) ≤ 1 - 1 / (scanM : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hM
    rw [hc, hl1, landing_eq_M, hnat C, hnat L]
    have hsub : (0 : ℝ) ≤ 1 / (scanM : ℝ) * ((C : ℝ) * (1 / 2 ^ 128)) +
        (L : ℝ) * (1 - 1 / (scanM : ℝ)) * (1 / 2 ^ 128) := by positivity
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add h1M (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_sub _ hsub, ← ENNReal.ofReal_mul (by
        apply div_nonneg _ hDpos.le; linarith)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hM0 : (scanM : ℝ) ≠ 0 := by linarith
    rw [hDr] at hDpos ⊢
    field_simp
    ring

/-- **The heavy coin is fair** at every budget whose identity mass pays it. -/
theorem fair_ofH (q : ℕ) (h : q / 2 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128) :
    FairS (wbarH q) (q / 2) (LmaxOf q) := fair_gen (q / 2) (LmaxOf q) h

theorem wbarH_le_one (q : ℕ) (h : q / 2 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128) :
    wbarH q ≤ 1 := (fair_ofH q h).le_one

/-- The creation rate under the heavy coin: `landing · wbarH q = (2 − landing) / denH q`. -/
theorem landing_mul_wbarH (q : ℕ) :
    (landing * wbarH q).toReal = (2 - 1 / (scanM : ℝ)) / (denH q : ℝ) := by
  have hM : (1 : ℝ) ≤ (scanM : ℝ) := by exact_mod_cast scanM_pos
  have hD0 : (0 : ℝ) ≤ (denH q : ℝ) := Nat.cast_nonneg _
  unfold wbarH
  rw [landing_eq_M, ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by
    apply mul_nonneg (by positivity); apply div_nonneg _ hD0; linarith)]
  have hM0 : (scanM : ℝ) ≠ 0 := by linarith
  by_cases hD : (denH q : ℝ) = 0
  · rw [hD]; simp
  · field_simp

/-- The fair-rate condition of the heavy coin holds at every smaller budget. -/
theorem fair_cond_monoH {q q' : ℕ} (h : q ≤ q')
    (hq' : q' / 2 + (scanM - 1) * LmaxOf q' + (2 * scanM - 1) ≤ 2 ^ 128) :
    q / 2 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128 := by
  have := Nat.mul_le_mul_left (scanM - 1) (LmaxOf_mono h)
  omega

theorem denH_anti {q q' : ℕ} (h : q ≤ q') : denH q' ≤ denH q := by
  have := Nat.mul_le_mul_left (scanM - 1) (LmaxOf_mono h)
  unfold denH
  omega

/-! ### Soundness of the heavy cover -/

theorem denHB_eq (b : ℕ) (hb : subtreeHeight = b) (q : ℕ) : denHB b q = denH q := by
  unfold denHB denH; rw [scanMb_eq b hb, lmaxB_eq b hb]

/-- The fair-rate condition of the heavy coin at every budget of a checked table. -/
theorem fair_of_rateH (b N qtop : ℕ) (t : PoisT) (ht : checkRateH b N qtop t = true) (hb : subtreeHeight = b)
    (q : ℕ) (hq : q ≤ qtop) : q / 2 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128 := by
  simp only [checkRateH, Bool.and_eq_true, decide_eq_true_eq] at ht
  have h := ht.1
  rw [scanMb_eq b hb, lmaxB_eq b hb] at h
  exact fair_cond_monoH hq h

/-- The rate of `N + 1` signatures and of the creations under the heavy coin is below the table rate
for every budget `q ≤ qtop`. -/
theorem rate_le_tableH (b N qtop : ℕ) (t : PoisT) (ht : checkRateH b N qtop t = true) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (q : ℕ) (hq : q ≤ qtop) :
    ((signatureLimit + 1 : ℕ) : ℝ) / 2 ^ b + (q : ℝ) * (landing * wbarH q).toReal / 2 ^ b ≤ (t.mu : ℝ) := by
  have hft := fair_of_rateH b N qtop t ht hb qtop le_rfl
  simp only [checkRateH, Bool.and_eq_true, decide_eq_true_eq] at ht
  have h2 := ht.2
  rw [scanMb_eq b hb, denHB_eq b hb] at h2
  have h2' := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at h2'
  have hM : (1 : ℝ) ≤ (scanM : ℝ) := by exact_mod_cast scanM_pos
  have hDt : (0 : ℝ) < (denH qtop : ℝ) := by
    have : 0 < denH qtop := by unfold denH; have := scanM_pos; omega
    exact_mod_cast this
  have hDq : (denH qtop : ℝ) ≤ (denH q : ℝ) := by exact_mod_cast denH_anti hq
  have hcast : ((2 * scanM - 1 : ℕ) : ℝ) = 2 * (scanM : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := scanM_pos; omega)]; push_cast; ring
  rw [hcast] at h2'
  rw [landing_mul_wbarH q, hN]
  have hq' : (q : ℝ) ≤ (qtop : ℝ) := by exact_mod_cast hq
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hkey : (q : ℝ) * ((2 - 1 / (scanM : ℝ)) / (denH q : ℝ)) ≤
      (2 * (scanM : ℝ) - 1) * qtop / ((scanM : ℝ) * (denH qtop : ℝ)) := by
    have h1 : (2 - 1 / (scanM : ℝ)) / (denH q : ℝ) ≤ (2 - 1 / (scanM : ℝ)) / (denH qtop : ℝ) :=
      div_le_div_of_nonneg_left (by rw [sub_nonneg, div_le_iff₀ (by linarith)]; linarith) hDt hDq
    calc (q : ℝ) * ((2 - 1 / (scanM : ℝ)) / (denH q : ℝ)) ≤ (qtop : ℝ) * ((2 - 1 / (scanM : ℝ)) / (denH qtop : ℝ)) := by
          apply mul_le_mul hq' h1 _ (by positivity)
          apply div_nonneg _ (by linarith)
          rw [sub_nonneg, div_le_iff₀ (by linarith)]; linarith
      _ = _ := by
          have hM0 : (scanM : ℝ) ≠ 0 := by linarith
          field_simp
  have hNc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hNc]
  calc ((N : ℝ) + 1) / 2 ^ b + (q : ℝ) * ((2 - 1 / (scanM : ℝ)) / (denH q : ℝ)) / 2 ^ b
      ≤ ((N : ℝ) + 1) / 2 ^ b + (2 * (scanM : ℝ) - 1) * qtop / ((scanM : ℝ) * (denH qtop : ℝ)) / 2 ^ b := by gcongr
    _ = ((N : ℝ) + 1) / 2 ^ b + (2 * (scanM : ℝ) - 1) * qtop / ((scanM : ℝ) * (denH qtop : ℝ) * 2 ^ b) := by
        rw [div_div]
    _ ≤ _ := h2'

/-- **A checked table and option bound the forest H-term with the spare slot** at every budget
`q ≤ qtop` and every base `β ≥ cthr`. -/
theorem startExcessH_le_opt (b N qtop : ℕ) (t : PoisT) (o : OptF) (hr : checkRateH b N qtop t = true)
    (ht : checkPT t = true)
    (ho : checkOptF b t o = true) (hb : subtreeHeight = b) (hN : signatureLimit = N) (q : ℕ)
    (hq : q ≤ qtop) (β : ℝ≥0∞) (hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ β) :
    ForsPotential.startExcessH (wbarH q) β q ≤ ENNReal.ofReal (o.B : ℝ) := by
  have h := hTermO_le_optF hb t o ht ho (wbarH q) landing (wbarH_le_one q (fair_of_rateH b N qtop t hr hb q hq))
    ForsPotential.landing_le_one
    (signatureLimit + 1) q (rate_le_tableH b N qtop t hr hb hN q hq) β hβc
  exact h

/-- The bound for one checked entry, for any H-term `X` below the option's bound. -/
theorem bound_of_entryX (b N : ℕ) (t : PoisT) (opts : List OptF)
    (hopts : ∀ o ∈ opts, checkOptF b t o = true) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (e : EntryF) (he : checkEntryF b N opts e = true) (q : ℕ) (hqa : e.1 ≤ q)
    (hqb : q ≤ e.2.1) (X : ℝ≥0∞)
    (hX : ∀ o ∈ opts, ENNReal.ofReal (o.cthr : ℝ) ≤ HiddenDebt.baselineW q → X ≤ ENNReal.ofReal (o.B : ℝ)) :
    (1 - HiddenDebt.budget 0 q) + (q : ℝ≥0∞) * X +
        ((q + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  obtain ⟨o, ho, hqb2, hcthr, hmain⟩ := checkEntryF_sound he
  obtain ⟨qa, qb, j⟩ := e
  dsimp only at hqa hqb hqb2 hcthr hmain
  have hoc := hopts o ho
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hB0 : (0 : ℝ) ≤ (o.B : ℝ) := by exact_mod_cast optF_B_nonneg hoc
  have hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ HiddenDebt.baselineW q :=
    le_trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast hcthr)) (ForsPotential.baselineW_ge q qb hqb)
  have hH : X ≤ ENNReal.ofReal (o.B : ℝ) := hX o ho hβc
  have hmainR : (qb : ℝ) * (o.B : ℝ) * ((1 / 2 : ℝ) / (1 - 1 / 2)) + ((qb : ℝ) + (kCreditF b : ℝ) + N) / 2 ^ 200 ≤
      ((qa : ℝ) / 2 ^ 128) ^ 2 + (kCreditF b : ℝ) / 2 ^ 127 := by
    have := (Rat.cast_le (K := ℝ)).mpr hmain
    push_cast at this
    norm_num
    linarith
  have hfinal := final_real (q : ℝ) (qa : ℝ) (qb : ℝ) (kCreditF b : ℝ) (N : ℝ) (o.B : ℝ) (1 / 2) 1
    (by exact_mod_cast hqa) (by exact_mod_cast hqb) (Nat.cast_nonneg _) hB0 (by norm_num) (by norm_num)
    (by norm_num) hmainR
  rw [mul_one] at hfinal
  rw [hb, hN, show 226 * 2 ^ b + 2 * (26 - b) = kCreditF b from rfl]
  have hbud : 1 - HiddenDebt.budget 0 q =
      ENNReal.ofReal (1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) := by
    unfold HiddenDebt.budget HiddenDebt.spaceReal
    rw [Nat.cast_zero, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (sq_nonneg _)]
  have hslackE : ((q + kCreditF b + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 =
      ENNReal.ofReal (((q : ℝ) + kCreditF b + N) / 2 ^ 200) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ← inv_pow, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have hrhs : ((q + kCreditF b : ℕ) : ℝ≥0∞) / 2 ^ 127 = ENNReal.ofReal (((q : ℝ) + kCreditF b) / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have hqE : (q : ℝ≥0∞) * ENNReal.ofReal (o.B : ℝ) = ENNReal.ofReal ((q : ℝ) * (o.B : ℝ)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hbud0 : 0 ≤ 1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2 := by
    have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq127
    have h0 : 0 ≤ ((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0) := by
      apply div_nonneg <;> linarith [show (2 : ℝ) ^ 128 = 2 * 2 ^ 127 by norm_num, show (0 : ℝ) ≤ q from Nat.cast_nonneg _]
    have h1 : ((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0) ≤ 1 := by
      rw [div_le_one (by norm_num)]; linarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg _]
    nlinarith
  calc 1 - HiddenDebt.budget 0 q + (q : ℝ≥0∞) * X +
        ((q + kCreditF b + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200
      ≤ ENNReal.ofReal (1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) +
          ENNReal.ofReal ((q : ℝ) * (o.B : ℝ)) +
          ENNReal.ofReal (((q : ℝ) + kCreditF b + N) / 2 ^ 200) := by
        rw [hbud, hslackE, ← hqE]
        gcongr
    _ = ENNReal.ofReal ((1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) +
          (q : ℝ) * (o.B : ℝ) + ((q : ℝ) + kCreditF b + N) / 2 ^ 200) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add hbud0 (by positivity)]
    _ ≤ ENNReal.ofReal (((q : ℝ) + kCreditF b) / 2 ^ 127) := ENNReal.ofReal_le_ofReal hfinal
    _ = _ := hrhs.symm

/-- The bound for one checked entry of a heavy cover. -/
theorem bound_of_entryH (b N qtop : ℕ) (t : PoisT) (opts : List OptF) (hr : checkRateH b N qtop t = true)
    (ht : checkPT t = true) (hopts : ∀ o ∈ opts, checkOptF b t o = true) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (e : EntryF) (he : checkEntryF b N opts e = true) (q : ℕ) (hqa : e.1 ≤ q)
    (hqb : q ≤ e.2.1) (hqt : q ≤ qtop) :
    (1 - HiddenDebt.budget 0 q) + (q : ℝ≥0∞) * ForsPotential.startExcessH (wbarH q) (HiddenDebt.baselineW q) q +
        ((q + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  bound_of_entryX b N t opts hopts hb hN e he q hqa hqb _ fun o ho hβc =>
    startExcessH_le_opt b N qtop t o hr ht (hopts o ho) hb hN q hqt _ hβc

/-- **The forest H-term bound with the spare slot at the weighted baseline from a heavy cover
certificate**, for every budget `qstart ≤ q' ≤ qtop`. -/
theorem h0H_bound_of_cover (b N qstart : ℕ) (cover : CoverW) (hcov : checkCoverH b N qstart cover = true)
    (hb : subtreeHeight = b) (hN : signatureLimit = N) (q' : ℕ) (hq0 : qstart ≤ q') (hq : q' ≤ cover.qtop) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * ForsPotential.startExcessH (wbarH q') (HiddenDebt.baselineW q') q' +
        ((q' + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  simp only [checkCoverH, Bool.and_eq_true, List.all_eq_true] at hcov
  obtain ⟨⟨⟨hr, ht⟩, hopts⟩, hchain⟩ := hcov
  obtain ⟨e, -, h1, h2, h3⟩ := chainF_sound b N cover.qtop cover.opts cover.entries qstart hchain q' hq0 hq
  exact bound_of_entryH b N cover.qtop cover.tab cover.opts hr ht hopts hb hN e h3 q' h1 h2 hq

/-- The fair-rate condition of the heavy coin at every budget of a heavy cover. -/
theorem fair_of_coverH (b N qstart : ℕ) (cover : CoverW) (hcov : checkCoverH b N qstart cover = true)
    (hb : subtreeHeight = b) (q' : ℕ) (hq : q' ≤ cover.qtop) :
    q' / 2 + (scanM - 1) * LmaxOf q' + (2 * scanM - 1) ≤ 2 ^ 128 := by
  simp only [checkCoverH, Bool.and_eq_true, List.all_eq_true] at hcov
  exact fair_of_rateH b N cover.qtop cover.tab hcov.1.1.1 hb q' hq

end Sphincs.Security.H0

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal
  SphincsFors.Security.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

/-! ### A chain of light covers, then heavy covers -/

/-- A chain of heavy covers of the large budgets, ending once every budget `q'` with
`q' + keygenCost < 2^127` is covered. -/
def checkCoversHeavy (b N : ℕ) : ℕ → List H0.CoverW → Bool
  | qstart, [] => decide (2 ^ 127 ≤ qstart + (226 * 2 ^ b + 2 * (26 - b)))
  | qstart, c :: heavy => H0.checkCoverH b N qstart c && checkCoversHeavy b N (c.qtop + 1) heavy

/-- A chain of covers of the large budgets: light covers first, then heavy covers. -/
def checkCoversH (b N : ℕ) : ℕ → List H0.CoverW → List H0.CoverW → Bool
  | qstart, [], heavy => checkCoversHeavy b N qstart heavy
  | qstart, c :: light, heavy => H0.checkCoverW b N qstart c && checkCoversH b N (c.qtop + 1) light heavy

theorem checkCoversH_cons (b N qstart : ℕ) (c : H0.CoverW) (light heavy : List H0.CoverW) :
    checkCoversH b N qstart (c :: light) heavy =
      (H0.checkCoverW b N qstart c && checkCoversH b N (c.qtop + 1) light heavy) := rfl

theorem checkCoversH_nil_cons (b N qstart : ℕ) (c : H0.CoverW) (heavy : List H0.CoverW) :
    checkCoversH b N qstart [] (c :: heavy) =
      (H0.checkCoverH b N qstart c && checkCoversH b N (c.qtop + 1) [] heavy) := rfl

theorem checkCoversH_nil_nil (b N qstart : ℕ) :
    checkCoversH b N qstart [] [] = decide (2 ^ 127 ≤ qstart + (226 * 2 ^ b + 2 * (26 - b))) := rfl

/-- Every budget from `qstart` on with `q' + keygenCost < 2^127` lies in a checked heavy cover. -/
theorem checkCoversHeavy_sound (b N : ℕ) : ∀ (heavy : List H0.CoverW) (qstart : ℕ),
    checkCoversHeavy b N qstart heavy = true → ∀ q', qstart ≤ q' → q' + (226 * 2 ^ b + 2 * (26 - b)) < 2 ^ 127 →
      ∃ c ∈ heavy, ∃ qs, H0.checkCoverH b N qs c = true ∧ qs ≤ q' ∧ q' ≤ c.qtop
  | [], qstart, h, q', h0, h1 => by
      simp only [checkCoversHeavy, decide_eq_true_eq] at h
      omega
  | c :: rest, qstart, h, q', h0, h1 => by
      simp only [checkCoversHeavy, Bool.and_eq_true] at h
      by_cases hq : q' ≤ c.qtop
      · exact ⟨c, List.mem_cons_self .., qstart, h.1, h0, hq⟩
      · obtain ⟨c', hc', hrest⟩ := checkCoversHeavy_sound b N rest (c.qtop + 1) h.2 q' (by omega) h1
        exact ⟨c', List.mem_cons_of_mem _ hc', hrest⟩

/-- Every budget from `qstart` on with `q' + keygenCost < 2^127` lies in a checked light cover or in
a checked heavy cover of the chain. -/
theorem checkCoversH_sound (b N : ℕ) (heavy : List H0.CoverW) : ∀ (light : List H0.CoverW) (qstart : ℕ),
    checkCoversH b N qstart light heavy = true → ∀ q', qstart ≤ q' →
      q' + (226 * 2 ^ b + 2 * (26 - b)) < 2 ^ 127 →
      (∃ c ∈ light, ∃ qs, H0.checkCoverW b N qs c = true ∧ qs ≤ q' ∧ q' ≤ c.qtop) ∨
        (∃ c ∈ heavy, ∃ qs, H0.checkCoverH b N qs c = true ∧ qs ≤ q' ∧ q' ≤ c.qtop)
  | [], qstart, h, q', h0, h1 => Or.inr (checkCoversHeavy_sound b N heavy qstart h q' h0 h1)
  | c :: rest, qstart, h, q', h0, h1 => by
      simp only [checkCoversH, Bool.and_eq_true] at h
      by_cases hq : q' ≤ c.qtop
      · exact Or.inl ⟨c, List.mem_cons_self .., qstart, h.1, h0, hq⟩
      · rcases checkCoversH_sound b N heavy rest (c.qtop + 1) h.2 q' (by omega) h1 with
          ⟨c', hc', hrest⟩ | hheavy
        · exact Or.inl ⟨c', List.mem_cons_of_mem _ hc', hrest⟩
        · exact Or.inr hheavy

variable [Params]

/-! ### Both routes -/

set_option maxRecDepth 100000 in
/-- **127 bits for the deterministic signer of the forest**, from the small-route check at `qh` (with
a table whose rate is checked at `qh`) and a checked chain of light covers, then heavy covers, of the
large budgets from `qh + 1` up to `2^127 − 1 − keygenCost`. -/
theorem det_bitsFH (hb0 : 0 < subtreeHeight) (b N : ℕ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true)
    (hrt : H0.checkRate b N qh t = true) (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true)
    (hsmall : checkSmallF b N qh ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true)
    (covers heavy : List H0.CoverW) (hcov : checkCoversH b N (qh + 1) covers heavy = true) :
    Det.HasClassicalSecurityBitsDet 127 := by
  obtain ⟨hnum, hqh, hN70, hcthr, hB, hc, hpayR, hcheck⟩ := checkSmallF_sound hsmall
  have hN70' : signatureLimit ≤ 2 ^ 70 := hN ▸ hN70
  set c : ℚ := (2 ^ b * on.En : ℚ) / 2 with hcdef
  set κ : ℚ := 2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) * 123 / (2 ^ b * 2 ^ 15) with hκdef
  have hκR : (κ : ℝ) = 2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by
    rw [hκdef]
    push_cast
    ring
  have hκ0 : 0 ≤ κ := by
    have hR : (0 : ℝ) ≤ (κ : ℝ) := by
      rw [hκR]
      have h1 : (ρ : ℝ) ≤ 2 := hnum.high
      have h2 : (0 : ℝ) ≤ (qh : ℝ) / 2 ^ 128 := by positivity
      have h3 : (0 : ℝ) ≤ (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by positivity
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
    rw [Rat.cast_mul, hκR, ← H0.scanMb_eq b hb]
    refine le_of_eq_of_le ?_ hcheck
    ring
  have hkg : keygenCost = 226 * 2 ^ b + 2 * (26 - b) := by rw [← hb]; rfl
  intro q hq1 adversary hbound
  by_cases hbig : 2 ^ 127 ≤ q
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hbig
  have hq127 : q < 2 ^ 127 := Nat.lt_of_not_le hbig
  by_cases hs : q - keygenCost ≤ qh
  · have hx : ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 ≤ (qh : ℝ) / 2 ^ 128 :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)
    have hnum' : Numeric (ρ : ℝ) (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) :=
      numeric_monoF hnum hx (by positivity)
    have hκq : 2 - (ρ : ℝ) + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
        (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ (κ : ℝ) := by
      have he : (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) =
          (N : ℝ) * 123 / (2 ^ b * 2 ^ 15) := by
        rw [hb, hN]
        field_simp
      rw [hκR, he]
      linarith
    refine le_trans (det_smallF hb0 adversary q hbound (by omega) (ρ : ℝ) hnum' κ hκ0 hκ1 hκq b N hb hN t o on
      hpt qh hrt hs ho hon hcthr) ?_
    exact small_closeFF q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (κ * c) hB hc2 hcheck'
  · have hK : keygenCost ≤ q := by omega
    have e1 : (q - keygenCost) + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) = q - keygenCost + keygenCost :=
      rfl
    rcases checkCoversH_sound b N heavy covers (qh + 1) hcov (q - keygenCost)
      (by omega) (by rw [← hkg]; omega) with ⟨cover, -, qs, hcv, hqs, hqt⟩ | ⟨cover, -, qs, hcv, hqs, hqt⟩
    · have hcovb := H0.h0W_bound_of_cover b N qs cover hcv hb hN (q - keygenCost) hqs hqt
      have hfairq := H0.fair_of_cover b N qs cover hcv hb (q - keygenCost) hqt
      have h := det_largeW hb0 hN70' adversary q hbound hq127 hK hfairq (by
        rw [e1] at hcovb
        exact hcovb)
      refine le_trans h (le_of_eq ?_)
      rw [Nat.cast_pow, Nat.cast_ofNat]
    · have hcovb := H0.h0H_bound_of_cover b N qs cover hcv hb hN (q - keygenCost) hqs hqt
      have hfairq := H0.fair_of_coverH b N qs cover hcv hb (q - keygenCost) hqt
      have h := det_largeH hb0 adversary q hbound hq127 hK (H0.wbarH (q - keygenCost))
        (H0.LmaxOf (q - keygenCost)) (H0.fair_ofH (q - keygenCost) hfairq) (lam_start_leF (q - keygenCost)) (by
        rw [e1] at hcovb
        exact hcovb)
      refine le_trans h (le_of_eq ?_)
      rw [Nat.cast_pow, Nat.cast_ofNat]

end Sphincs.Security.ForsPotential
