import FORS.SmallBudget.Closing
import FORS.LargeBudget.HeavyRoute

/-! **The certificate of the large route with one heavy message.** The heavy coin `wbarH q` pays the
rate at `q / 2` cached digests (`fair_ofH`); a heavy cover (`checkCoverH`) is a light cover checked
with `N + 1` signatures and the heavy coin, and bounds the large-route term with the spare slot
(`startExcessH`) at every budget it covers. A chain of light covers followed by heavy covers
(`checkCoversH`) gives the deterministic signer at 127 bits (`det_bitsFH`). -/

open ENNReal NNReal

namespace FORS.Security.H0

variable [Params]

open Concrete ForsPrice ForsPotential FORS.Base.H0 FORS.Base.Domination

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

/-! ### The checker -/

/-- The identity mass of a group under the heavy coin, times `2^128`, at subtree height `b` and
budget `q`. -/
def denHB (H b q : ℕ) : ℕ := 2 ^ 128 - (q / 2 + (scanMb H b - 1) * lmaxB H b q)

/-- The heavy coin is fair up to the budget `qtop`, and the table rate covers `N + 1` signatures and
the creations of the scan signer under the heavy coin at every budget `q ≤ qtop`. -/
def checkRateH (H b N qtop : ℕ) (t : PoisT) : Bool :=
  decide (qtop / 2 + (scanMb H b - 1) * lmaxB H b qtop + (2 * scanMb H b - 1) ≤ 2 ^ 128) &&
    decide (((N : ℚ) + 1) / 2 ^ b +
      ((2 * scanMb H b - 1 : ℕ) : ℚ) * qtop / (scanMb H b * denHB H b qtop * 2 ^ b) ≤ t.mu)

/-- A heavy cover of every budget `qstart ≤ q ≤ qtop`. -/
def checkCoverH (H b k a K N qstart : ℕ) (c : CoverW) : Bool :=
  checkRateH H b N c.qtop c.tab && checkPT c.tab && c.opts.all (checkOpt H b k a c.tab) &&
    chainF K N c.qtop c.opts qstart c.entries

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

theorem denHB_eq (H b : ℕ) (hH : totalHeight = H) (hb : subtreeHeight = b) (q : ℕ) : denHB H b q = denH q := by
  unfold denHB denH; rw [scanMb_eq H b hH hb, lmaxB_eq H b hH hb]

/-- The fair-rate condition of the heavy coin at every budget of a checked table. -/
theorem fair_of_rateH (H b N qtop : ℕ) (t : PoisT) (ht : checkRateH H b N qtop t = true)
    (hH : totalHeight = H) (hb : subtreeHeight = b)
    (q : ℕ) (hq : q ≤ qtop) : q / 2 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128 := by
  simp only [checkRateH, Bool.and_eq_true, decide_eq_true_eq] at ht
  have h := ht.1
  rw [scanMb_eq H b hH hb, lmaxB_eq H b hH hb] at h
  exact fair_cond_monoH hq h

/-- The rate of `N + 1` signatures and of the creations under the heavy coin is below the table rate
for every budget `q ≤ qtop`. -/
theorem rate_le_tableH (H b N qtop : ℕ) (t : PoisT) (ht : checkRateH H b N qtop t = true)
    (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (q : ℕ) (hq : q ≤ qtop) :
    ((signatureLimit + 1 : ℕ) : ℝ) / 2 ^ b + (q : ℝ) * (landing * wbarH q).toReal / 2 ^ b ≤ (t.mu : ℝ) := by
  have hft := fair_of_rateH H b N qtop t ht hH hb qtop le_rfl
  simp only [checkRateH, Bool.and_eq_true, decide_eq_true_eq] at ht
  have h2 := ht.2
  rw [scanMb_eq H b hH hb, denHB_eq H b hH hb] at h2
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

/-- **A checked table and option bound the FORS H-term with the spare slot** at every budget
`q ≤ qtop` and every base `β ≥ cthr`. -/
theorem startExcessH_le_opt (H b k a N qtop : ℕ) (t : PoisT) (o : Opt) (hr : checkRateH H b N qtop t = true)
    (ht : checkPT t = true)
    (ho : checkOpt H b k a t o = true) (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (hN : signatureLimit = N) (q : ℕ)
    (hq : q ≤ qtop) (β : ℝ≥0∞) (hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ β) :
    ForsPotential.startExcessH (wbarH q) β q ≤ ENNReal.ofReal (o.B : ℝ) := by
  have h := hTermO_le_opt hH hb hk ha t o ht ho (wbarH q) landing
    (wbarH_le_one q (fair_of_rateH H b N qtop t hr hH hb q hq))
    ForsPotential.landing_le_one
    (signatureLimit + 1) q (rate_le_tableH H b N qtop t hr hH hb hN q hq) β hβc
  exact h

/-- The bound for one checked entry, for any H-term `X` below the option's bound. -/
theorem bound_of_entryX (H b k a K N : ℕ) (t : PoisT) (opts : List Opt)
    (hopts : ∀ o ∈ opts, checkOpt H b k a t o = true)
    (hK : Prefix.keygenHashCost = K) (hN : signatureLimit = N) (e : EntryF) (he : checkEntryF K N opts e = true)
    (q : ℕ) (hqa : e.1 ≤ q)
    (hqb : q ≤ e.2.1) (X : ℝ≥0∞)
    (hX : ∀ o ∈ opts, ENNReal.ofReal (o.cthr : ℝ) ≤ HiddenDebt.baselineW q → X ≤ ENNReal.ofReal (o.B : ℝ)) :
    (1 - HiddenDebt.budget 0 q) + (q : ℝ≥0∞) * X +
        ((q + Prefix.keygenHashCost + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q + Prefix.keygenHashCost : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  obtain ⟨o, ho, hqb2, hcthr, hmain⟩ := checkEntryF_sound he
  obtain ⟨qa, qb, j⟩ := e
  dsimp only at hqa hqb hqb2 hcthr hmain
  have hoc := hopts o ho
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hB0 : (0 : ℝ) ≤ (o.B : ℝ) := by exact_mod_cast opt_B_nonneg hoc
  have hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ HiddenDebt.baselineW q :=
    le_trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast hcthr)) (ForsPotential.baselineW_ge q qb hqb)
  have hH : X ≤ ENNReal.ofReal (o.B : ℝ) := hX o ho hβc
  have hmainR : (qb : ℝ) * (o.B : ℝ) * ((1 / 2 : ℝ) / (1 - 1 / 2)) + ((qb : ℝ) + (K : ℝ) + N) / 2 ^ 200 ≤
      ((qa : ℝ) / 2 ^ 128) ^ 2 + (K : ℝ) / 2 ^ 127 := by
    have := (Rat.cast_le (K := ℝ)).mpr hmain
    push_cast at this
    norm_num
    linarith
  have hfinal := final_real (q : ℝ) (qa : ℝ) (qb : ℝ) (K : ℝ) (N : ℝ) (o.B : ℝ) (1 / 2) 1
    (by exact_mod_cast hqa) (by exact_mod_cast hqb) (Nat.cast_nonneg _) hB0 (by norm_num) (by norm_num)
    (by norm_num) hmainR
  rw [mul_one] at hfinal
  rw [hK, hN]
  have hbud : 1 - HiddenDebt.budget 0 q =
      ENNReal.ofReal (1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) := by
    unfold HiddenDebt.budget HiddenDebt.spaceReal
    rw [Nat.cast_zero, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (sq_nonneg _)]
  have hslackE : ((q + K + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 =
      ENNReal.ofReal (((q : ℝ) + K + N) / 2 ^ 200) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ← inv_pow, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have hrhs : ((q + K : ℕ) : ℝ≥0∞) / 2 ^ 127 = ENNReal.ofReal (((q : ℝ) + K) / 2 ^ 127) := by
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
        ((q + K + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200
      ≤ ENNReal.ofReal (1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) +
          ENNReal.ofReal ((q : ℝ) * (o.B : ℝ)) +
          ENNReal.ofReal (((q : ℝ) + K + N) / 2 ^ 200) := by
        rw [hbud, hslackE, ← hqE]
        gcongr
    _ = ENNReal.ofReal ((1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) +
          (q : ℝ) * (o.B : ℝ) + ((q : ℝ) + K + N) / 2 ^ 200) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add hbud0 (by positivity)]
    _ ≤ ENNReal.ofReal (((q : ℝ) + K) / 2 ^ 127) := ENNReal.ofReal_le_ofReal hfinal
    _ = _ := hrhs.symm

/-- The bound for one checked entry of a heavy cover. -/
theorem bound_of_entryH (H b k a K N qtop : ℕ) (t : PoisT) (opts : List Opt) (hr : checkRateH H b N qtop t = true)
    (ht : checkPT t = true) (hopts : ∀ o ∈ opts, checkOpt H b k a t o = true) (hH : totalHeight = H)
    (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a) (hK : Prefix.keygenHashCost = K)
    (hN : signatureLimit = N) (e : EntryF) (he : checkEntryF K N opts e = true) (q : ℕ) (hqa : e.1 ≤ q)
    (hqb : q ≤ e.2.1) (hqt : q ≤ qtop) :
    (1 - HiddenDebt.budget 0 q) + (q : ℝ≥0∞) * ForsPotential.startExcessH (wbarH q) (HiddenDebt.baselineW q) q +
        ((q + Prefix.keygenHashCost + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q + Prefix.keygenHashCost : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  bound_of_entryX H b k a K N t opts hopts hK hN e he q hqa hqb _ fun o ho hβc =>
    startExcessH_le_opt H b k a N qtop t o hr ht (hopts o ho) hH hb hk ha hN q hqt _ hβc

/-- **The FORS H-term bound with the spare slot at the weighted baseline from a heavy cover
certificate**, for every budget `qstart ≤ q' ≤ qtop`. -/
theorem h0H_bound_of_cover (H b k a K N qstart : ℕ) (cover : CoverW)
    (hcov : checkCoverH H b k a K N qstart cover = true)
    (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a)
    (hK : Prefix.keygenHashCost = K) (hN : signatureLimit = N) (q' : ℕ) (hq0 : qstart ≤ q')
    (hq : q' ≤ cover.qtop) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * ForsPotential.startExcessH (wbarH q') (HiddenDebt.baselineW q') q' +
        ((q' + Prefix.keygenHashCost + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + Prefix.keygenHashCost : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  simp only [checkCoverH, Bool.and_eq_true, List.all_eq_true] at hcov
  obtain ⟨⟨⟨hr, ht⟩, hopts⟩, hchain⟩ := hcov
  obtain ⟨e, -, h1, h2, h3⟩ := chainF_sound K N cover.qtop cover.opts cover.entries qstart hchain q' hq0 hq
  exact bound_of_entryH H b k a K N cover.qtop cover.tab cover.opts hr ht hopts hH hb hk ha hK hN e h3 q'
    h1 h2 hq

/-- The fair-rate condition of the heavy coin at every budget of a heavy cover. -/
theorem fair_of_coverH (H b k a K N qstart : ℕ) (cover : CoverW)
    (hcov : checkCoverH H b k a K N qstart cover = true)
    (hH : totalHeight = H) (hb : subtreeHeight = b) (q' : ℕ) (hq : q' ≤ cover.qtop) :
    q' / 2 + (scanM - 1) * LmaxOf q' + (2 * scanM - 1) ≤ 2 ^ 128 := by
  simp only [checkCoverH, Bool.and_eq_true, List.all_eq_true] at hcov
  exact fair_of_rateH H b N cover.qtop cover.tab hcov.1.1.1 hH hb q' hq

end FORS.Security.H0

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
  FORS.Base.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

/-! ### A chain of light covers, then heavy covers -/

/-- A chain of heavy covers of the large budgets, ending once every budget `q'` with
`q' + keygenCost < 2^127` is covered. -/
def checkCoversHeavy (H b k a K N : ℕ) : ℕ → List H0.CoverW → Bool
  | qstart, [] => decide (2 ^ 127 ≤ qstart + K)
  | qstart, c :: heavy =>
      H0.checkCoverH H b k a K N qstart c && checkCoversHeavy H b k a K N (c.qtop + 1) heavy

/-- A chain of covers of the large budgets: light covers first, then heavy covers. -/
def checkCoversH (H b k a K N : ℕ) : ℕ → List H0.CoverW → List H0.CoverW → Bool
  | qstart, [], heavy => checkCoversHeavy H b k a K N qstart heavy
  | qstart, c :: light, heavy =>
      H0.checkCoverW H b k a K N qstart c && checkCoversH H b k a K N (c.qtop + 1) light heavy

/-- Every budget from `qstart` on with `q' + keygenCost < 2^127` lies in a checked heavy cover. -/
theorem checkCoversHeavy_sound (H b k a K N : ℕ) : ∀ (heavy : List H0.CoverW) (qstart : ℕ),
    checkCoversHeavy H b k a K N qstart heavy = true → ∀ q', qstart ≤ q' → q' + K < 2 ^ 127 →
      ∃ c ∈ heavy, ∃ qs, H0.checkCoverH H b k a K N qs c = true ∧ qs ≤ q' ∧ q' ≤ c.qtop
  | [], qstart, h, q', h0, h1 => by
      simp only [checkCoversHeavy, decide_eq_true_eq] at h
      omega
  | c :: rest, qstart, h, q', h0, h1 => by
      simp only [checkCoversHeavy, Bool.and_eq_true] at h
      by_cases hq : q' ≤ c.qtop
      · exact ⟨c, List.mem_cons_self .., qstart, h.1, h0, hq⟩
      · obtain ⟨c', hc', hrest⟩ := checkCoversHeavy_sound H b k a K N rest (c.qtop + 1) h.2 q' (by omega) h1
        exact ⟨c', List.mem_cons_of_mem _ hc', hrest⟩

/-- Every budget from `qstart` on with `q' + keygenCost < 2^127` lies in a checked light cover or in
a checked heavy cover of the chain. -/
theorem checkCoversH_sound (H b k a K N : ℕ) (heavy : List H0.CoverW) :
    ∀ (light : List H0.CoverW) (qstart : ℕ),
    checkCoversH H b k a K N qstart light heavy = true → ∀ q', qstart ≤ q' →
      q' + K < 2 ^ 127 →
      (∃ c ∈ light, ∃ qs, H0.checkCoverW H b k a K N qs c = true ∧ qs ≤ q' ∧ q' ≤ c.qtop) ∨
        (∃ c ∈ heavy, ∃ qs, H0.checkCoverH H b k a K N qs c = true ∧ qs ≤ q' ∧ q' ≤ c.qtop)
  | [], qstart, h, q', h0, h1 => Or.inr (checkCoversHeavy_sound H b k a K N heavy qstart h q' h0 h1)
  | c :: rest, qstart, h, q', h0, h1 => by
      simp only [checkCoversH, Bool.and_eq_true] at h
      by_cases hq : q' ≤ c.qtop
      · exact Or.inl ⟨c, List.mem_cons_self .., qstart, h.1, h0, hq⟩
      · rcases checkCoversH_sound H b k a K N heavy rest (c.qtop + 1) h.2 q' (by omega) h1 with
          ⟨c', hc', hrest⟩ | hheavy
        · exact Or.inl ⟨c', List.mem_cons_of_mem _ hc', hrest⟩
        · exact Or.inr hheavy

/-! ### Both routes -/

set_option maxRecDepth 100000 in
/-- **127 bits for the deterministic signer**, from the small-route check at `qh` (with
a table whose rate is checked at `qh`) and a checked chain of light covers, then heavy covers, of the
large budgets from `qh + 1` up to `2^127 − 1 − keygenCost`. -/
theorem det_bitsFH (hb0 : 0 < keptHeight topLayer) (H b k a K N : ℕ) (hH : totalHeight = H)
    (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a)
    (hK : Prefix.keygenHashCost = K) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true)
    (hrt : H0.checkRate H b N qh t = true) (ho : H0.checkOpt H b k a t o = true)
    (hon : H0.checkOptN H k a t on = true)
    (hsmall : checkSmallF H b a N qh ρ o.cthr o.B ((2 ^ b * on.En : ℚ) / 2) = true)
    (covers heavy : List H0.CoverW) (hcov : checkCoversH H b k a K N (qh + 1) covers heavy = true) :
    HasClassicalSecurityBits 127 := by
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
        (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) ≤ (κ : ℝ) := by
      have he : (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) =
          (N : ℝ) / (2 ^ b * 2 ^ a) := by
        rw [hb, ha, hN]
        field_simp
      rw [hκR, he]
      linarith
    refine le_trans (det_smallF hb0 adversary q hbound (by omega) (ρ : ℝ) hnum' κ hκ0 hκ1 hκq
      H b k a N hH hb hk ha hN t o on hpt qh hrt hs ho hon hcthr) ?_
    exact small_closeFF q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (κ * c) hB hc2 hcheck'
  · have hKq : keygenCost ≤ q := by omega
    have e1 : (q - keygenCost) + Prefix.keygenHashCost = q - keygenCost + keygenCost :=
      rfl
    rcases checkCoversH_sound H b k a K N heavy covers (qh + 1) hcov (q - keygenCost)
      (by omega) (by rw [← hkg]; omega) with ⟨cover, -, qs, hcv, hqs, hqt⟩ | ⟨cover, -, qs, hcv, hqs, hqt⟩
    · have hcovb := H0.h0W_bound_of_cover H b k a K N qs cover hcv hH hb hk ha hK hN (q - keygenCost) hqs hqt
      have hfairq := H0.fair_of_cover H b k a K N qs cover hcv hH hb (q - keygenCost) hqt
      have h := det_largeW hb0 hN70' adversary q hbound hq127 hKq hfairq (by
        rw [e1] at hcovb
        exact hcovb)
      refine le_trans h (le_of_eq ?_)
      rw [Nat.cast_pow, Nat.cast_ofNat]
    · have hcovb := H0.h0H_bound_of_cover H b k a K N qs cover hcv hH hb hk ha hK hN (q - keygenCost) hqs hqt
      have hfairq := H0.fair_of_coverH H b k a K N qs cover hcv hH hb (q - keygenCost) hqt
      have h := det_largeH hb0 adversary q hbound hq127 hKq (H0.wbarH (q - keygenCost))
        (H0.LmaxOf (q - keygenCost)) (H0.fair_ofH (q - keygenCost) hfairq) (lam_start_leF (q - keygenCost)) (by
        rw [e1] at hcovb
        exact hcovb)
      refine le_trans h (le_of_eq ?_)
      rw [Nat.cast_pow, Nat.cast_ofNat]

end FORS.Security.ForsPotential
