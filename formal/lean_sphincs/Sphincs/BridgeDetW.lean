import Sphincs.H0ForestOpt
import Sphincs.BridgeSatWRoutes
import SphincsFors.H0Numeric

/-! Forest split-bound covers at the survival-weighted baseline `baselineW` (thresholds `betaWQ`): a
successful cover check bounds the large-route term at every budget it covers. -/

open ENNReal NNReal

namespace Sphincs.Security.H0

open Concrete ForestPrice SphincsFors.Security.H0 SphincsFors.Security.Domination

/-- Keygen credit `K` of the forest signer: the `226 · 2^b + 2 (26 − b)` hash calls of key
generation from the scheme seed (`Prefix.hashCalls_keygenFromMaster`), with one seed derivation for
the starts of two chains. The call deriving the scheme seed is not credited. -/
def kCreditF (b : ℕ) : ℕ := 226 * 2 ^ b + 2 * (26 - b)

/-- A cover entry: budgets `[qa, qb]` and the index of its option. -/
abbrev EntryF := ℕ × ℕ × ℕ

/-- A forest cover: a Poisson table, options, entries. -/
structure CoverW where
  qtop : ℕ
  tab : PoisT
  opts : List OptF
  entries : List EntryF

/-- The inverse landing probability at subtree height `b`. -/
def scanMb (b : ℕ) : ℕ := 2 ^ (26 - b)

/-- The cap on the landed pairs at subtree height `b` and budget `q`. -/
def lmaxB (b q : ℕ) : ℕ := 65 * ((q + 64 * scanMb b - 1) / (64 * scanMb b)) + 2 ^ 15

/-- The identity mass of a group, times `2^128`, at subtree height `b` and budget `q`. -/
def denB (b q : ℕ) : ℕ := 2 ^ 128 - (q + 2 ^ 32 + (scanMb b - 1) * lmaxB b q)

/-- The scan coin is fair up to the budget `qtop`, and the table rate covers the signatures and the
creations of the scan signer (`(2 − landing) q / denB` per unit) at every budget `q ≤ qtop`. -/
def checkRate (b N qtop : ℕ) (t : PoisT) : Bool :=
  decide (qtop + 2 ^ 32 + (scanMb b - 1) * lmaxB b qtop + (2 * scanMb b - 1) ≤ 2 ^ 128) &&
    decide ((N : ℚ) / 2 ^ b + ((2 * scanMb b - 1 : ℕ) : ℚ) * qtop / (scanMb b * denB b qtop * 2 ^ b) ≤ t.mu)

/-- The check of one entry. -/
def checkEntryF (b N : ℕ) (opts : List OptF) (e : EntryF) : Bool :=
  match opts[e.2.2]? with
  | none => false
  | some o =>
      decide (2 * e.2.1 ≤ 2 ^ 128) && decide (o.cthr ≤ ForsPotential.betaWQ e.2.1) &&
        decide ((e.2.1 : ℚ) * o.B + ((e.2.1 : ℚ) + kCreditF b + N) / 2 ^ 200 ≤
          ((e.1 : ℚ) / 2 ^ 128) ^ 2 + (kCreditF b : ℚ) / 2 ^ 127)

/-- Consecutive entries cover `[last, 2^127]`. -/
def chainF (b N qtop : ℕ) (opts : List OptF) : ℕ → List EntryF → Bool
  | last, [] => decide (qtop < last)
  | last, e :: rest => decide (e.1 ≤ last) && checkEntryF b N opts e && chainF b N qtop opts (e.2.1 + 1) rest

/-- A cover of every budget `qstart ≤ q ≤ qtop`. -/
def checkCoverW (b N qstart : ℕ) (c : CoverW) : Bool :=
  checkRate b N c.qtop c.tab && checkPT c.tab && c.opts.all (checkOptF b c.tab) &&
    chainF b N c.qtop c.opts qstart c.entries

theorem chainF_sound (b N qtop : ℕ) (opts : List OptF) : ∀ (cover : List EntryF) (last : ℕ),
    chainF b N qtop opts last cover = true →
      ∀ q, last ≤ q → q ≤ qtop → ∃ e ∈ cover, e.1 ≤ q ∧ q ≤ e.2.1 ∧ checkEntryF b N opts e = true
  | [], last, h, q, hq, hq' => by
      simp only [chainF, decide_eq_true_eq] at h
      omega
  | e :: rest, last, h, q, hq, hq' => by
      simp only [chainF, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨he1, he2⟩, hrest⟩ := h
      by_cases hle : q ≤ e.2.1
      · exact ⟨e, List.mem_cons_self .., by omega, hle, he2⟩
      · obtain ⟨e', he', h1, h2, h3⟩ := chainF_sound b N qtop opts rest _ hrest q (by omega) hq'
        exact ⟨e', List.mem_cons_of_mem _ he', h1, h2, h3⟩

theorem checkEntryF_sound {b N : ℕ} {opts : List OptF} {e : EntryF} (h : checkEntryF b N opts e = true) :
    ∃ o ∈ opts, 2 * e.2.1 ≤ 2 ^ 128 ∧ o.cthr ≤ ForsPotential.betaWQ e.2.1 ∧
      (e.2.1 : ℚ) * o.B + ((e.2.1 : ℚ) + kCreditF b + N) / 2 ^ 200 ≤
        ((e.1 : ℚ) / 2 ^ 128) ^ 2 + (kCreditF b : ℚ) / 2 ^ 127 := by
  unfold checkEntryF at h
  rcases hget : opts[e.2.2]? with _ | o
  · rw [hget] at h; exact absurd h (by simp)
  · rw [hget] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨o, List.mem_of_getElem? hget, h.1.1, h.1.2, h.2⟩

theorem optF_B_nonneg {b : ℕ} {t : PoisT} {o : OptF} (ho : checkOptF b t o = true) : 0 ≤ o.B := by
  obtain ⟨-, hθ, hcthr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hB, hEg0, hEe0⟩ := checkOptF_parts ho
  have hsq0 : 0 ≤ sqUp t.P b (1 + o.Ee) := by
    have h := sqUp_ge t.P b (1 + o.Ee) ((1 + o.Ee : ℚ) : ℝ) (by push_cast; positivity) le_rfl
    have h0 : (0 : ℝ) ≤ ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by push_cast; positivity
    exact_mod_cast le_trans h0 h
  have hE := one_le_expLow (o.θ * o.cthr) t.J t.P (by positivity)
  have he : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
  refine le_trans ?_ hB
  positivity

variable [Params]

theorem scanMb_eq (b : ℕ) (hb : subtreeHeight = b) : scanMb b = scanM := by unfold scanMb scanM; rw [hb]

theorem lmaxB_eq (b : ℕ) (hb : subtreeHeight = b) (q : ℕ) : lmaxB b q = LmaxOf q := by
  unfold lmaxB LmaxOf; rw [scanMb_eq b hb]

theorem denB_eq (b : ℕ) (hb : subtreeHeight = b) (q : ℕ) : denB b q = denOf q := by
  unfold denB denOf; rw [scanMb_eq b hb, lmaxB_eq b hb]

/-- The fair-rate condition of the scan coin at every budget of a checked table. -/
theorem fair_of_rate (b N qtop : ℕ) (t : PoisT) (ht : checkRate b N qtop t = true) (hb : subtreeHeight = b)
    (q : ℕ) (hq : q ≤ qtop) : q + 2 ^ 32 + (scanM - 1) * LmaxOf q + (2 * scanM - 1) ≤ 2 ^ 128 := by
  simp only [checkRate, Bool.and_eq_true, decide_eq_true_eq] at ht
  have h := ht.1
  rw [scanMb_eq b hb, lmaxB_eq b hb] at h
  exact fair_cond_mono hq h

/-- The creation rate of the scan signer is below the table rate for every budget `q ≤ qtop`. -/
theorem rate_le_tableF (b N qtop : ℕ) (t : PoisT) (ht : checkRate b N qtop t = true) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (q : ℕ) (hq : q ≤ qtop) :
    (signatureLimit : ℝ) / 2 ^ b + (q : ℝ) * (landing * wbarOf q).toReal / 2 ^ b ≤ (t.mu : ℝ) := by
  have hfq := fair_of_rate b N qtop t ht hb q hq
  have hft := fair_of_rate b N qtop t ht hb qtop le_rfl
  simp only [checkRate, Bool.and_eq_true, decide_eq_true_eq] at ht
  have h2 := ht.2
  rw [scanMb_eq b hb, denB_eq b hb] at h2
  have h2' := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at h2'
  have hM : (1 : ℝ) ≤ (scanM : ℝ) := by exact_mod_cast scanM_pos
  have hDt : (0 : ℝ) < (denOf qtop : ℝ) := by
    have : 0 < denOf qtop := by unfold denOf; have := scanM_pos; omega
    exact_mod_cast this
  have hDq : (denOf qtop : ℝ) ≤ (denOf q : ℝ) := by exact_mod_cast denOf_anti hq
  have hcast : ((2 * scanM - 1 : ℕ) : ℝ) = 2 * (scanM : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := scanM_pos; omega)]; push_cast; ring
  rw [hcast] at h2'
  rw [landing_mul_wbar q hfq, hN]
  have hq' : (q : ℝ) ≤ (qtop : ℝ) := by exact_mod_cast hq
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hkey : (q : ℝ) * ((2 - 1 / (scanM : ℝ)) / (denOf q : ℝ)) ≤
      (2 * (scanM : ℝ) - 1) * qtop / ((scanM : ℝ) * (denOf qtop : ℝ)) := by
    have h1 : (2 - 1 / (scanM : ℝ)) / (denOf q : ℝ) ≤ (2 - 1 / (scanM : ℝ)) / (denOf qtop : ℝ) :=
      div_le_div_of_nonneg_left (by rw [sub_nonneg, div_le_iff₀ (by linarith)]; linarith) hDt hDq
    calc (q : ℝ) * ((2 - 1 / (scanM : ℝ)) / (denOf q : ℝ)) ≤ (qtop : ℝ) * ((2 - 1 / (scanM : ℝ)) / (denOf qtop : ℝ)) := by
          apply mul_le_mul hq' h1 _ (by positivity)
          apply div_nonneg _ (by linarith)
          rw [sub_nonneg, div_le_iff₀ (by linarith)]; linarith
      _ = _ := by
          have hM0 : (scanM : ℝ) ≠ 0 := by linarith
          field_simp
  calc (N : ℝ) / 2 ^ b + (q : ℝ) * ((2 - 1 / (scanM : ℝ)) / (denOf q : ℝ)) / 2 ^ b
      ≤ (N : ℝ) / 2 ^ b + (2 * (scanM : ℝ) - 1) * qtop / ((scanM : ℝ) * (denOf qtop : ℝ)) / 2 ^ b := by gcongr
    _ = (N : ℝ) / 2 ^ b + (2 * (scanM : ℝ) - 1) * qtop / ((scanM : ℝ) * (denOf qtop : ℝ) * 2 ^ b) := by
        rw [div_div]
    _ ≤ _ := h2'

/-- **A checked table and option bound the one-coin forest H-term** at every budget `q ≤ qtop` and
every base `β ≥ cthr`. -/
theorem startExcessO_le_opt (b N qtop : ℕ) (t : PoisT) (o : OptF) (hr : checkRate b N qtop t = true)
    (ht : checkPT t = true)
    (ho : checkOptF b t o = true) (hb : subtreeHeight = b) (hN : signatureLimit = N) (q : ℕ)
    (hq : q ≤ qtop) (β : ℝ≥0∞) (hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ β) :
    ForsPotential.startExcessO (wbarOf q) β q ≤ ENNReal.ofReal (o.B : ℝ) := by
  have h := hTermO_le_optF hb t o ht ho (wbarOf q) landing (wbar_le_one q (fair_of_rate b N qtop t hr hb q hq))
    ForsPotential.landing_le_one
    signatureLimit q (rate_le_tableF b N qtop t hr hb hN q hq) β hβc
  exact h


/-- The bound for one checked entry. -/
theorem bound_of_entryF (b N qtop : ℕ) (t : PoisT) (opts : List OptF) (hr : checkRate b N qtop t = true)
    (ht : checkPT t = true) (hopts : ∀ o ∈ opts, checkOptF b t o = true) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (e : EntryF) (he : checkEntryF b N opts e = true) (q : ℕ) (hqa : e.1 ≤ q)
    (hqb : q ≤ e.2.1) (hqt : q ≤ qtop) :
    (1 - HiddenDebt.budget 0 q) + (q : ℝ≥0∞) * ForsPotential.startExcessO (wbarOf q) (HiddenDebt.baselineW q) q +
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
  have hq2 : 2 * q ≤ 2 ^ 128 := by omega
  have hB0 : (0 : ℝ) ≤ (o.B : ℝ) := by exact_mod_cast optF_B_nonneg hoc
  have hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ HiddenDebt.baselineW q :=
    le_trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast hcthr)) (ForsPotential.baselineW_ge q qb hqb)
  have hH : ForsPotential.startExcessO (wbarOf q) (HiddenDebt.baselineW q) q ≤ ENNReal.ofReal (o.B : ℝ) :=
    startExcessO_le_opt b N qtop t o hr ht hoc hb hN q hqt _ hβc
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
  calc 1 - HiddenDebt.budget 0 q + (q : ℝ≥0∞) * ForsPotential.startExcessO (wbarOf q) (HiddenDebt.baselineW q) q +
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

/-- **The one-coin forest H-term bound at the weighted baseline from a cover certificate**, for every
budget `qstart ≤ q' ≤ qtop`. -/
theorem h0W_bound_of_cover (b N qstart : ℕ) (cover : CoverW) (hcov : checkCoverW b N qstart cover = true)
    (hb : subtreeHeight = b) (hN : signatureLimit = N) (q' : ℕ) (hq0 : qstart ≤ q') (hq : q' ≤ cover.qtop) :
    (1 - HiddenDebt.budget 0 q') +
        (q' : ℝ≥0∞) * ForsPotential.startExcessO (wbarOf q') (HiddenDebt.baselineW q') q' +
        ((q' + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (226 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  simp only [checkCoverW, Bool.and_eq_true, List.all_eq_true] at hcov
  obtain ⟨⟨⟨hr, ht⟩, hopts⟩, hchain⟩ := hcov
  obtain ⟨e, -, h1, h2, h3⟩ := chainF_sound b N cover.qtop cover.opts cover.entries qstart hchain q' hq0 hq
  exact bound_of_entryF b N cover.qtop cover.tab cover.opts hr ht hopts hb hN e h3 q' h1 h2 hq

/-- The fair-rate condition of the scan coin at every budget of a cover. -/
theorem fair_of_cover (b N qstart : ℕ) (cover : CoverW) (hcov : checkCoverW b N qstart cover = true)
    (hb : subtreeHeight = b) (q' : ℕ) (hq : q' ≤ cover.qtop) :
    q' + 2 ^ 32 + (scanM - 1) * LmaxOf q' + (2 * scanM - 1) ≤ 2 ^ 128 := by
  simp only [checkCoverW, Bool.and_eq_true, List.all_eq_true] at hcov
  exact fair_of_rate b N cover.qtop cover.tab hcov.1.1.1 hb q' hq

end Sphincs.Security.H0
