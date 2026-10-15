import SphincsFors.H0Once

/-! Poisson domination of the one-coin H-term at the level of count functions
`F : (ι → ℕ) → ℝ≥0∞`. A count function is good (`CountGood`) if it is monotone, has increasing
differences across coordinates and along each coordinate, and grows at most exponentially. Good
functions are closed under Poisson coordinates and Bernoulli coins; a Bernoulli coin is below a Poisson
coordinate of the same mean (chord), and a uniform-or-nothing slot of probability `p` is below
iid Poisson coordinates of mean `p / L`. Hence the one-coin H-term of `F ∘ cnt` is below the iid
Poisson mean of `F` at rate `N / L + q λ w / L`. -/

open ENNReal NNReal

namespace SphincsFors.Security.H0

open Domination

set_option linter.unusedSectionVars false

/-! ### Poisson weights -/

/-- The Poisson weight `e^{-a} a^n / n!`. -/
noncomputable def poisW (a : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(a : ℝ)) * (a : ℝ) ^ n / n.factorial)

theorem poisW_tsum (a : ℝ≥0) : ∑' n, poisW a n = 1 := by
  have h := ProbabilityTheory.hasSum_one_poissonMeasure a
  unfold poisW
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h.summable, h.tsum_eq, ENNReal.ofReal_one]

theorem poisW_succ (a : ℝ≥0) (n : ℕ) : poisW a (n + 1) * ((n + 1 : ℕ) : ℝ≥0∞) = (a : ℝ≥0∞) * poisW a n := by
  unfold poisW
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem poisW_mean (a : ℝ≥0) : ∑' n, poisW a n * (n : ℝ≥0∞) = a := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  have h : ∀ n : ℕ, poisW a (n + 1) * ((n + 1 : ℕ) : ℝ≥0∞) = (a : ℝ≥0∞) * poisW a n := poisW_succ a
  simp only [Nat.cast_succ] at h ⊢
  simp only [h, ENNReal.tsum_mul_left, poisW_tsum, mul_one]

theorem poisW_zero_rate (n : ℕ) : poisW 0 n = if n = 0 then 1 else 0 := by
  unfold poisW
  rcases n with _ | n
  · simp
  · simp

/-- **Poisson convolution.** -/
theorem poisW_conv (a b : ℝ≥0) (s : ℕ) :
    ∑ x ∈ Finset.antidiagonal s, poisW a x.1 * poisW b x.2 = poisW (a + b) s := by
  unfold poisW
  rw [Finset.sum_congr rfl fun x _ => (ENNReal.ofReal_mul (by positivity)).symm,
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  congr 1
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  rw [add_pow, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have his : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.cast_choose ℝ his]
  have h1 : (0 : ℝ) < (i.factorial : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((s - i).factorial : ℝ) := by positivity
  have h3 : (0 : ℝ) < (s.factorial : ℝ) := by positivity
  rw [neg_add, Real.exp_add]
  field_simp

/-- `Σ e^{-a} a^n / n! r^n = e^{a r - a}`. -/
theorem poisW_mul_pow (a r : ℝ≥0) :
    ∑' n, poisW a n * (r : ℝ≥0∞) ^ n = ENNReal.ofReal (Real.exp ((a : ℝ) * r - a)) := by
  have h : ∀ n, poisW a n * (r : ℝ≥0∞) ^ n = ENNReal.ofReal (Real.exp ((a : ℝ) * r - a)) * poisW (a * r) n := by
    intro n
    unfold poisW
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    push_cast
    have key : Real.exp ((a : ℝ) * r - a) * Real.exp (-((a : ℝ) * r)) = Real.exp (-(a : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [mul_pow, ← key]
    ring
  simp only [h, ENNReal.tsum_mul_left, poisW_tsum, mul_one]

/-! ### Poisson coordinates -/

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Add an independent `Poisson(a)` count to coordinate `l`. -/
noncomputable def pois (a : ℝ≥0) (l : ι) (G : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ) : ℝ≥0∞ :=
  ∑' n, poisW a n * G (k + Pi.single l n)

theorem pois_mono (a : ℝ≥0) (l : ι) {G H : (ι → ℕ) → ℝ≥0∞} (h : ∀ k, G k ≤ H k) (k : ι → ℕ) :
    pois a l G k ≤ pois a l H k :=
  ENNReal.tsum_le_tsum fun _ => by gcongr; exact h _

theorem pois_add (a : ℝ≥0) (l : ι) (G H : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ) :
    pois a l (fun x => G x + H x) k = pois a l G k + pois a l H k := by
  unfold pois
  simp only [mul_add, ENNReal.tsum_add]

theorem pois_const_mul (a : ℝ≥0) (l : ι) (c : ℝ≥0∞) (G : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ) :
    pois a l (fun x => c * G x) k = c * pois a l G k := by
  unfold pois
  rw [← ENNReal.tsum_mul_left]
  congr 1; funext n; ring

theorem pois_shift (a : ℝ≥0) (l : ι) (G : (ι → ℕ) → ℝ≥0∞) (k e : ι → ℕ) :
    pois a l G (k + e) = pois a l (fun x => G (x + e)) k := by
  unfold pois
  congr 1; funext n
  rw [add_right_comm]

theorem pois_zero_rate (l : ι) (G : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ) : pois 0 l G k = G k := by
  unfold pois
  rw [tsum_eq_single 0 (fun n hn => by simp [poisW_zero_rate, hn])]
  simp [poisW_zero_rate]

theorem pois_comm (a b : ℝ≥0) (l j : ι) (G : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ) :
    pois a l (pois b j G) k = pois b j (pois a l G) k := by
  unfold pois
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; funext n; congr 1; funext m
  rw [add_right_comm]
  ring

/-- **Semigroup.** Two Poisson counts at one coordinate add up. -/
theorem pois_pois (a b : ℝ≥0) (l : ι) (G : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ) :
    pois a l (pois b l G) k = pois (a + b) l G k := by
  unfold pois
  simp only [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  rw [← (Finset.sigmaAntidiagonalEquivProd).tsum_eq, ENNReal.tsum_sigma']
  congr 1; funext s
  change ∑' x : ↥(Finset.antidiagonal s),
    (fun p : ℕ × ℕ => poisW a p.1 * (poisW b p.2 * G (k + Pi.single l p.1 + Pi.single l p.2))) x = _
  refine (Finset.tsum_subtype (Finset.antidiagonal s)
    (fun p : ℕ × ℕ => poisW a p.1 * (poisW b p.2 * G (k + Pi.single l p.1 + Pi.single l p.2)))).trans ?_
  rw [← poisW_conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [add_assoc, ← Pi.single_add, hp]
  ring

theorem le_pois (a : ℝ≥0) (l : ι) {G : (ι → ℕ) → ℝ≥0∞} (hG : Monotone G) (k : ι → ℕ) : G k ≤ pois a l G k := by
  calc G k = ∑' n, poisW a n * G k := by rw [ENNReal.tsum_mul_right, poisW_tsum, one_mul]
    _ ≤ pois a l G k := ENNReal.tsum_le_tsum fun _ => by gcongr; exact hG le_self_add

/-! ### Iid Poisson coordinates -/

/-- Poisson coordinates along a list of coordinates. -/
noncomputable def poisList (a : ℝ≥0) : List ι → ((ι → ℕ) → ℝ≥0∞) → (ι → ℕ) → ℝ≥0∞
  | [], G => G
  | l :: ls, G => poisList a ls (pois a l G)

/-- Iid `Poisson(a)` counts added to every coordinate. -/
noncomputable def poisIID (a : ℝ≥0) (G : (ι → ℕ) → ℝ≥0∞) : (ι → ℕ) → ℝ≥0∞ :=
  poisList a (Finset.univ : Finset ι).toList G

theorem poisList_mono (a : ℝ≥0) : ∀ (ls : List ι) {G H : (ι → ℕ) → ℝ≥0∞}, (∀ k, G k ≤ H k) →
    ∀ k, poisList a ls G k ≤ poisList a ls H k
  | [], _, _, h, k => h k
  | l :: ls, _, _, h, k => poisList_mono a ls (pois_mono a l h) k

theorem poisList_add (a : ℝ≥0) : ∀ (ls : List ι) (G H : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ),
    poisList a ls (fun x => G x + H x) k = poisList a ls G k + poisList a ls H k
  | [], _, _, _ => rfl
  | l :: ls, G, H, k => by
      simp only [poisList]
      rw [show pois a l (fun x => G x + H x) = fun x => pois a l G x + pois a l H x from
        funext fun x => pois_add a l G H x]
      exact poisList_add a ls _ _ k

theorem poisList_const_mul (a : ℝ≥0) (c : ℝ≥0∞) : ∀ (ls : List ι) (G : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ),
    poisList a ls (fun x => c * G x) k = c * poisList a ls G k
  | [], _, _ => rfl
  | l :: ls, G, k => by
      simp only [poisList]
      rw [show pois a l (fun x => c * G x) = fun x => c * pois a l G x from
        funext fun x => pois_const_mul a l c G x]
      exact poisList_const_mul a c ls _ k

theorem poisList_zero_rate : ∀ (ls : List ι) (G : (ι → ℕ) → ℝ≥0∞), poisList 0 ls G = G
  | [], _ => rfl
  | l :: ls, G => by
      simp only [poisList]
      rw [show pois 0 l G = G from funext fun x => pois_zero_rate l G x]
      exact poisList_zero_rate ls G

theorem poisList_pois (a b : ℝ≥0) (j : ι) : ∀ (ls : List ι) (G : (ι → ℕ) → ℝ≥0∞),
    poisList a ls (pois b j G) = pois b j (poisList a ls G)
  | [], _ => rfl
  | l :: ls, G => by
      simp only [poisList]
      rw [show pois a l (pois b j G) = pois b j (pois a l G) from funext fun x => pois_comm a b l j G x]
      exact poisList_pois a b j ls _

theorem poisList_poisList (a b : ℝ≥0) : ∀ (ls : List ι) (G : (ι → ℕ) → ℝ≥0∞),
    poisList a ls (poisList b ls G) = poisList (a + b) ls G
  | [], _ => rfl
  | l :: ls, G => by
      simp only [poisList]
      rw [← poisList_pois b a l ls,
        show pois a l (pois b l G) = pois (a + b) l G from funext fun x => pois_pois a b l G x]
      exact poisList_poisList a b ls _

theorem le_poisList_of_le {G H : (ι → ℕ) → ℝ≥0∞} (a : ℝ≥0) (ls : List ι) (hH : Monotone H)
    (h : ∀ k, G k ≤ H k) : ∀ k, G k ≤ poisList a ls H k := by
  induction ls generalizing H with
  | nil => exact h
  | cons l ls ih =>
      have hmono : Monotone (pois a l H) := fun k k' hk =>
        ENNReal.tsum_le_tsum fun _ => by gcongr; exact hH (add_le_add_left hk _)
      exact ih hmono fun k => le_trans (h k) (le_pois a l hH k)

/-- **Semigroup** of iid Poisson coordinates. -/
theorem poisIID_poisIID (a b : ℝ≥0) (G : (ι → ℕ) → ℝ≥0∞) :
    poisIID a (poisIID b G) = poisIID (a + b) G :=
  poisList_poisList a b _ G

theorem poisIID_zero_rate (G : (ι → ℕ) → ℝ≥0∞) : poisIID 0 G = G := poisList_zero_rate _ G

/-- Iid Poisson means of a monotone function grow with the rate. -/
theorem poisIID_mono_rate {G : (ι → ℕ) → ℝ≥0∞} (hG : Monotone G) {a b : ℝ≥0} (hab : a ≤ b) (k : ι → ℕ) :
    poisIID a G k ≤ poisIID b G k := by
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp hab
  rw [← poisIID_poisIID]
  exact poisList_mono a _ (le_poisList_of_le c _ hG fun _ => le_rfl) k

/-! ### Good count functions -/

/-- A good count function: monotone, with increasing differences across coordinates and along each
coordinate, and at most exponential growth. -/
structure CountGood (G : (ι → ℕ) → ℝ≥0∞) : Prop where
  mono : Monotone G
  super : ∀ k i j, i ≠ j →
    G (k + Pi.single i 1) + G (k + Pi.single j 1) ≤ G (k + Pi.single i 1 + Pi.single j 1) + G k
  convex : ∀ k i, G (k + Pi.single i 1) + G (k + Pi.single i 1) ≤ G (k + Pi.single i 1 + Pi.single i 1) + G k
  growth : ∃ C r : ℝ≥0, ∀ k, G k ≤ (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (∑ l, k l)

theorem CountGood.ne_top {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (k : ι → ℕ) : G k ≠ ⊤ := by
  obtain ⟨C, r, h⟩ := hG.growth
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)) (h k)

theorem sum_add_single (k : ι → ℕ) (l : ι) (n : ℕ) : ∑ i, (k + Pi.single l n : ι → ℕ) i = ∑ i, k i + n := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]

theorem CountGood.pois {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (a : ℝ≥0) (l : ι) : CountGood (pois a l G) where
  mono := fun k k' hk => ENNReal.tsum_le_tsum fun _ => by gcongr; exact hG.mono (add_le_add_left hk _)
  super := by
    intro k i j hij
    unfold H0.pois
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_right ?_ _
    have h := hG.super (k + Pi.single l n) i j hij
    simp only [add_right_comm _ (Pi.single l n : ι → ℕ)] at h ⊢
    exact h
  convex := by
    intro k i
    unfold H0.pois
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_right ?_ _
    have h := hG.convex (k + Pi.single l n) i
    simp only [add_right_comm _ (Pi.single l n : ι → ℕ)] at h ⊢
    exact h
  growth := by
    obtain ⟨C, r, h⟩ := hG.growth
    refine ⟨C * Real.toNNReal (Real.exp ((a : ℝ) * r - a)), r, fun k => ?_⟩
    calc H0.pois a l G k ≤ ∑' n, poisW a n * ((C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (∑ i, k i + n)) :=
          ENNReal.tsum_le_tsum fun n => by gcongr; rw [← sum_add_single k l n]; exact h _
      _ = (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (∑ i, k i) * ∑' n, poisW a n * (r : ℝ≥0∞) ^ n := by
          rw [← ENNReal.tsum_mul_left]
          congr 1; funext n; rw [pow_add]; ring
      _ = _ := by
          rw [poisW_mul_pow, ENNReal.ofReal, ENNReal.coe_mul]
          ring

theorem CountGood.poisList (a : ℝ≥0) : ∀ (ls : List ι) {G : (ι → ℕ) → ℝ≥0∞}, CountGood G → CountGood (poisList a ls G)
  | [], _, hG => hG
  | l :: ls, _, hG => CountGood.poisList a ls (hG.pois a l)

theorem CountGood.poisIID {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (a : ℝ≥0) : CountGood (poisIID a G) :=
  CountGood.poisList a _ hG

theorem CountGood.shift {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (e : ι → ℕ) : CountGood (fun k => G (k + e)) where
  mono := fun k k' hk => hG.mono (add_le_add_left hk _)
  super := by
    intro k i j hij
    have h := hG.super (k + e) i j hij
    simp only [add_right_comm _ e] at h ⊢
    exact h
  convex := by
    intro k i
    have h := hG.convex (k + e) i
    simp only [add_right_comm _ e] at h ⊢
    exact h
  growth := by
    obtain ⟨C, r, h⟩ := hG.growth
    refine ⟨C * (r + 1) ^ (∑ l, e l), r + 1, fun k => ?_⟩
    calc G (k + e) ≤ (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (∑ l, (k + e) l) := h _
      _ ≤ (C : ℝ≥0∞) * ((r : ℝ≥0∞) + 1) ^ (∑ l, (k + e) l) := by gcongr; exact le_self_add
      _ = _ := by
          simp only [Pi.add_apply, Finset.sum_add_distrib, pow_add]
          push_cast
          ring

/-- Mixtures of good functions are good. -/
theorem CountGood.mix {G H : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (hH : CountGood H) {p : ℝ≥0∞} (hp : p ≤ 1) :
    CountGood (fun k => p * G k + (1 - p) * H k) where
  mono := fun k k' hk => add_le_add (mul_le_mul_right (hG.mono hk) _) (mul_le_mul_right (hH.mono hk) _)
  super := by
    intro k i j hij
    have h1 := hG.super k i j hij
    have h2 := hH.super k i j hij
    calc p * G (k + Pi.single i 1) + (1 - p) * H (k + Pi.single i 1) +
          (p * G (k + Pi.single j 1) + (1 - p) * H (k + Pi.single j 1))
        = p * (G (k + Pi.single i 1) + G (k + Pi.single j 1)) +
          (1 - p) * (H (k + Pi.single i 1) + H (k + Pi.single j 1)) := by ring
      _ ≤ p * (G (k + Pi.single i 1 + Pi.single j 1) + G k) +
          (1 - p) * (H (k + Pi.single i 1 + Pi.single j 1) + H k) := by gcongr
      _ = _ := by ring
  convex := by
    intro k i
    have h1 := hG.convex k i
    have h2 := hH.convex k i
    calc p * G (k + Pi.single i 1) + (1 - p) * H (k + Pi.single i 1) +
          (p * G (k + Pi.single i 1) + (1 - p) * H (k + Pi.single i 1))
        = p * (G (k + Pi.single i 1) + G (k + Pi.single i 1)) +
          (1 - p) * (H (k + Pi.single i 1) + H (k + Pi.single i 1)) := by ring
      _ ≤ p * (G (k + Pi.single i 1 + Pi.single i 1) + G k) +
          (1 - p) * (H (k + Pi.single i 1 + Pi.single i 1) + H k) := by gcongr
      _ = _ := by ring
  growth := by
    obtain ⟨C, r, h⟩ := hG.growth
    obtain ⟨C', r', h'⟩ := hH.growth
    refine ⟨C + C', max r r', fun k => ?_⟩
    have hp' : 1 - p ≤ 1 := tsub_le_self
    calc p * G k + (1 - p) * H k ≤ 1 * ((C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (∑ l, k l)) +
          1 * ((C' : ℝ≥0∞) * (r' : ℝ≥0∞) ^ (∑ l, k l)) := by gcongr <;> [exact h k; exact h' k]
      _ ≤ (C : ℝ≥0∞) * ((max r r' : ℝ≥0) : ℝ≥0∞) ^ (∑ l, k l) +
          (C' : ℝ≥0∞) * ((max r r' : ℝ≥0) : ℝ≥0∞) ^ (∑ l, k l) := by
          rw [one_mul, one_mul]
          gcongr
          · exact_mod_cast le_max_left r r'
          · exact_mod_cast le_max_right r r'
      _ = _ := by push_cast; ring

/-! ### The chord: a Bernoulli coin is below a Poisson coordinate of the same mean -/

theorem good_incr {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (k : ι → ℕ) (l : ι) :
    ∀ n, G (k + Pi.single l n) + G (k + Pi.single l 1) ≤ G (k + Pi.single l (n + 1)) + G k
  | 0 => by simp [add_comm]
  | n + 1 => by
      have ih := good_incr hG k l n
      have hc := hG.convex (k + Pi.single l n) l
      simp only [add_assoc, ← Pi.single_add] at hc
      have hfin : G (k + Pi.single l n) + G (k + Pi.single l (n + 1)) ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hG.ne_top _, hG.ne_top _⟩
      refine (ENNReal.add_le_add_iff_right hfin).1 ?_
      calc G (k + Pi.single l (n + 1)) + G (k + Pi.single l 1) + (G (k + Pi.single l n) + G (k + Pi.single l (n + 1)))
          = (G (k + Pi.single l (n + 1)) + G (k + Pi.single l (n + 1))) +
            (G (k + Pi.single l n) + G (k + Pi.single l 1)) := by ring
        _ ≤ (G (k + Pi.single l (n + 1 + 1)) + G (k + Pi.single l n)) +
            (G (k + Pi.single l (n + 1)) + G k) := add_le_add hc ih
        _ = _ := by ring

theorem good_chord_point {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (k : ι → ℕ) (l : ι) :
    ∀ n : ℕ, G k + (n : ℝ≥0∞) * G (k + Pi.single l 1) ≤ G (k + Pi.single l n) + (n : ℝ≥0∞) * G k
  | 0 => by simp
  | n + 1 => by
      have ih := good_chord_point hG k l n
      have hi := good_incr hG k l n
      push_cast
      calc G k + ((n : ℝ≥0∞) + 1) * G (k + Pi.single l 1)
          = (G k + (n : ℝ≥0∞) * G (k + Pi.single l 1)) + G (k + Pi.single l 1) := by ring
        _ ≤ (G (k + Pi.single l n) + (n : ℝ≥0∞) * G k) + G (k + Pi.single l 1) := by gcongr
        _ = (G (k + Pi.single l n) + G (k + Pi.single l 1)) + (n : ℝ≥0∞) * G k := by ring
        _ ≤ (G (k + Pi.single l (n + 1)) + G k) + (n : ℝ≥0∞) * G k := by gcongr
        _ = _ := by ring

/-- **Chord.** `G(k) + a G(k + e_l) ≤ Pois_l(a) G (k) + a G(k)`. -/
theorem good_chord {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (a : ℝ≥0) (l : ι) (k : ι → ℕ) :
    G k + (a : ℝ≥0∞) * G (k + Pi.single l 1) ≤ pois a l G k + (a : ℝ≥0∞) * G k := by
  have h := ENNReal.tsum_le_tsum fun n => mul_le_mul_right (good_chord_point hG k l n) (poisW a n)
  simp only [mul_add, ENNReal.tsum_add] at h
  rw [ENNReal.tsum_mul_right, poisW_tsum, one_mul] at h
  simp only [← mul_assoc, ENNReal.tsum_mul_right, poisW_mean] at h
  exact h

/-- Increments along `l` grow with the Poisson count at `j ≠ l`. -/
theorem good_cross_point {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (k : ι → ℕ) {l j : ι} (hlj : l ≠ j) :
    ∀ n : ℕ, G (k + Pi.single j n) + G (k + Pi.single l 1) ≤ G (k + Pi.single l 1 + Pi.single j n) + G k
  | 0 => by simp [add_comm]
  | n + 1 => by
      have ih := good_cross_point hG k hlj n
      have hs := hG.super (k + Pi.single j n) l j hlj
      have e1 : k + Pi.single j n + Pi.single l 1 + Pi.single j 1 = k + Pi.single l 1 + Pi.single j (n + 1) := by
        rw [Pi.single_add]; abel
      have e2 : k + Pi.single j n + Pi.single j 1 = k + Pi.single j (n + 1) := by
        rw [Pi.single_add]; abel
      have e3 : k + Pi.single j n + Pi.single l 1 = k + Pi.single l 1 + Pi.single j n := by abel
      rw [e1, e2, e3] at hs
      have hfin : G (k + Pi.single l 1 + Pi.single j n) + G (k + Pi.single j n) ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hG.ne_top _, hG.ne_top _⟩
      refine (ENNReal.add_le_add_iff_right hfin).1 ?_
      calc G (k + Pi.single j (n + 1)) + G (k + Pi.single l 1) +
            (G (k + Pi.single l 1 + Pi.single j n) + G (k + Pi.single j n))
          = (G (k + Pi.single l 1 + Pi.single j n) + G (k + Pi.single j (n + 1))) +
            (G (k + Pi.single j n) + G (k + Pi.single l 1)) := by ring
        _ ≤ (G (k + Pi.single l 1 + Pi.single j (n + 1)) + G (k + Pi.single j n)) +
            (G (k + Pi.single l 1 + Pi.single j n) + G k) := add_le_add hs ih
        _ = _ := by ring

theorem good_cross {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (a : ℝ≥0) {l j : ι} (hlj : l ≠ j) (k : ι → ℕ) :
    pois a j G k + G (k + Pi.single l 1) ≤ pois a j G (k + Pi.single l 1) + G k := by
  have h := ENNReal.tsum_le_tsum fun n => mul_le_mul_right (good_cross_point hG k hlj n) (poisW a n)
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, poisW_tsum, one_mul] at h
  exact h

/-! ### Uniform-or-nothing slots against iid Poisson coordinates -/

theorem list_cross_sum {ι' : Type} (f g : ι' → ℝ≥0∞) (c d : ℝ≥0∞) :
    ∀ ls : List ι', (∀ j ∈ ls, d + g j ≤ f j + c) →
      (ls.length : ℝ≥0∞) * d + (ls.map g).sum ≤ (ls.map f).sum + (ls.length : ℝ≥0∞) * c
  | [], _ => by simp
  | j :: ls, h => by
      have ih := list_cross_sum f g c d ls fun i hi => h i (List.mem_cons_of_mem _ hi)
      have hj := h j List.mem_cons_self
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      push_cast
      calc ((ls.length : ℝ≥0∞) + 1) * d + (g j + (ls.map g).sum)
          = (d + g j) + ((ls.length : ℝ≥0∞) * d + (ls.map g).sum) := by ring
        _ ≤ (f j + c) + ((ls.map f).sum + (ls.length : ℝ≥0∞) * c) := add_le_add hj ih
        _ = _ := by ring

/-- **Several coordinates.** `G + a Σ_l G(· + e_l) ≤ P_ls(a) G + |ls| a G`. -/
theorem poisList_lower (a : ℝ≥0) :
    ∀ (ls : List ι), ls.Nodup → ∀ {G : (ι → ℕ) → ℝ≥0∞}, CountGood G → ∀ k,
      G k + (a : ℝ≥0∞) * (ls.map fun l => G (k + Pi.single l 1)).sum ≤
        poisList a ls G k + ((ls.length : ℝ≥0∞) * a) * G k
  | [], _, _, _, k => by simp [poisList]
  | l :: ls, hnd, G, hG, k => by
      rw [List.nodup_cons] at hnd
      have hG' := hG.pois a l
      have ih := poisList_lower a ls hnd.2 hG' k
      have hch := good_chord hG a l k
      have hcr := list_cross_sum (fun j => H0.pois a l G (k + Pi.single j 1)) (fun j => G (k + Pi.single j 1))
        (G k) (H0.pois a l G k) ls fun j hj =>
          good_cross hG a (fun h => hnd.1 (by rw [← h]; exact hj)) k
      have hcr' := mul_le_mul_right hcr (a : ℝ≥0∞)
      set X := H0.pois a l G k + (a : ℝ≥0∞) * (ls.map fun j => H0.pois a l G (k + Pi.single j 1)).sum +
        (a : ℝ≥0∞) * ((ls.length : ℝ≥0∞) * H0.pois a l G k) with hX
      have hXfin : X ≠ ⊤ := by
        refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hG'.ne_top _, ?_⟩, ?_⟩
        · refine ENNReal.mul_ne_top ENNReal.coe_ne_top (list_sum_ne_top _ ?_)
          intro v hv
          obtain ⟨j, _, rfl⟩ := List.mem_map.1 hv
          exact hG'.ne_top _
        · exact ENNReal.mul_ne_top ENNReal.coe_ne_top
            (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hG'.ne_top _))
      simp only [poisList, List.map_cons, List.sum_cons, List.length_cons]
      refine (ENNReal.add_le_add_iff_right hXfin).1 ?_
      have hsum := add_le_add (add_le_add ih hch) hcr'
      calc G k + (a : ℝ≥0∞) * (G (k + Pi.single l 1) + (ls.map fun j => G (k + Pi.single j 1)).sum) + X
          = (H0.pois a l G k + (a : ℝ≥0∞) * (ls.map fun j => H0.pois a l G (k + Pi.single j 1)).sum) +
              (G k + (a : ℝ≥0∞) * G (k + Pi.single l 1)) +
              (a : ℝ≥0∞) * ((ls.length : ℝ≥0∞) * H0.pois a l G k +
                (ls.map fun j => G (k + Pi.single j 1)).sum) := by
            rw [hX]; ring
        _ ≤ (poisList a ls (H0.pois a l G) k + ((ls.length : ℝ≥0∞) * a) * H0.pois a l G k) +
              (H0.pois a l G k + (a : ℝ≥0∞) * G k) +
              (a : ℝ≥0∞) * ((ls.map fun j => H0.pois a l G (k + Pi.single j 1)).sum +
                (ls.length : ℝ≥0∞) * G k) := hsum
        _ = _ := by
            rw [hX]; push_cast; ring

/-- **Uniform-or-nothing slot.** With `L a ≤ 1`, a slot that adds one uniform coordinate with
probability `L a` is below iid `Poisson(a)` coordinates. -/
theorem slot_le_poisIID {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) (a : ℝ≥0)
    (ha : (Fintype.card ι : ℝ≥0∞) * a ≤ 1) (k : ι → ℕ) :
    (1 - (Fintype.card ι : ℝ≥0∞) * a) * G k + (a : ℝ≥0∞) * ∑ l, G (k + Pi.single l 1) ≤ poisIID a G k := by
  have h := poisList_lower a (Finset.univ : Finset ι).toList (Finset.nodup_toList _) hG k
  rw [Finset.sum_map_toList, Finset.length_toList, Finset.card_univ] at h
  have hfin : ((Fintype.card ι : ℝ≥0∞) * a) * G k ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top) (hG.ne_top k)
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc (1 - (Fintype.card ι : ℝ≥0∞) * a) * G k + (a : ℝ≥0∞) * ∑ l, G (k + Pi.single l 1) +
        ((Fintype.card ι : ℝ≥0∞) * a) * G k
      = ((1 - (Fintype.card ι : ℝ≥0∞) * a) + (Fintype.card ι : ℝ≥0∞) * a) * G k +
          (a : ℝ≥0∞) * ∑ l, G (k + Pi.single l 1) := by ring
    _ = G k + (a : ℝ≥0∞) * ∑ l, G (k + Pi.single l 1) := by rw [tsub_add_cancel_of_le ha, one_mul]
    _ ≤ _ := h

/-! ### Bernoulli coins on count functions -/

/-- A coin of probability `p` adding one count to coordinate `l`. -/
noncomputable def coinC (p : ℝ≥0∞) (l : ι) (G : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ) : ℝ≥0∞ :=
  p * G (k + Pi.single l 1) + (1 - p) * G k

/-- Independent coins of probability `w`, one per listed coordinate (the first one outermost). -/
noncomputable def coinsList (w : ℝ≥0∞) : List ι → ((ι → ℕ) → ℝ≥0∞) → (ι → ℕ) → ℝ≥0∞
  | [], G => G
  | l :: ls, G => coinC w l (coinsList w ls G)

theorem pois_coinC (a : ℝ≥0) (j : ι) (p : ℝ≥0∞) (l : ι) (G : (ι → ℕ) → ℝ≥0∞) (k : ι → ℕ) :
    pois a j (coinC p l G) k = coinC p l (pois a j G) k := by
  unfold coinC
  rw [pois_add, pois_const_mul, pois_const_mul, pois_shift]

theorem poisList_coinC (a : ℝ≥0) (p : ℝ≥0∞) (l : ι) : ∀ (ls : List ι) (G : (ι → ℕ) → ℝ≥0∞),
    poisList a ls (coinC p l G) = coinC p l (poisList a ls G)
  | [], _ => rfl
  | j :: ls, G => by
      simp only [poisList]
      rw [show H0.pois a j (coinC p l G) = coinC p l (H0.pois a j G) from funext fun x => pois_coinC a j p l G x]
      exact poisList_coinC a p l ls _

theorem poisList_coinsList (a : ℝ≥0) (w : ℝ≥0∞) (ls : List ι) :
    ∀ (items : List ι) (G : (ι → ℕ) → ℝ≥0∞),
      poisList a ls (coinsList w items G) = coinsList w items (poisList a ls G)
  | [], _ => rfl
  | l :: items, G => by
      simp only [coinsList]
      rw [poisList_coinC, poisList_coinsList a w ls items G]

theorem CountGood.coinC {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) {p : ℝ≥0∞} (hp : p ≤ 1) (l : ι) : CountGood (coinC p l G) where
  mono := fun k k' hk => by
    unfold H0.coinC
    gcongr
    · exact hG.mono (add_le_add_left hk _)
    · exact hG.mono hk
  super := by
    intro k i j hij
    unfold H0.coinC
    have h1 := hG.super (k + Pi.single l 1) i j hij
    have h2 := hG.super k i j hij
    simp only [add_right_comm _ (Pi.single l 1 : ι → ℕ)] at h1
    calc p * G (k + Pi.single i 1 + Pi.single l 1) + (1 - p) * G (k + Pi.single i 1) +
          (p * G (k + Pi.single j 1 + Pi.single l 1) + (1 - p) * G (k + Pi.single j 1))
        = p * (G (k + Pi.single i 1 + Pi.single l 1) + G (k + Pi.single j 1 + Pi.single l 1)) +
          (1 - p) * (G (k + Pi.single i 1) + G (k + Pi.single j 1)) := by ring
      _ ≤ p * (G (k + Pi.single i 1 + Pi.single j 1 + Pi.single l 1) + G (k + Pi.single l 1)) +
          (1 - p) * (G (k + Pi.single i 1 + Pi.single j 1) + G k) := by gcongr
      _ = _ := by ring
  convex := by
    intro k i
    unfold H0.coinC
    have h1 := hG.convex (k + Pi.single l 1) i
    have h2 := hG.convex k i
    simp only [add_right_comm _ (Pi.single l 1 : ι → ℕ)] at h1
    calc p * G (k + Pi.single i 1 + Pi.single l 1) + (1 - p) * G (k + Pi.single i 1) +
          (p * G (k + Pi.single i 1 + Pi.single l 1) + (1 - p) * G (k + Pi.single i 1))
        = p * (G (k + Pi.single i 1 + Pi.single l 1) + G (k + Pi.single i 1 + Pi.single l 1)) +
          (1 - p) * (G (k + Pi.single i 1) + G (k + Pi.single i 1)) := by ring
      _ ≤ p * (G (k + Pi.single i 1 + Pi.single i 1 + Pi.single l 1) + G (k + Pi.single l 1)) +
          (1 - p) * (G (k + Pi.single i 1 + Pi.single i 1) + G k) := by gcongr
      _ = _ := by ring
  growth := by
    obtain ⟨C, r, h⟩ := hG.growth
    refine ⟨C * (r + 1), r, fun k => ?_⟩
    unfold H0.coinC
    have hp' : 1 - p ≤ 1 := tsub_le_self
    calc p * G (k + Pi.single l 1) + (1 - p) * G k
        ≤ 1 * ((C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (∑ i, k i + 1)) + 1 * ((C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (∑ i, k i)) := by
          gcongr
          · rw [← sum_add_single k l 1]; exact h _
          · exact h _
      _ = _ := by
          push_cast
          rw [pow_succ]
          ring

theorem CountGood.coinsList {G : (ι → ℕ) → ℝ≥0∞} (hG : CountGood G) {w : ℝ≥0∞} (hw : w ≤ 1) :
    ∀ items : List ι, CountGood (coinsList w items G)
  | [] => hG
  | l :: items => (CountGood.coinsList hG hw items).coinC hw l

/-! ### From views to counts -/

variable {V : Type} (idx : V → ι)

theorem cnt_add_single_fun (d : Multiset V) (u : V) :
    cnt idx (d + {u}) = cnt idx d + Pi.single (idx u) 1 := by
  funext l
  rw [cnt_add_single, Pi.add_apply, Pi.single_apply]
  by_cases h : idx u = l
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem cnt_zero_fun : cnt idx (0 : Multiset V) = 0 := by
  funext l; exact cnt_zero idx l

/-- Coins on items are coins on their coordinates. -/
theorem slotValue_cnt (G : (ι → ℕ) → ℝ≥0∞) (w : ℝ≥0∞) :
    ∀ (items : List V) (d : Multiset V),
      slotValue (fun e => G (cnt idx e)) d (itemCoins w items) = coinsList w (items.map idx) G (cnt idx d)
  | [], _ => rfl
  | v :: rest, d => by
      rw [itemCoins_cons]
      simp only [slotValue, List.map_cons, coinsList, coinC]
      rw [slotValue_cnt G w rest (d + {v}), slotValue_cnt G w rest d, cnt_add_single_fun]

/-! ### Fresh slots, coins and creations -/

/-- **Fresh slots.** `m` fresh uniform disclosures are below iid `Poisson(m/L)` counts. -/
theorem fresh_le_poisIID (U : Finset V) (hU : UniformIndex idx U) {F : (ι → ℕ) → ℝ≥0∞} (hF : CountGood F)
    (α : ℝ≥0) (hα : (Fintype.card ι : ℝ≥0∞) * α = 1) :
    ∀ (m : ℕ) (d : Multiset V), fresh U (fun e => F (cnt idx e)) m d ≤ poisIID ((m : ℝ≥0) * α) F (cnt idx d)
  | 0, d => by
      simp only [fresh, Nat.cast_zero, zero_mul, poisIID_zero_rate]
      exact le_rfl
  | m + 1, d => by
      set Q := poisIID ((m : ℝ≥0) * α) F with hQ
      have hQg : CountGood Q := hF.poisIID _
      have hαinv : ((Fintype.card ι : ℝ≥0∞))⁻¹ = (α : ℝ≥0∞) :=
        (ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hα)).symm
      simp only [fresh]
      calc freshAvg U (fun u => fresh U (fun e => F (cnt idx e)) m (d + {u}))
          ≤ freshAvg U (fun u => (fun l => Q (cnt idx d + Pi.single l 1)) (idx u)) :=
            freshAvg_mono U fun u _ => by
              have h := fresh_le_poisIID U hU hF α hα m (d + {u})
              rw [cnt_add_single_fun] at h
              exact h
        _ = (α : ℝ≥0∞) * ∑ l, Q (cnt idx d + Pi.single l 1) :=
            (hU (fun l => Q (cnt idx d + Pi.single l 1))).trans (by rw [hαinv])
        _ = (1 - (Fintype.card ι : ℝ≥0∞) * α) * Q (cnt idx d) + (α : ℝ≥0∞) * ∑ l, Q (cnt idx d + Pi.single l 1) := by
            rw [hα, tsub_self, zero_mul, zero_add]
        _ ≤ poisIID α Q (cnt idx d) := slot_le_poisIID hQg α hα.le _
        _ = poisIID (((m + 1 : ℕ) : ℝ≥0) * α) F (cnt idx d) := by
            rw [hQ, poisIID_poisIID]
            congr 2
            push_cast
            ring

theorem one_sub_add_mul_one_sub {lam w : ℝ≥0∞} (hlam : lam ≤ 1) (hw : w ≤ 1) :
    (1 - lam) + lam * (1 - w) = 1 - lam * w := by
  have hl : lam ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hlam
  have hw' : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw
  have hlw : lam * w ≤ 1 := mul_le_one' hlam hw
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_sub_of_le hlam ENNReal.one_ne_top, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hw ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le hlw ENNReal.one_ne_top, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_one]
  ring

/-- One creation step: an item with a uniform view with probability `λ`, whose coin has
probability `w`, is below iid `Poisson(λ w / L)` counts. -/
theorem creation_step_pois (U : Finset V) (hU : UniformIndex idx U) {H : (ι → ℕ) → ℝ≥0∞} (hH : CountGood H)
    (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (γ : ℝ≥0) (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hγ : (Fintype.card ι : ℝ≥0∞) * γ = lam * w) :
    (1 - lam) * H 0 + lam * freshAvg U (fun v => coinC w (idx v) H 0) ≤ poisIID γ H 0 := by
  set L : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) with hLdef
  have hLT : L ≠ ⊤ := ENNReal.natCast_ne_top _
  have hA : freshAvg U (fun v => coinC w (idx v) H 0) =
      L⁻¹ * (w * ∑ l, H (0 + Pi.single l 1)) + (1 - w) * H 0 := by
    refine (hU (fun l => coinC w l H 0)).trans ?_
    unfold coinC
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add,
      ← hLdef, ← mul_assoc L⁻¹ L, ENNReal.inv_mul_cancel hL hLT, one_mul]
  have hγ' : lam * L⁻¹ * w = (γ : ℝ≥0∞) := by
    calc lam * L⁻¹ * w = L⁻¹ * (lam * w) := by ring
      _ = L⁻¹ * (L * γ) := by rw [hγ]
      _ = γ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hL hLT, one_mul]
  have hlw : L * γ ≤ 1 := by rw [hγ]; exact mul_le_one' hlam hw
  rw [hA]
  calc (1 - lam) * H 0 + lam * (L⁻¹ * (w * ∑ l, H (0 + Pi.single l 1)) + (1 - w) * H 0)
      = ((1 - lam) + lam * (1 - w)) * H 0 + (lam * L⁻¹ * w) * ∑ l, H (0 + Pi.single l 1) := by ring
    _ = (1 - L * γ) * H 0 + (γ : ℝ≥0∞) * ∑ l, H (0 + Pi.single l 1) := by
        rw [one_sub_add_mul_one_sub hlam hw, hγ', hγ]
    _ ≤ poisIID γ H 0 := slot_le_poisIID hH γ hlw 0

/-- **Creations.** `j` future pairs, each an item with probability `λ` and a coin of probability
`w`, are below iid `Poisson(j λ w / L)` counts, for any items already present. -/
theorem creations_le_poisIID (U : Finset V) (hU : UniformIndex idx U) {Q : (ι → ℕ) → ℝ≥0∞} (hQ : CountGood Q)
    (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (γ : ℝ≥0) (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hγ : (Fintype.card ι : ℝ≥0∞) * γ = lam * w) :
    ∀ (j : ℕ) (items : List V),
      creations U lam (fun I => coinsList w (I.map idx) Q 0) j items ≤
        coinsList w (items.map idx) (poisIID ((j : ℝ≥0) * γ) Q) 0
  | 0, items => by
      simp only [creations, Nat.cast_zero, zero_mul, poisIID_zero_rate]
      exact le_rfl
  | j + 1, items => by
      set Qj := poisIID ((j : ℝ≥0) * γ) Q with hQj
      have hQjg : CountGood Qj := hQ.poisIID _
      set H := coinsList w (items.map idx) Qj with hHdef
      have hHg : CountGood H := hQjg.coinsList hw _
      have ih := creations_le_poisIID U hU hQ w lam hw hlam γ hL hγ j
      simp only [creations]
      calc (1 - lam) * creations U lam (fun I => coinsList w (I.map idx) Q 0) j items +
            lam * freshAvg U (fun v => creations U lam (fun I => coinsList w (I.map idx) Q 0) j (v :: items))
          ≤ (1 - lam) * H 0 + lam * freshAvg U (fun v => coinC w (idx v) H 0) := by
            gcongr
            · exact ih items
            · exact freshAvg_mono U fun v _ => ih (v :: items)
        _ ≤ poisIID γ H 0 := creation_step_pois idx U hU hHg w lam hw hlam γ hL hγ
        _ = coinsList w (items.map idx) (poisIID γ Qj) 0 := by
            rw [hHdef]; unfold poisIID; rw [poisList_coinsList]
        _ = _ := by
            rw [hQj, poisIID_poisIID]
            congr 3
            push_cast
            ring

/-- **Poisson domination of the one-coin H-term.** For a good count function `F`, the H-term of
`F ∘ cnt` (fresh slots at the uniform rate `α = 1/L`, one coin of probability `w` per future
pair, created with probability `λ`) is below the iid Poisson mean of `F` at rate `N α + q γ`,
`L γ = λ w`. -/
theorem hTermO_le_poisIID (U : Finset V) (hU : UniformIndex idx U) {F : (ι → ℕ) → ℝ≥0∞} (hF : CountGood F)
    (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (α γ : ℝ≥0) (hα : (Fintype.card ι : ℝ≥0∞) * α = 1)
    (hγ : (Fintype.card ι : ℝ≥0∞) * γ = lam * w) (N q : ℕ) :
    hTermO U w lam N q (fun d => F (cnt idx d)) ≤ poisIID ((N : ℝ≥0) * α + (q : ℝ≥0) * γ) F 0 := by
  have hL : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hα; exact zero_ne_one hα
  set Q := poisIID ((N : ℝ≥0) * α) F with hQ
  have hQg : CountGood Q := hF.poisIID _
  unfold hTermO
  calc creations U lam (fun I => virtualOnce U w (fun d => F (cnt idx d)) N I 0) q []
      ≤ creations U lam (fun I => coinsList w (I.map idx) Q 0) q [] := by
        refine creations_mono (fun I => ?_) q []
        unfold virtualOnce
        calc slotValue (fresh U (fun d => F (cnt idx d)) N) 0 (itemCoins w I)
            ≤ slotValue (fun e => Q (cnt idx e)) 0 (itemCoins w I) :=
              slotValue_le_of_le (fun e => fresh_le_poisIID idx U hU hF α hα N e) _ _
          _ = coinsList w (I.map idx) Q 0 := by rw [slotValue_cnt, cnt_zero_fun]
    _ ≤ coinsList w (([] : List V).map idx) (poisIID ((q : ℝ≥0) * γ) Q) 0 :=
        creations_le_poisIID idx U hU hQg w lam hw hlam γ hL hγ q []
    _ = poisIID ((N : ℝ≥0) * α + (q : ℝ≥0) * γ) F 0 := by
        simp only [List.map_nil, coinsList]
        rw [hQ, poisIID_poisIID, add_comm]

/-- The domination at any larger rate. -/
theorem hTermO_le_poisIID_of_le (U : Finset V) (hU : UniformIndex idx U) {F : (ι → ℕ) → ℝ≥0∞} (hF : CountGood F)
    (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (α γ : ℝ≥0) (hα : (Fintype.card ι : ℝ≥0∞) * α = 1)
    (hγ : (Fintype.card ι : ℝ≥0∞) * γ = lam * w) (N q : ℕ) (μ : ℝ≥0) (hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ) :
    hTermO U w lam N q (fun d => F (cnt idx d)) ≤ poisIID μ F 0 :=
  le_trans (hTermO_le_poisIID idx U hU hF w lam hw hlam α γ hα hγ N q) (poisIID_mono_rate hF.mono hμ 0)

end SphincsFors.Security.H0
