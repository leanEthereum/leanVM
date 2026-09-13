import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def binomialAverage (rate : ENNReal) : Nat → (Nat → ENNReal) → ENNReal
  | 0, f => f 0
  | steps + 1, f =>
      (1 - rate) * binomialAverage rate steps f +
        rate * binomialAverage rate steps (fun count => f (count + 1))

theorem binomialAverage_zero (rate : ENNReal) (f : Nat → ENNReal) :
    binomialAverage rate 0 f = f 0 := rfl

theorem binomialAverage_succ (rate : ENNReal) (steps : Nat) (f : Nat → ENNReal) :
    binomialAverage rate (steps + 1) f =
      (1 - rate) * binomialAverage rate steps f +
        rate * binomialAverage rate steps (fun count => f (count + 1)) := rfl

theorem binomialAverage_add (rate : ENNReal) (steps : Nat) (f g : Nat → ENNReal) :
    binomialAverage rate steps (fun count => f count + g count) =
      binomialAverage rate steps f + binomialAverage rate steps g := by
  induction steps generalizing f g with
  | zero => rfl
  | succ steps ih =>
      simp only [binomialAverage_succ, ih, mul_add]
      ac_rfl

theorem binomialAverage_mul_left (rate factor : ENNReal) (steps : Nat) (f : Nat → ENNReal) :
    binomialAverage rate steps (fun count => factor * f count) =
      factor * binomialAverage rate steps f := by
  induction steps generalizing f with
  | zero => rfl
  | succ steps ih =>
      simp only [binomialAverage_succ, ih]
      ring

theorem binomialAverage_mul_right (rate factor : ENNReal) (steps : Nat) (f : Nat → ENNReal) :
    binomialAverage rate steps (fun count => f count * factor) =
      binomialAverage rate steps f * factor := by
  simpa only [mul_comm] using binomialAverage_mul_left rate factor steps f

theorem binomialAverage_sum {α : Type*} (rate : ENNReal) (steps : Nat) (set : Finset α)
    (f : α → Nat → ENNReal) :
    binomialAverage rate steps (fun count => ∑ i ∈ set, f i count) =
      ∑ i ∈ set, binomialAverage rate steps (f i) := by
  induction steps generalizing f with
  | zero => rfl
  | succ steps ih =>
      simp only [binomialAverage_succ, ih, Finset.mul_sum, Finset.sum_add_distrib]

theorem binomialAverage_mono (rate : ENNReal) (steps : Nat) {f g : Nat → ENNReal}
    (h : ∀ count, f count ≤ g count) :
    binomialAverage rate steps f ≤ binomialAverage rate steps g := by
  induction steps generalizing f g with
  | zero => exact h 0
  | succ steps ih =>
      exact add_le_add (mul_le_mul' le_rfl (ih h))
        (mul_le_mul' le_rfl (ih (fun count => h (count + 1))))

theorem bernoulli_mix_increment {rate : ENNReal} (hrate : rate ≤ 1) (value increment : ENNReal) :
    (1 - rate) * value + rate * (value + increment) = value + rate * increment := by
  calc
    _ = (1 - rate + rate) * value + rate * increment := by ring
    _ = _ := by rw [tsub_add_cancel_of_le hrate, one_mul]

theorem binomialAverage_const {rate : ENNReal} (hrate : rate ≤ 1) (steps : Nat) (value : ENNReal) :
    binomialAverage rate steps (fun _ => value) = value := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [binomialAverage_succ, ih, ← add_mul, tsub_add_cancel_of_le hrate, one_mul]

theorem binomialAverage_choose {rate : ENNReal} (hrate : rate ≤ 1) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (count.choose degree : ENNReal)) =
      (steps.choose degree : ENNReal) * rate ^ degree := by
  induction steps generalizing degree with
  | zero =>
      cases degree <;> simp [binomialAverage_zero]
  | succ steps ih =>
      cases degree with
      | zero => simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, binomialAverage_const hrate]
      | succ degree =>
          rw [binomialAverage_succ]
          simp_rw [Nat.choose_succ_succ, Nat.cast_add]
          rw [binomialAverage_add]
          simp_rw [ih]
          rw [add_comm ((steps.choose degree : ENNReal) * rate ^ degree), bernoulli_mix_increment hrate]
          simp only [Nat.succ_eq_add_one, pow_succ]
          ring

theorem binomialAverage_descFactorial {rate : ENNReal} (hrate : rate ≤ 1) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (count.descFactorial degree : ENNReal)) =
      (steps.descFactorial degree : ENNReal) * rate ^ degree := by
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [binomialAverage_mul_left, binomialAverage_choose hrate]
  ring

theorem mul_descFactorial_eq (count degree : Nat) :
    count * count.descFactorial degree =
      count.descFactorial (degree + 1) + degree * count.descFactorial degree := by
  by_cases h : degree ≤ count
  · rw [Nat.descFactorial_succ, ← Nat.add_mul, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.mul_zero,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.mul_zero, Nat.add_zero]

theorem power_eq_stirling_descFactorial (count degree : Nat) :
    count ^ degree = ∑ order ∈ Finset.range (degree + 1),
      Nat.stirlingSecond degree order * count.descFactorial order := by
  induction degree with
  | zero => simp
  | succ degree ih =>
      rw [pow_succ, ih, Finset.sum_mul,
        Finset.sum_range_succ' (fun order => Nat.stirlingSecond (degree + 1) order * count.descFactorial order)]
      simp only [Nat.stirlingSecond_succ_zero, Nat.zero_mul, Nat.add_zero,
        Nat.stirlingSecond_succ_succ, Nat.add_mul, Finset.sum_add_distrib]
      have hshift :
          (∑ order ∈ Finset.range (degree + 1),
            (order + 1) * Nat.stirlingSecond degree (order + 1) * count.descFactorial (order + 1)) =
          ∑ order ∈ Finset.range (degree + 1),
            order * Nat.stirlingSecond degree order * count.descFactorial order := by
        let f := fun order => order * Nat.stirlingSecond degree order * count.descFactorial order
        change (∑ order ∈ Finset.range (degree + 1), f (order + 1)) =
          ∑ order ∈ Finset.range (degree + 1), f order
        calc
          _ = ∑ order ∈ Finset.range (degree + 2), f order := by
            simpa [f] using (Finset.sum_range_succ' f (degree + 1)).symm
          _ = _ := by
            rw [Finset.sum_range_succ]
            simp [f, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self degree)]
      simp only [Nat.add_mul, Finset.sum_add_distrib] at hshift
      rw [hshift, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro order _
      calc
        _ = Nat.stirlingSecond degree order * (count * count.descFactorial order) := by ring
        _ = _ := by rw [mul_descFactorial_eq]; ring

theorem binomialAverage_power {rate : ENNReal} (hrate : rate ≤ 1) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (count : ENNReal) ^ degree) =
      ∑ order ∈ Finset.range (degree + 1),
        (Nat.stirlingSecond degree order : ENNReal) *
          (steps.descFactorial order : ENNReal) * rate ^ order := by
  have hpower (count : Nat) : (count : ENNReal) ^ degree =
      ∑ order ∈ Finset.range (degree + 1),
        (Nat.stirlingSecond degree order : ENNReal) * (count.descFactorial order : ENNReal) := by
    exact_mod_cast power_eq_stirling_descFactorial count degree
  simp_rw [hpower]
  rw [binomialAverage_sum]
  apply Finset.sum_congr rfl
  intro order _
  rw [binomialAverage_mul_left, binomialAverage_descFactorial hrate]
  ring

theorem stirlingSecond_le_choose_mul_pow (degree order : Nat) :
    Nat.stirlingSecond degree order ≤ degree.choose order * degree ^ (degree - order) := by
  induction degree generalizing order with
  | zero => cases order <;> simp
  | succ degree ih =>
      cases order with
      | zero => simp
      | succ order =>
          by_cases hlt : order < degree
          · have hpow : (order + 1) * degree ^ (degree - (order + 1)) ≤
                (degree + 1) ^ (degree - order) := by
              calc
                _ ≤ (degree + 1) * (degree + 1) ^ (degree - (order + 1)) :=
                  Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (Nat.le_succ _) _)
                _ = _ := by
                  rw [← pow_succ']
                  congr 1
                  omega
            calc
              _ = (order + 1) * Nat.stirlingSecond degree (order + 1) +
                    Nat.stirlingSecond degree order := Nat.stirlingSecond_succ_succ _ _
              _ ≤ (order + 1) * (degree.choose (order + 1) * degree ^ (degree - (order + 1))) +
                    degree.choose order * degree ^ (degree - order) :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ (ih _)) (ih _)
              _ = degree.choose (order + 1) * ((order + 1) * degree ^ (degree - (order + 1))) +
                    degree.choose order * degree ^ (degree - order) := by ring
              _ ≤ degree.choose (order + 1) * (degree + 1) ^ (degree - order) +
                    degree.choose order * (degree + 1) ^ (degree - order) :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ hpow)
                    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _))
              _ = _ := by
                  rw [Nat.choose_succ_succ]
                  simp only [Nat.add_sub_add_right]
                  ring
          · by_cases heq : order = degree
            · subst order; simp [Nat.stirlingSecond_self]
            · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]
              exact Nat.zero_le _

theorem binomialAverage_power_le {rate : ENNReal} (hrate : rate ≤ 1) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (count : ENNReal) ^ degree) ≤
      ((steps : ENNReal) * rate + degree) ^ degree := by
  rw [binomialAverage_power hrate]
  calc
    _ ≤ ∑ order ∈ Finset.range (degree + 1),
        (degree.choose order : ENNReal) * (degree : ENNReal) ^ (degree - order) *
          ((steps : ENNReal) * rate) ^ order := by
      apply Finset.sum_le_sum
      intro order _
      have hc : (Nat.stirlingSecond degree order : ENNReal) ≤
          (degree.choose order : ENNReal) * (degree : ENNReal) ^ (degree - order) := by
        exact_mod_cast stirlingSecond_le_choose_mul_pow degree order
      have hf : (steps.descFactorial order : ENNReal) ≤ (steps : ENNReal) ^ order := by
        exact_mod_cast Nat.descFactorial_le_pow steps order
      apply (mul_le_mul' (mul_le_mul' hc hf) le_rfl).trans_eq
      rw [mul_pow]
      ring
    _ = _ := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro order _
      ring

theorem binomialAverage_shifted_power (rate shift : ENNReal) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (shift + count) ^ degree) =
      ∑ order ∈ Finset.range (degree + 1),
        (degree.choose order : ENNReal) * shift ^ (degree - order) *
          binomialAverage rate steps (fun count => (count : ENNReal) ^ order) := by
  have hpower (count : Nat) : (shift + count) ^ degree =
      ∑ order ∈ Finset.range (degree + 1),
        (degree.choose order : ENNReal) * shift ^ (degree - order) * (count : ENNReal) ^ order := by
    rw [add_comm shift, add_pow]
    apply Finset.sum_congr rfl
    intro order _
    ring
  simp_rw [hpower]
  rw [binomialAverage_sum]
  simp_rw [binomialAverage_mul_left]

theorem binomialAverage_shifted_power_le {rate : ENNReal} (hrate : rate ≤ 1)
    (shift : ENNReal) (steps degree : Nat) :
    binomialAverage rate steps (fun count => (shift + count) ^ degree) ≤
      (shift + steps * rate + degree) ^ degree := by
  rw [binomialAverage_shifted_power]
  calc
    _ ≤ ∑ order ∈ Finset.range (degree + 1),
        (degree.choose order : ENNReal) * shift ^ (degree - order) *
          ((steps : ENNReal) * rate + degree) ^ order := by
      apply Finset.sum_le_sum
      intro order horder
      have ho : order ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp horder)
      exact mul_le_mul' le_rfl ((binomialAverage_power_le hrate steps order).trans
        (pow_le_pow_left' (add_le_add le_rfl (Nat.cast_le.mpr ho)) _))
    _ = _ := by
      rw [show shift + steps * rate + degree = steps * rate + degree + shift by ac_rfl, add_pow]
      apply Finset.sum_congr rfl
      intro order _
      ring

theorem binomialAverage_power_mono_of_factorial {rate nextRate : ENNReal}
    (hrate : rate ≤ 1) (hnext : nextRate ≤ 1) (steps nextSteps degree : Nat)
    (hmoments : ∀ order, order ≤ degree →
      (steps.descFactorial order : ENNReal) * rate ^ order ≤
        (nextSteps.descFactorial order : ENNReal) * nextRate ^ order) :
    binomialAverage rate steps (fun count => (count : ENNReal) ^ degree) ≤
      binomialAverage nextRate nextSteps (fun count => (count : ENNReal) ^ degree) := by
  rw [binomialAverage_power hrate, binomialAverage_power hnext]
  apply Finset.sum_le_sum
  intro order horder
  simp only [mul_assoc]
  exact mul_le_mul' le_rfl (hmoments order (Nat.le_of_lt_succ (Finset.mem_range.mp horder)))

theorem binomialAverage_shifted_power_mono_of_factorial {rate nextRate shift nextShift : ENNReal}
    (hrate : rate ≤ 1) (hnext : nextRate ≤ 1) (hshift : shift ≤ nextShift)
    (steps nextSteps degree : Nat)
    (hmoments : ∀ order, order ≤ degree →
      (steps.descFactorial order : ENNReal) * rate ^ order ≤
        (nextSteps.descFactorial order : ENNReal) * nextRate ^ order) :
    binomialAverage rate steps (fun count => (shift + count) ^ degree) ≤
      binomialAverage nextRate nextSteps (fun count => (nextShift + count) ^ degree) := by
  apply (binomialAverage_mono rate steps (fun count =>
    pow_le_pow_left' (add_le_add hshift (le_rfl (a := (count : ENNReal)))) degree)).trans
  rw [binomialAverage_shifted_power, binomialAverage_shifted_power]
  apply Finset.sum_le_sum
  intro order horder
  apply mul_le_mul' le_rfl
  exact binomialAverage_power_mono_of_factorial hrate hnext steps nextSteps order
    (fun j hj => hmoments j (hj.trans (Nat.le_of_lt_succ (Finset.mem_range.mp horder))))

theorem mass_pow_le_descFactorial (mass : ENNReal) (count degree : Nat)
    (hroom : mass + degree ≤ ((count + 1 : Nat) : ENNReal)) :
    mass ^ degree ≤ (count.descFactorial degree : ENNReal) := by
  have hdegree : degree ≤ count + 1 := Nat.cast_le.mp ((le_add_left le_rfl).trans hroom)
  have hcancel : ((count + 1 - degree : Nat) : ENNReal) + degree = ((count + 1 : Nat) : ENNReal) := by
    exact_mod_cast Nat.sub_add_cancel hdegree
  have hmass : mass ≤ ((count + 1 - degree : Nat) : ENNReal) :=
    ENNReal.le_of_add_le_add_right (by finiteness) (hroom.trans_eq hcancel.symm)
  apply (pow_le_pow_left' hmass degree).trans
  exact_mod_cast Nat.pow_sub_le_descFactorial count degree

theorem binomialAverage_shifted_power_le_of_room {rate nextRate shift nextShift mass : ENNReal}
    (hrate : rate ≤ 1) (hnext : nextRate ≤ 1) (hshift : shift ≤ nextShift)
    (steps nextSteps degree : Nat)
    (hmean : (steps : ENNReal) * rate ≤ mass * nextRate)
    (hroom : mass + degree ≤ ((nextSteps + 1 : Nat) : ENNReal)) :
    binomialAverage rate steps (fun count => (shift + count) ^ degree) ≤
      binomialAverage nextRate nextSteps (fun count => (nextShift + count) ^ degree) := by
  apply binomialAverage_shifted_power_mono_of_factorial hrate hnext hshift steps nextSteps degree
  intro order horder
  have hfall : (steps.descFactorial order : ENNReal) ≤ (steps : ENNReal) ^ order := by
    exact_mod_cast Nat.descFactorial_le_pow steps order
  calc
    _ ≤ (steps : ENNReal) ^ order * rate ^ order := mul_le_mul' hfall le_rfl
    _ = ((steps : ENNReal) * rate) ^ order := (mul_pow _ _ _).symm
    _ ≤ (mass * nextRate) ^ order := pow_le_pow_left' hmean order
    _ = mass ^ order * nextRate ^ order := mul_pow _ _ _
    _ ≤ _ := mul_le_mul'
      (mass_pow_le_descFactorial mass nextSteps order
        ((add_le_add le_rfl (Nat.cast_le.mpr horder)).trans hroom)) le_rfl

end SphincsSecurity.Concrete
