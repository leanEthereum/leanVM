import SphincsFors.BridgeMix

/-! The exclusive group of one message under a signer that tries `R0, R0 + 1, ...`. A status
assigns to every randomizer `none` (unqueried), `some none` (queried, the digest does not land) or
`some (some v)` (queried, lands, view `v`). `grp σ ex h d` is the mean of the base function `h`
over the selection of the signer: a start absorbed by a known landed value discloses its view, an
unqueried start that is not absorbed discloses nothing here (the fresh slot of the signature pays
it), and a known non-landing start that is not absorbed is credited a fresh disclosed view: that
mass is what a scan can still turn into a known item. One more query raises the mean by at most
`(2 - p) / |R|` times the average gain of one disclosure. -/

open ENNReal

namespace SphincsFors.Security.Walk

open Domination

variable {R V : Type} [DecidableEq R] [DecidableEq V]

/-- Statuses of the randomizers of one message. -/
abbrev St (R V : Type) := R → Option (Option V)

/-- Stop weight. -/
noncomputable def sOf (p : ℝ≥0∞) (σ : St R V) (x : R) : ℝ≥0∞ :=
  match σ x with
  | none => p
  | some none => 0
  | some (some _) => 1

/-- Continuation weight. -/
noncomputable def tOf (p : ℝ≥0∞) (σ : St R V) (x : R) : ℝ≥0∞ :=
  match σ x with
  | none => 1 - p
  | some none => 1
  | some (some _) => 0

theorem sOf_add_tOf {p : ℝ≥0∞} (hp : p ≤ 1) (σ : St R V) (x : R) : sOf p σ x + tOf p σ x = 1 := by
  unfold sOf tOf
  rcases σ x with _ | _ | _
  · exact add_tsub_cancel_of_le hp
  · simp
  · simp

theorem sOf_ne_top {p : ℝ≥0∞} (hp : p ≤ 1) (σ : St R V) (x : R) : sOf p σ x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← sOf_add_tOf hp σ x]; exact le_self_add)

theorem tOf_ne_top {p : ℝ≥0∞} (hp : p ≤ 1) (σ : St R V) (x : R) : tOf p σ x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← sOf_add_tOf hp σ x]; exact le_add_self)

theorem tOf_le_one (p : ℝ≥0∞) (σ : St R V) (x : R) : tOf p σ x ≤ 1 := by
  unfold tOf
  rcases σ x with _ | _ | _
  · exact tsub_le_self
  · exact le_rfl
  · exact bot_le

/-- Payoff at a stop: a known landed value discloses its view, unless it is excluded. -/
noncomputable def pay (σ : St R V) (ex : R → Bool) (h : Multiset V → ℝ≥0∞) (d : Multiset V) (b : ℝ≥0∞)
    (x : R) : ℝ≥0∞ :=
  match σ x with
  | some (some v) => if ex x then h d else h (d + {v})
  | _ => b

theorem sOf_landed (p : ℝ≥0∞) (σ : St R V) (y : R) (v : V) :
    sOf p (Function.update σ y (some (some v))) = Function.update (sOf p σ) y 1 := by
  funext x
  by_cases hx : x = y
  · subst hx; simp [sOf]
  · simp [sOf, Function.update_of_ne hx]

theorem tOf_landed (p : ℝ≥0∞) (σ : St R V) (y : R) (v : V) :
    tOf p (Function.update σ y (some (some v))) = Function.update (tOf p σ) y 0 := by
  funext x
  by_cases hx : x = y
  · subst hx; simp [tOf]
  · simp [tOf, Function.update_of_ne hx]

theorem sOf_unlanded (p : ℝ≥0∞) (σ : St R V) (y : R) :
    sOf p (Function.update σ y (some none)) = Function.update (sOf p σ) y 0 := by
  funext x
  by_cases hx : x = y
  · subst hx; simp [sOf]
  · simp [sOf, Function.update_of_ne hx]

theorem tOf_unlanded (p : ℝ≥0∞) (σ : St R V) (y : R) :
    tOf p (Function.update σ y (some none)) = Function.update (tOf p σ) y 1 := by
  funext x
  by_cases hx : x = y
  · subst hx; simp [tOf]
  · simp [tOf, Function.update_of_ne hx]

theorem pay_landed (σ : St R V) (ex : R → Bool) (h : Multiset V → ℝ≥0∞) (d : Multiset V) (b : ℝ≥0∞) (y : R)
    (v : V) (hex : ex y = false) :
    pay (Function.update σ y (some (some v))) ex h d b = Function.update (pay σ ex h d b) y (h (d + {v})) := by
  funext x
  by_cases hx : x = y
  · subst hx; simp [pay, hex]
  · simp [pay, Function.update_of_ne hx]

theorem pay_unlanded (σ : St R V) (ex : R → Bool) (h : Multiset V → ℝ≥0∞) (d : Multiset V) (b : ℝ≥0∞) (y : R)
    (hy : σ y = none) : pay (Function.update σ y (some none)) ex h d b = pay σ ex h d b := by
  funext x
  by_cases hx : x = y
  · subst hx; simp [pay, hy]
  · simp [pay, Function.update_of_ne hx]

section Group

variable [Fintype R] [Nonempty R] [Fintype V] [Nonempty V] (e : R ≃ R) (p : ℝ≥0∞) (L : ℕ)

/-- What a start pays when no known landed value absorbs it. -/
noncomputable def baseOf (σ : St R V) (h : Multiset V → ℝ≥0∞) (d : Multiset V) (x0 : R) : ℝ≥0∞ :=
  if σ x0 = some none then avgT h d else h d

/-- The mean of `h` over the walk from one start. -/
noncomputable def grpAt (σ : St R V) (ex : R → Bool) (h : Multiset V → ℝ≥0∞) (d : Multiset V) (x0 : R) : ℝ≥0∞ :=
  val e (sOf p σ) (tOf p σ) (pay σ ex h d (baseOf σ h d x0)) (baseOf σ h d x0) L x0

/-- **The group of one message.** -/
noncomputable def grp (σ : St R V) (ex : R → Bool) (h : Multiset V → ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ :=
  ((Fintype.card R : ℕ) : ℝ≥0∞)⁻¹ * ∑ x0, grpAt e p L σ ex h d x0

variable {e p L}

theorem card_inv_ne_top : (((Fintype.card R : ℕ) : ℝ≥0∞))⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.2 (by exact_mod_cast Fintype.card_ne_zero)

theorem card_inv_mul_card : (((Fintype.card R : ℕ) : ℝ≥0∞))⁻¹ * ((Fintype.card R : ℕ) : ℝ≥0∞) = 1 :=
  ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

theorem rep_avgT : Rep (fun (h : Multiset V → ℝ≥0∞) d => avgT h d) := by
  have := Rep.freshAvg (Finset.univ : Finset V)
    (fun (v : V) (h : Multiset V → ℝ≥0∞) (d : Multiset V) => h (d + ({v} : Multiset V)))
    fun v => Rep.translate ({v} : Multiset V)
  exact this

theorem rep_grp (hp : p ≤ 1) (σ : St R V) (ex : R → Bool) : Rep (fun h d => grp e p L σ ex h d) := by
  refine (Rep.finset_sum Finset.univ (fun x0 h d => grpAt e p L σ ex h d x0) fun x0 => ?_).const_mul card_inv_ne_top
  have hbase : Rep (fun (h : Multiset V → ℝ≥0∞) d => baseOf σ h d x0) := by
    unfold baseOf
    split_ifs
    · exact rep_avgT
    · exact Rep.id
  refine rep_val e (sOf p σ) (tOf p σ) (sOf_ne_top hp σ) (tOf_ne_top hp σ)
    (fun h d => pay σ ex h d (baseOf σ h d x0)) (fun h d => baseOf σ h d x0) (fun x => ?_) hbase L x0
  unfold pay
  rcases σ x with _ | _ | v
  · exact hbase
  · exact hbase
  · simp only
    split_ifs
    · exact Rep.id
    · exact Rep.translate {v}

theorem le_baseOf {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h) (σ : St R V) (d : Multiset V) (x0 : R) :
    h d ≤ baseOf σ h d x0 := by
  unfold baseOf
  split_ifs
  · exact le_avgT hmono d
  · exact le_rfl

theorem le_pay {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h) (σ : St R V) (ex : R → Bool) (d : Multiset V)
    {b : ℝ≥0∞} (hb : h d ≤ b) (x : R) : h d ≤ pay σ ex h d b x := by
  unfold pay
  rcases σ x with _ | _ | v
  · exact hb
  · exact hb
  · simp only
    split_ifs
    · exact le_rfl
    · exact hmono _ _ (Multiset.le_add_right _ _)

theorem grp_const (hp : p ≤ 1) (σ : St R V) (ex : R → Bool) (K : ℝ≥0∞) (d : Multiset V) :
    grp e p L σ ex (fun _ => K) d = K := by
  have hat : ∀ x0, grpAt e p L σ ex (fun _ => K) d x0 = K := by
    intro x0
    have hb : baseOf σ (fun _ : Multiset V => K) d x0 = K := by
      unfold baseOf avgT
      split_ifs
      · exact freshAvg_const _ Finset.univ_nonempty K
      · rfl
    have hpay : pay σ ex (fun _ : Multiset V => K) d K = fun _ => K := by
      funext x
      unfold pay
      rcases σ x with _ | _ | v <;> simp
    unfold grpAt
    rw [hb, hpay]
    exact val_const e _ _ (sOf_add_tOf hp σ) K L x0
  unfold grp
  simp only [hat, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, card_inv_mul_card, one_mul]

theorem le_grp (hp : p ≤ 1) {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h) (σ : St R V) (ex : R → Bool)
    (d : Multiset V) : h d ≤ grp e p L σ ex h d := by
  have hat : ∀ x0, h d ≤ grpAt e p L σ ex h d x0 := fun x0 =>
    val_ge e _ _ (sOf_add_tOf hp σ) (le_pay hmono σ ex d (le_baseOf hmono σ d x0)) (le_baseOf hmono σ d x0) L x0
  unfold grp
  calc h d = ((Fintype.card R : ℕ) : ℝ≥0∞)⁻¹ * ∑ _x0 : R, h d := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← mul_assoc, card_inv_mul_card, one_mul]
    _ ≤ _ := mul_le_mul_right (Finset.sum_le_sum fun x0 _ => hat x0) _

/-- Excluding more known values lowers the mean. -/
theorem grp_ex_mono {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h) (σ : St R V) {ex ex' : R → Bool}
    (hex : ∀ x, ex x = true → ex' x = true) (d : Multiset V) : grp e p L σ ex' h d ≤ grp e p L σ ex h d := by
  unfold grp grpAt
  refine mul_le_mul_right (Finset.sum_le_sum fun x0 _ => val_mono e _ _ (fun x => ?_) le_rfl L x0) _
  unfold pay
  rcases σ x with _ | _ | v
  · exact le_rfl
  · exact le_rfl
  · simp only
    by_cases h1 : ex x
    · rw [ite_eq_left h1, ite_eq_left (hex x h1)]
    · rw [ite_eq_right h1]
      split_ifs
      · exact hmono _ _ (Multiset.le_add_right _ _)
      · exact le_rfl

/-- **Signing.** The base value, plus the gains of the known landed values weighted by their exact
selection probabilities, is at most the mean of the group. -/
theorem grp_ge_pool (hp : p ≤ 1) {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h) (σ : St R V) (ex : R → Bool)
    (d : Multiset V) :
    h d + ((Fintype.card R : ℕ) : ℝ≥0∞)⁻¹ * ∑ x0, val e (sOf p σ) (tOf p σ)
        (fun x => match σ x with
          | some (some v) => if ex x then 0 else gain h d v
          | _ => 0) 0 L x0 ≤
      grp e p L σ ex h d := by
  set gp : R → ℝ≥0∞ := fun x => match σ x with
    | some (some v) => if ex x then 0 else gain h d v
    | _ => 0 with hgp
  have hat : ∀ x0, h d + val e (sOf p σ) (tOf p σ) gp 0 L x0 ≤ grpAt e p L σ ex h d x0 := by
    intro x0
    have h1 : h d + val e (sOf p σ) (tOf p σ) gp 0 L x0 =
        val e (sOf p σ) (tOf p σ) (fun z => h d + gp z) (h d + 0) L x0 := by
      rw [val_add, val_const e _ _ (sOf_add_tOf hp σ)]
    rw [h1]
    unfold grpAt
    refine val_mono e _ _ (fun x => ?_) (by rw [add_zero]; exact le_baseOf hmono σ d x0) L x0
    simp only [hgp]
    unfold pay
    rcases σ x with _ | _ | v
    · rw [add_zero]; exact le_baseOf hmono σ d x0
    · rw [add_zero]; exact le_baseOf hmono σ d x0
    · simp only
      split_ifs
      · rw [add_zero]
      · exact le_of_eq (add_gain h hmono d v).symm
  unfold grp
  calc h d + ((Fintype.card R : ℕ) : ℝ≥0∞)⁻¹ * ∑ x0, val e (sOf p σ) (tOf p σ) gp 0 L x0
      = ((Fintype.card R : ℕ) : ℝ≥0∞)⁻¹ * ∑ x0 : R, (h d + val e (sOf p σ) (tOf p σ) gp 0 L x0) := by
        rw [Finset.sum_add_distrib, mul_add]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← mul_assoc, card_inv_mul_card, one_mul]
    _ ≤ _ := mul_le_mul_right (Finset.sum_le_sum fun x0 _ => hat x0) _

/-- **A new landed value, seen by itself.** With its own item excluded, the group after a landing
query is at most the group before. -/
theorem grp_landed_excl_le (hp : p ≤ 1) {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h) (σ : St R V) (y : R)
    (hy : σ y = none) (v : V) (ex : R → Bool) (d : Multiset V) :
    grp e p L (Function.update σ y (some (some v))) (fun x => decide (x = y) || ex x) h d ≤ grp e p L σ ex h d := by
  unfold grp
  refine mul_le_mul_right (Finset.sum_le_sum fun x0 _ => ?_) _
  have hbase : baseOf (Function.update σ y (some (some v))) h d x0 = baseOf σ h d x0 := by
    unfold baseOf
    by_cases hx : x0 = y
    · subst hx; simp [hy]
    · rw [Function.update_of_ne hx]
  unfold grpAt
  rw [hbase, sOf_landed, tOf_landed]
  refine val_stop_le e _ _ y (sOf_add_tOf hp σ) (K := h d)
    (le_pay hmono σ ex d (le_baseOf hmono σ d x0)) (le_baseOf hmono σ d x0) (fun x hx => ?_) ?_ L x0
  · simp [pay, Function.update_of_ne hx, hx]
  · simp [pay]

/-- **One more query.** -/
theorem grp_step (hp : p ≤ 1) (hp0 : p ≠ 0) (A : ℕ) (hL : L ≤ A + 1) (hL1 : 1 ≤ L)
    (hfree : ∀ (y : R) j, j < A → e^[j] (e y) ≠ y) {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h)
    (hfin : ∀ D, h D ≠ ⊤) (σ : St R V) (y : R) (hy : σ y = none) (ex : R → Bool) (hex : ex y = false) (d : Multiset V) :
    p * freshAvg Finset.univ (fun v => grp e p L (Function.update σ y (some (some v))) ex h d) +
        (1 - p) * grp e p L (Function.update σ y (some none)) ex h d ≤
      grp e p L σ ex h d + (1 + (1 - p)) * ((Fintype.card R : ℕ) : ℝ≥0∞)⁻¹ * (avgT h d - h d) := by
  set g := avgT h d - h d with hg
  set u := ((Fintype.card R : ℕ) : ℝ≥0∞)⁻¹ with hu
  have havg : avgT h d = h d + g := (add_tsub_cancel_of_le (le_avgT hmono d)).symm
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hq : p + (1 - p) = 1 := add_tsub_cancel_of_le hp
  have hgfin : avgT h d ≠ ⊤ := freshAvg_ne_top Finset.univ_nonempty fun v => hfin _
  set s := sOf p σ with hs
  set t := tOf p σ with ht
  have hsy : s y = p := by simp [hs, sOf, hy]
  have hty : t y = 1 - p := by simp [ht, tOf, hy]
  set w : R → ℝ≥0∞ := fun x => if x = y then 0 else if σ x = some none then 0 else 1 with hw
  -- one start
  have hpoint : ∀ x0, p * freshAvg Finset.univ (fun v => grpAt e p L (Function.update σ y (some (some v))) ex h d x0) +
      (1 - p) * grpAt e p L (Function.update σ y (some none)) ex h d x0 ≤
      grpAt e p L σ ex h d x0 + g * ((if x0 = y then 1 else 0) + p * (w x0 * arrive e t y L x0)) := by
    intro x0
    by_cases hx0 : x0 = y
    · subst hx0
      obtain ⟨L', rfl⟩ := Nat.exists_eq_add_of_le' hL1
      have hbL : ∀ v, baseOf (Function.update σ x0 (some (some v))) h d x0 = h d := by
        intro v; simp [baseOf]
      have hbN : baseOf (Function.update σ x0 (some none)) h d x0 = avgT h d := by simp [baseOf]
      have hb0 : baseOf σ h d x0 = h d := by simp [baseOf, hy]
      have hLv : ∀ v, grpAt e p (L' + 1) (Function.update σ x0 (some (some v))) ex h d x0 = h (d + {v}) := by
        intro v
        unfold grpAt
        rw [hbL, sOf_landed, tOf_landed, pay_landed σ ex h d _ x0 v hex]
        simp [val]
      set X := val e s t (pay σ ex h d (h d)) (h d) L' (e x0) with hX
      have hN : grpAt e p (L' + 1) (Function.update σ x0 (some none)) ex h d x0 ≤ X + g := by
        unfold grpAt
        rw [hbN, sOf_unlanded, tOf_unlanded, pay_unlanded σ ex h d _ x0 hy]
        simp only [val, Function.update_self, zero_mul, zero_add, one_mul]
        have hkeep : val e (Function.update (sOf p σ) x0 0) (Function.update (tOf p σ) x0 1)
            (pay σ ex h d (avgT h d)) (avgT h d) L' (e x0) =
            val e s t (pay σ ex h d (avgT h d)) (avgT h d) L' (e x0) := by
          refine val_congr e _ _ _ L' (e x0) fun j hj => ?_
          have hne : e^[j] (e x0) ≠ x0 := hfree x0 j (by omega)
          simp [Function.update_of_ne hne, hs, ht]
        rw [hkeep, havg]
        refine le_trans (val_mono e s t (c' := fun z => pay σ ex h d (h d) z + g) (fun z => ?_) le_rfl L' (e x0))
          (val_add_const_le e s t (fun x => (sOf_add_tOf hp σ x).le) _ _ g L' (e x0))
        unfold pay
        rcases σ z with _ | _ | v
        · exact le_rfl
        · exact le_rfl
        · simp only
          exact le_self_add
      have h0 : grpAt e p (L' + 1) σ ex h d x0 = p * h d + (1 - p) * X := by
        unfold grpAt
        rw [hb0]
        simp only [val]
        rw [← hs, ← ht, hsy, hty]
        simp [pay, hy, hX]
      simp only [hLv, ite_true, hw, mul_zero, zero_mul, add_zero, mul_one]
      rw [h0]
      change p * avgT h d + _ ≤ _
      rw [havg]
      calc p * (h d + g) + (1 - p) * grpAt e p (L' + 1) (Function.update σ x0 (some none)) ex h d x0
          ≤ p * (h d + g) + (1 - p) * (X + g) := by gcongr
        _ = p * h d + (1 - p) * X + (p + (1 - p)) * g := by ring
        _ = _ := by rw [hq, one_mul]
    · set b := baseOf σ h d x0 with hb
      have hbL : ∀ v, baseOf (Function.update σ y (some (some v))) h d x0 = b := by
        intro v; simp [baseOf, hb, Function.update_of_ne hx0]
      have hbN : baseOf (Function.update σ y (some none)) h d x0 = b := by
        simp [baseOf, hb, Function.update_of_ne hx0]
      set c := pay σ ex h d b with hc
      have hcy : c y = b := by simp [hc, pay, hy]
      set VN := val e (Function.update s y 0) (Function.update t y 1) c b L x0 with hVN
      set V0 := val e s t c b L x0 with hV0
      set Ar := arrive e t y L x0 with hAr
      set VL : V → ℝ≥0∞ := fun v => val e (Function.update s y 1) (Function.update t y 0)
        (Function.update c y (h (d + {v}))) b L x0 with hVL
      have hLv : ∀ v, grpAt e p L (Function.update σ y (some (some v))) ex h d x0 = VL v := by
        intro v
        unfold grpAt
        rw [hbL, sOf_landed, tOf_landed, pay_landed σ ex h d _ y v hex]
      have hNv : grpAt e p L (Function.update σ y (some none)) ex h d x0 = VN := by
        unfold grpAt
        rw [hbN, sOf_unlanded, tOf_unlanded, pay_unlanded σ ex h d _ y hy]
      have hq1 : ∀ v, p * VL v + (1 - p) * VN + p * Ar * b = V0 + p * Ar * h (d + {v}) := by
        intro v
        have := val_query e s t y p hp hsy hty c (h (d + {v})) b A (hfree y) L x0 hL
        rw [hcy] at this
        exact this
      have hAr1 : Ar ≤ 1 := by
        rw [hAr, ← val_arrive e s t y L x0]
        refine val_le e _ _ (fun x => ?_) (fun x => ?_) bot_le L x0
        · by_cases hx : x = y
          · subst hx; simp
          · rw [Function.update_of_ne hx, Function.update_of_ne hx]
            exact (sOf_add_tOf hp σ x).le
        · split_ifs <;> simp
      have hArt : p * Ar ≠ ⊤ := ENNReal.mul_ne_top hpt (ne_top_of_le_ne_top ENNReal.one_ne_top hAr1)
      have hmean : p * freshAvg Finset.univ VL + (1 - p) * VN + p * Ar * b = V0 + p * Ar * avgT h d := by
        have h1 : freshAvg Finset.univ (fun v => p * VL v + (1 - p) * VN + p * Ar * b) =
            freshAvg Finset.univ (fun v => V0 + p * Ar * h (d + {v})) := by
          congr 1; funext v; exact hq1 v
        rw [freshAvg_add, freshAvg_add, freshAvg_mul, freshAvg_const _ Finset.univ_nonempty,
          freshAvg_const _ Finset.univ_nonempty, freshAvg_add, freshAvg_const _ Finset.univ_nonempty,
          freshAvg_mul] at h1
        exact h1
      simp only [hLv, hNv, ite_eq_right hx0, zero_add]
      by_cases hnl : σ x0 = some none
      · have hbv : b = avgT h d := by simp [hb, baseOf, hnl]
        have hw0 : w x0 = 0 := by simp [hw, hx0, hnl]
        rw [hw0, zero_mul, mul_zero, mul_zero, add_zero]
        rw [hbv] at hmean
        exact le_of_eq ((ENNReal.add_left_inj (ENNReal.mul_ne_top hArt hgfin)).1 hmean)
      · have hbv : b = h d := by simp [hb, baseOf, hnl]
        have hw1 : w x0 = 1 := by simp [hw, hx0, hnl]
        rw [hw1, one_mul]
        rw [hbv, havg] at hmean
        have : p * freshAvg Finset.univ VL + (1 - p) * VN + p * Ar * h d = V0 + g * (p * Ar) + p * Ar * h d := by
          rw [hmean]; ring
        exact le_of_eq ((ENNReal.add_left_inj (ENNReal.mul_ne_top hArt (hfin d))).1 this)
  -- the starts that reach `y`
  have hrank : ∑ x0, w x0 * arrive e t y L x0 ≤ (1 - p) * p⁻¹ := by
    refine sum_arrive_le e t y w (1 - p) ((1 - p) * p⁻¹) ?_ (fun x => tOf_le_one p σ x) (fun x => ?_) ?_
      (fun x hx => ?_) L
    · have : 1 + (1 - p) * p⁻¹ = p⁻¹ := by
        calc 1 + (1 - p) * p⁻¹ = p * p⁻¹ + (1 - p) * p⁻¹ := by rw [ENNReal.mul_inv_cancel hp0 hpt]
          _ = (p + (1 - p)) * p⁻¹ := by ring
          _ = p⁻¹ := by rw [hq, one_mul]
      rw [this]
    · simp only [hw]; split_ifs <;> simp
    · simp [hw]
    · simp only [hw] at hx
      split_ifs at hx with h1 h2
      · exact absurd rfl hx
      · exact absurd rfl hx
      · simp only [ht, tOf]
        rcases hσ : σ x with _ | _ | v
        · exact le_rfl
        · exact absurd hσ h2
        · exact bot_le
  have hsumB : ∑ x0 : R, ((if x0 = y then (1 : ℝ≥0∞) else 0) + p * (w x0 * arrive e t y L x0)) ≤ 1 + (1 - p) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    refine add_le_add (le_of_eq (by simp)) ?_
    calc p * ∑ x0, w x0 * arrive e t y L x0 ≤ p * ((1 - p) * p⁻¹) := mul_le_mul_right hrank _
      _ = (1 - p) * (p * p⁻¹) := by ring
      _ = 1 - p := by rw [ENNReal.mul_inv_cancel hp0 hpt, mul_one]
  have hsumL : freshAvg Finset.univ (fun v => grp e p L (Function.update σ y (some (some v))) ex h d) =
      u * ∑ x0, freshAvg Finset.univ (fun v => grpAt e p L (Function.update σ y (some (some v))) ex h d x0) := by
    unfold grp freshAvg
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hsumL]
  unfold grp
  calc p * (u * ∑ x0, freshAvg Finset.univ (fun v => grpAt e p L (Function.update σ y (some (some v))) ex h d x0)) +
        (1 - p) * (u * ∑ x0, grpAt e p L (Function.update σ y (some none)) ex h d x0)
      = u * ∑ x0, (p * freshAvg Finset.univ (fun v => grpAt e p L (Function.update σ y (some (some v))) ex h d x0) +
          (1 - p) * grpAt e p L (Function.update σ y (some none)) ex h d x0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ u * ∑ x0, (grpAt e p L σ ex h d x0 +
          g * ((if x0 = y then 1 else 0) + p * (w x0 * arrive e t y L x0))) :=
        mul_le_mul_right (Finset.sum_le_sum fun x0 _ => hpoint x0) _
    _ = u * ∑ x0, grpAt e p L σ ex h d x0 +
          u * g * ∑ x0 : R, ((if x0 = y then (1 : ℝ≥0∞) else 0) + p * (w x0 * arrive e t y L x0)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    _ ≤ u * ∑ x0, grpAt e p L σ ex h d x0 + u * g * (1 + (1 - p)) := by gcongr
    _ = _ := by ring

/-- **One more query, in mixture form.** The mean after a query is at most the mixture of the mean
and of its average after one more uniform disclosure, with weight `(2 - p) / |R|`. -/
theorem grp_avg_step (hp : p ≤ 1) (hp0 : p ≠ 0) (A : ℕ) (hL : L ≤ A + 1) (hL1 : 1 ≤ L)
    (hfree : ∀ (y : R) j, j < A → e^[j] (e y) ≠ y) {h : Multiset V → ℝ≥0∞}
    (hf : Monotone' h ∧ Supermodular h ∧ ∀ D, h D ≠ ⊤) (σ : St R V) (y : R) (hy : σ y = none) (ex : R → Bool)
    (hex : ex y = false) (r : ℝ≥0∞) (hr : r = (1 + (1 - p)) * ((Fintype.card R : ℕ) : ℝ≥0∞)⁻¹) (hr1 : r ≤ 1)
    (d : Multiset V) :
    p * freshAvg Finset.univ (fun v => grp e p L (Function.update σ y (some (some v))) ex h d) +
        (1 - p) * grp e p L (Function.update σ y (some none)) ex h d ≤
      (1 - r) * grp e p L σ ex h d + r * avgT (grp e p L σ ex h) d := by
  have hR := rep_grp (e := e) (L := L) hp σ ex
  set T := grp e p L σ ex h with hT
  have hTp := hR.props hf
  set g := avgT h d - h d with hg
  have hstep := grp_step hp hp0 A hL hL1 hfree hf.1 hf.2.2 σ y hy ex hex d
  rw [← hr] at hstep
  have hgain : T d + g ≤ avgT T d := by
    have h1 : avgT T d = grp e p L σ ex (fun D => avgT h D) d := by
      unfold avgT
      rw [hR.map_freshAvg]
      congr 1
      funext v
      exact (hR.map_translate h {v} d).symm
    rw [h1]
    calc T d + g = grp e p L σ ex (fun D => h D + (fun _ => g) D) d := by
          rw [hR.map_add, grp_const hp]
      _ ≤ _ := hR.map_mono_above d fun D hD => add_avgGain_le hf.1 hf.2.1 hf.2.2 d D hD
  have hTd : T d ≠ ⊤ := hTp.2.2 d
  have hg' : g ≤ avgT T d - T d := ENNReal.le_sub_of_add_le_left hTd hgain
  have hTle : T d ≤ avgT T d := le_avgT hTp.1 d
  refine le_trans hstep ?_
  calc T d + r * g ≤ T d + r * (avgT T d - T d) := by gcongr
    _ = (1 - r) * T d + r * (T d + (avgT T d - T d)) := by
        rw [mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le hr1, one_mul]
    _ = _ := by rw [add_tsub_cancel_of_le hTle]

end Group

end SphincsFors.Security.Walk
