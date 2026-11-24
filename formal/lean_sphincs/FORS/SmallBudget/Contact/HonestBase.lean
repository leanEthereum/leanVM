module

public import FORS.CoverPotential.Presample
public import FORS.LazyRun.HonestRead

@[expose] public section

/-! The interpreter's ordinary and draw steps with honest reads (`SourceCostSpec D R ι H`), and
presampling for a value of the run alone: it keeps the value's mean, for one input and for a fresh
family. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)
variable {H : Type} [HonestInputs H D]

omit [Fintype ι] in
/-- One ordinary query in the interpreter, with honest reads. -/
theorem interp_ordinaryHB {β : Type} (x : D) (next : R → OracleComp (SourceCostSpec D R ι H) β)
    (budget : ℕ) (state : DebtState D R ι) :
    interp tg initial model (liftM ((SourceCostSpec D R ι H).query (.inl (.inr (.inl x)))) >>= next) budget state =
      if 1 ≤ budget then ordinaryStep model x state.known state >>= fun result =>
        (fun out => ((out.1.1, out.1.2.1, Sum.inl x :: out.1.2.2.1,
          touch (H := H) tg initial state (.inl (.inr (.inl x))) ++ out.1.2.2.2), out.2)) <$>
            interp tg initial model (next result.1) (budget - 1) result.2
      else pure ((none, [], [], []), state) := by
  rw [interp_query_bind]
  rw [costStep_ordinary]
  rfl

omit [Fintype ι] in
/-- A private draw is drawn directly and changes nothing else, with honest reads. -/
theorem interp_drawHB {β : Type} (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp (SourceCostSpec D R ι H) β) (budget : ℕ) (state : DebtState D R ι) :
    interp tg initial model (liftM ((SourceCostSpec D R ι H).query (.inl (.inl draw))) >>= next) budget state =
      (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1))) >>= fun value =>
        interp tg initial model (next value) budget state := by
  rw [interp_query_bind]
  split_ifs with h
  · change ((fun v => (v, state)) <$> (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))) >>=
        (fun result => (fun out : Run D ι β × DebtState D R ι => ((out.1.1, [] ++ out.1.2.1, [] ++ out.1.2.2.1,
          [] ++ out.1.2.2.2), out.2)) <$> interp tg initial model (next result.1) (budget - 0) result.2) = _
    rw [bind_map_left]
    refine bind_congr fun value => ?_
    simp only [List.nil_append, Nat.sub_zero]
    rw [show (fun out : Run D ι β × DebtState D R ι =>
        ((out.1.1, out.1.2.1, out.1.2.2.1, out.1.2.2.2), out.2)) = id from rfl, id_map]
  · exact absurd (Nat.zero_le budget) h

/-! ### Presampling keeps a value of the run alone -/

omit [Fintype ι] in
/-- A value of the run alone is unchanged by presampling. -/
theorem interp_presample_eq (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι H) α) (budget : ℕ) (state : DebtState D R ι)
    (F : Run D ι α → ℝ≥0∞) :
    ∑' s, Pr{let y ← presample x state}[y = s] *
        ∑' out, Pr{let x ← interp tg initial model computation budget s}[x = out] * F out.1 =
      ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] * F out.1 := by
  have heq : ∑' s, Pr{let y ← presample x state}[y = s] *
      ∑' out, Pr{let x ← interp tg initial model computation budget s}[x = out] * F out.1 =
      ∑' out, Pr{let y ← (interp tg initial model computation budget state >>= fun out =>
        (fun s => (out.1, s)) <$> presample x out.2)}[y = out] * F out.1 := by
    rw [← OracleComp.tsum_prEvent_bind_mul]
    exact tsum_congr fun out => congrArg (· * _) ((presample_interp tg initial model x hk computation budget state).prEvent_eq _)
  rw [heq, OracleComp.tsum_prEvent_bind_mul]
  refine tsum_congr fun out => ?_
  rw [OracleComp.tsum_prEvent_map_mul]
  simp only
  rw [ENNReal.tsum_mul_right, presample_mass, one_mul]

/-! ### Storing a family of inputs -/

variable [Fintype R]

omit [Fintype ι] in
/-- Presampling one fresh untargeted input keeps a value of the run alone. -/
theorem interp_presample_fresh_eq (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι H) α) (budget : ℕ) (state : DebtState D R ι)
    (hx : state.cache x = none) (F : Run D ι α → ℝ≥0∞) :
    ∑' out, Pr{let z ← interp tg initial model computation budget state}[z = out] * F out.1 =
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr{let z ← (interp tg initial model computation budget
        (state.store x v))}[z = out] * F out.1 := by
  rw [← interp_presample_eq tg initial model x hk computation budget state F,
    presample_fresh x state hx, OracleComp.tsum_prEvent_map_mul, tsum_uniform_eq]

omit [Fintype ι] in
/-- **Presampling an injective family of fresh untargeted inputs** keeps a value of the run alone. -/
theorem interp_presampleAll_eq {α : Type} (computation : OracleComp (SourceCostSpec D R ι H) α) (budget : ℕ)
    (F : Run D ι α → ℝ≥0∞) :
    ∀ {n : ℕ} (x : Fin n → D), Function.Injective x → (∀ i, tg.kind (x i) = .none) →
      ∀ state : DebtState D R ι, (∀ i, state.cache (x i) = none) →
        ∑' out, Pr{let z ← interp tg initial model computation budget state}[z = out] * F out.1 =
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
            ∑' out, Pr{let z ← interp tg initial model computation budget (storeAll x u state)}[z = out] * F out.1
  | 0, x, _, _, state, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hk, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      rw [interp_presample_fresh_eq tg initial model (x 0) (hk 0) computation budget state (hfresh 0) F]
      have hrest : ∀ v, ∑' out, Pr{let z ← interp tg initial model computation budget (state.store (x 0) v)}[z = out] * F out.1 =
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R, ∑' out, Pr{let z ← (interp tg initial model
            computation budget (storeAll (Fin.tail x) w (state.store (x 0) v)))}[z = out] * F out.1 := fun v =>
        interp_presampleAll_eq computation budget F (Fin.tail x) hxt (fun i => hk i.succ) _ fun i => by
          show (state.store (x 0) v).cache (x i.succ) = none
          rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
          exact hfresh i.succ
      calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr{let z ← (interp tg initial model computation budget
              (state.store (x 0) v))}[z = out] * F out.1
          = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
              ∑' out, Pr{let z ← (interp tg initial model computation budget
                (storeAll (Fin.tail x) w (state.store (x 0) v)))}[z = out] * F out.1) :=
            congrArg (fun A => (Fintype.card R : ℝ≥0∞)⁻¹ * A) (Finset.sum_congr rfl fun v _ => hrest v)
        _ = ((Fintype.card R : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → R,
              ∑' out, Pr{let z ← (interp tg initial model computation budget
                (storeAll x (Fin.cons v w) state))}[z = out] * F out.1 := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            congr 1
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl

omit [Fintype ι] in
/-- **A query of one input of a fresh family**, for a value of the run alone: the uniform answer at
input `c` followed by the run has the same mean as the run after storing uniform answers at the
whole family. -/
theorem interp_presample_new_eq {α : Type} {n : ℕ} (x : Fin n → D) (hx : Function.Injective x)
    (hk : ∀ i, tg.kind (x i) = .none) (c : Fin n) (next : R → OracleComp (SourceCostSpec D R ι H) α)
    (budget : ℕ) (state : DebtState D R ι) (hfresh : ∀ i, state.cache (x i) = none)
    (F : Run D ι α → ℝ≥0∞) :
    ∑' v, Pr{let z ← ($ᵗ R : ProbComp R)}[z = v] *
        ∑' out, Pr{let z ← interp tg initial model (next v) budget (state.store (x c) v)}[z = out] * F out.1 =
      ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
        ∑' out, Pr{let z ← interp tg initial model (next (u c)) budget (storeAll x u state)}[z = out] * F out.1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (m + 1) → D := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, ∑' out, Pr{let z ← interp tg initial model (next v) budget (state.store (x c) v)}[z = out] * F out.1 =
      ((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R, ∑' out, Pr{let z ← (interp tg initial model
        (next v) budget (storeAll x' (Fin.cons v w) state))}[z = out] * F out.1 := by
    intro v
    rw [← hx'0]
    exact interp_presampleAll_eq tg initial model (next v) budget F (Fin.tail x') hxt (fun i => hk _) _
      fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr{let z ← (interp tg initial model (next v) budget
          (state.store (x c) v))}[z = out] * F out.1
      = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
          ∑' out, Pr{let z ← interp tg initial model (next v) budget (storeAll x' (Fin.cons v w) state)}[z = out] * F out.1) :=
        congrArg (fun A => (Fintype.card R : ℝ≥0∞)⁻¹ * A) (Finset.sum_congr rfl fun v _ => hrest v)
    _ = ((Fintype.card R : ℝ≥0∞) ^ (m + 1))⁻¹ * ∑ u' : Fin (m + 1) → R,
          ∑' out, Pr{let z ← interp tg initial model (next (u' 0)) budget (storeAll x' u' state)}[z = out] * F out.1 := by
        rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
          (Or.inl (ENNReal.natCast_ne_top _))]
        congr 1
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl
    _ = _ := by
        congr 1
        refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl R)) _ _ fun u' => ?_
        have hu : (σ.arrowCongr (Equiv.refl R)) u' ∘ σ = u' := by
          funext i
          simp [Equiv.arrowCongr_apply, hσ, Equiv.swap_apply_self]
        conv_lhs => rw [← hu]
        rw [storeAll_perm x hx _ σ state]
        congr 3


end FORS.Security.HiddenDebt
