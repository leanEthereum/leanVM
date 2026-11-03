import FORS.LargeBudget.SurvivalWeight
import FORS.ScanSigner.FairShare
import FORS.ScanSigner.Scan

/-! The bounds of the scan signer `R = R0 + i δ`, weighted by the final survival weight. The
message-digest blocks are untargeted, so their reads keep the weight; everything after the digest
read of the final assembly lowers it in expectation. Each bound of `ScanSigner/Scan` therefore holds with
the integrand multiplied by the final weight and the walk value multiplied by the initial weight.
A trial reads the index block of a pair alone, so a fresh pair is drawn whole by presampling its
remaining digest calls: presampling keeps the weight exactly, because the blocks are untargeted
(`interp_presample_newW`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-! ### Presampling a family of untargeted inputs, weighted -/

/-- Storing untargeted answers at a whole family keeps the weight. -/
theorem weight_storeAllW : ∀ {n : ℕ} (x : Fin n → D) (u : Fin n → R) (state : DebtState D R ι),
    (∀ i, tg.kind (x i) = .none) → weight tg initial (storeAll x u state) = weight tg initial state
  | 0, _, _, _, _ => rfl
  | _ + 1, x, u, state, hk => by
      rw [storeAll_succ, weight_storeAllW (Fin.tail x) (Fin.tail u) _ fun i => hk i.succ,
        weight_store_untargetedW tg initial state (x 0) (u 0) (hk 0)]

variable [Fintype R]

/-- Presampling one fresh untargeted input helps a weighted value whose run part is monotone under
fresh stores: the store itself leaves the weight alone. -/
theorem interp_presample_freshW (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) (state : DebtState D R ι)
    (hx : state.cache x = none) (V : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hV : ∀ out (y : D) (v : R), out.2.cache y = none → V out ≤ V (out.1, out.2.store y v)) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] *
        (weight tg initial out.2 * V out) ≤
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model computation budget
        (state.store x v)] * (weight tg initial out.2 * V out) := by
  refine le_trans (interp_presample_le tg initial model x hk computation budget state
    (fun out => weight tg initial out.2 * V out) fun out s hs => ?_) ?_
  · cases hc : out.2.cache x with
    | some w =>
        rw [presample_cached x out.2 w hc, support_pure, Set.mem_singleton_iff] at hs
        rw [hs]
    | none =>
        rw [presample_fresh x out.2 hc, support_map] at hs
        obtain ⟨v, _, rfl⟩ := hs
        simp only
        rw [weight_store_untargetedW tg initial out.2 x v hk]
        exact mul_le_mul_right (hV out x v hc) _
  · rw [presample_fresh x state hx, tsum_probOutput_map_mul, tsum_uniform_eq]

/-- **Presampling an injective family of fresh untargeted inputs**, weighted. -/
theorem interp_presampleAllW {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ)
    (V : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hV : ∀ out (y : D) (v : R), out.2.cache y = none → V out ≤ V (out.1, out.2.store y v)) :
    ∀ {n : ℕ} (x : Fin n → D), Function.Injective x → (∀ i, tg.kind (x i) = .none) →
      ∀ state : DebtState D R ι, (∀ i, state.cache (x i) = none) →
        ∑' out, Pr[= out | interp tg initial model computation budget state] *
            (weight tg initial out.2 * V out) ≤
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
            ∑' out, Pr[= out | interp tg initial model computation budget (storeAll x u state)] *
              (weight tg initial out.2 * V out)
  | 0, x, _, _, state, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hk, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      refine le_trans (interp_presample_freshW tg initial model (x 0) (hk 0) computation budget state
        (hfresh 0) V hV) ?_
      have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model computation budget (state.store (x 0) v)] *
          (weight tg initial out.2 * V out) ≤
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R, ∑' out, Pr[= out | interp tg initial model
            computation budget (storeAll (Fin.tail x) w (state.store (x 0) v))] *
              (weight tg initial out.2 * V out) := fun v =>
        interp_presampleAllW computation budget V hV (Fin.tail x) hxt (fun i => hk i.succ) _ fun i => by
          show (state.store (x 0) v).cache (x i.succ) = none
          rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
          exact hfresh i.succ
      calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model computation budget
              (state.store (x 0) v)] * (weight tg initial out.2 * V out)
          ≤ (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll (Fin.tail x) w (state.store (x 0) v))] * (weight tg initial out.2 * V out)) := by
            gcongr with v
            exact hrest v
        _ = ((Fintype.card R : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → R,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll x (Fin.cons v w) state)] * (weight tg initial out.2 * V out) := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            congr 1
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl

/-- **A query of one input of a fresh family**, weighted. -/
theorem interp_presample_newW {α : Type} {n : ℕ} (x : Fin n → D) (hx : Function.Injective x)
    (hk : ∀ i, tg.kind (x i) = .none) (c : Fin n) (next : R → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) (hfresh : ∀ i, state.cache (x i) = none)
    (V : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hV : ∀ out (y : D) (v : R), out.2.cache y = none → V out ≤ V (out.1, out.2.store y v)) :
    ∑' v, Pr[= v | ($ᵗ R : ProbComp R)] *
        ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] *
          (weight tg initial out.2 * V out) ≤
      ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
        ∑' out, Pr[= out | interp tg initial model (next (u c)) budget (storeAll x u state)] *
          (weight tg initial out.2 * V out) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (m + 1) → D := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] *
      (weight tg initial out.2 * V out) ≤
      ((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R, ∑' out, Pr[= out | interp tg initial model
        (next v) budget (storeAll x' (Fin.cons v w) state)] * (weight tg initial out.2 * V out) := by
    intro v
    rw [← hx'0]
    exact interp_presampleAllW tg initial model (next v) budget V hV (Fin.tail x') hxt (fun i => hk _) _
      fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model (next v) budget
          (state.store (x c) v)] * (weight tg initial out.2 * V out)
      ≤ (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
          ∑' out, Pr[= out | interp tg initial model (next v) budget
            (storeAll x' (Fin.cons v w) state)] * (weight tg initial out.2 * V out)) := by
        gcongr with v
        exact hrest v
    _ = ((Fintype.card R : ℝ≥0∞) ^ (m + 1))⁻¹ * ∑ u' : Fin (m + 1) → R,
          ∑' out, Pr[= out | interp tg initial model (next (u' 0)) budget (storeAll x' u' state)] *
            (weight tg initial out.2 * V out) := by
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

/-! ### Presampling and the weighted payments -/

/-- **Presampling an untargeted input keeps the weighted payments.** The payment of a step reads the
state only through its weight, which an untargeted store leaves alone, and the rest of the run
commutes with the presample (`presample_costStep`). -/
theorem wflag_presample_eq (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ (budget : ℕ) (state : DebtState D R ι),
      ∑' s, Pr[= s | presample x state] * wflag tg initial model computation budget s =
        wflag tg initial model computation budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state
      simp only [wflag_pure, mul_zero, tsum_zero]
  | query_bind input next ih =>
      intro budget state
      have hw : ∀ s ∈ support (presample x state), weight tg initial s = weight tg initial state := by
        intro s hs
        cases hc : state.cache x with
        | some v =>
            rw [presample_cached x state v hc, support_pure, Set.mem_singleton_iff] at hs
            rw [hs]
        | none =>
            rw [presample_fresh x state hc, support_map] at hs
            obtain ⟨v, _, rfl⟩ := hs
            exact weight_store_untargetedW tg initial state x v hk
      have hpay : ∀ s ∈ support (presample x state),
          wpays tg initial s input = wpays tg initial state input := by
        intro s hs
        have h := hw s hs
        rcases input with (draw | (bytes | coordinate)) | amount
        · rfl
        · simp only [wpays, h]
        · rfl
        · rfl
      simp only [wflag_query_bind]
      split_ifs with hcost
      · set K : (SourceCostSpec D R ι).Range input × DebtState D R ι → ℝ≥0∞ := fun r =>
          wpays tg initial state input +
            wflag tg initial model (next r.1) (budget - sourceCost input) r.2 with hK
        have hleft : ∑' s, Pr[= s | presample x state] *
            ∑' r, Pr[= r | costStep model input s] *
              (wpays tg initial s input +
                wflag tg initial model (next r.1) (budget - sourceCost input) r.2) =
            ∑' s, Pr[= s | presample x state] * ∑' r, Pr[= r | costStep model input s] * K r := by
          refine tsum_congr fun s => ?_
          by_cases hs : s ∈ support (presample x state)
          · rw [hpay s hs]
          · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]
        have hcomm := presample_costStep model x input state (fun r => (pure r : ProbComp _))
        simp only [bind_pure] at hcomm
        rw [hleft, ← tsum_probOutput_bind_mul]
        calc ∑' r, Pr[= r | presample x state >>= fun s => costStep model input s] * K r
            = ∑' r, Pr[= r | costStep model input state >>= fun r =>
                presample x r.2 >>= fun s => (pure (r.1, s) : ProbComp _)] * K r :=
              tsum_congr fun r => congrArg (· * K r) (probOutput_congr rfl hcomm)
          _ = ∑' r, Pr[= r | costStep model input state] *
                ∑' s, Pr[= s | presample x r.2] * K (r.1, s) := by
              rw [tsum_probOutput_bind_mul]
              refine tsum_congr fun r => congrArg _ ?_
              rw [tsum_probOutput_bind_mul]
              exact tsum_congr fun s => by rw [tsum_probOutput_pure_mul]
          _ = ∑' r, Pr[= r | costStep model input state] * K r := by
              refine tsum_congr fun r => congrArg _ ?_
              simp only [hK]
              have hsplit : (∑' s, Pr[= s | presample x r.2] *
                    (wpays tg initial state input +
                      wflag tg initial model (next r.1) (budget - sourceCost input) s)) =
                  (∑' s, Pr[= s | presample x r.2] * wpays tg initial state input) +
                    ∑' s, Pr[= s | presample x r.2] *
                      wflag tg initial model (next r.1) (budget - sourceCost input) s := by
                rw [← ENNReal.tsum_add]
                exact tsum_congr fun s => mul_add _ _ _
              rw [hsplit, ENNReal.tsum_mul_right, presample_mass, one_mul,
                ih r.1 (budget - sourceCost input) r.2]
      · simp only [mul_zero, tsum_zero]

/-- Presampling one fresh untargeted input keeps the weighted payments. -/
theorem wflag_presample_fresh_eq (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) (state : DebtState D R ι)
    (hx : state.cache x = none) :
    wflag tg initial model computation budget state =
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, wflag tg initial model computation budget (state.store x v) := by
  rw [← wflag_presample_eq tg initial model x hk computation budget state, presample_fresh x state hx,
    tsum_probOutput_map_mul, tsum_uniform_eq]

/-- **Presampling an injective family of fresh untargeted inputs** keeps the weighted payments. -/
theorem wflag_presampleAll_eq {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) :
    ∀ {n : ℕ} (x : Fin n → D), Function.Injective x → (∀ i, tg.kind (x i) = .none) →
      ∀ state : DebtState D R ι, (∀ i, state.cache (x i) = none) →
        wflag tg initial model computation budget state =
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
            wflag tg initial model computation budget (storeAll x u state)
  | 0, x, _, _, state, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hk, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      rw [wflag_presample_fresh_eq tg initial model (x 0) (hk 0) computation budget state (hfresh 0)]
      have hrest : ∀ v, wflag tg initial model computation budget (state.store (x 0) v) =
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
            wflag tg initial model computation budget (storeAll (Fin.tail x) w (state.store (x 0) v)) := fun v =>
        wflag_presampleAll_eq computation budget (Fin.tail x) hxt (fun i => hk i.succ) _ fun i => by
          show (state.store (x 0) v).cache (x i.succ) = none
          rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
          exact hfresh i.succ
      calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, wflag tg initial model computation budget (state.store (x 0) v)
          = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
              wflag tg initial model computation budget (storeAll (Fin.tail x) w (state.store (x 0) v))) :=
            congrArg (fun A => (Fintype.card R : ℝ≥0∞)⁻¹ * A) (Finset.sum_congr rfl fun v _ => hrest v)
        _ = ((Fintype.card R : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → R,
              wflag tg initial model computation budget (storeAll x (Fin.cons v w) state) := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            congr 1
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl

/-- **A query of one input of a fresh family**, for the weighted payments: the uniform answer at
input `c` followed by the run pays the same as the run after storing uniform answers at the whole
family. -/
theorem wflag_presample_new_eq {α : Type} {n : ℕ} (x : Fin n → D) (hx : Function.Injective x)
    (hk : ∀ i, tg.kind (x i) = .none) (c : Fin n) (next : R → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) (hfresh : ∀ i, state.cache (x i) = none) :
    ∑' v, Pr[= v | ($ᵗ R : ProbComp R)] *
        wflag tg initial model (next v) budget (state.store (x c) v) =
      ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
        wflag tg initial model (next (u c)) budget (storeAll x u state) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (m + 1) → D := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, wflag tg initial model (next v) budget (state.store (x c) v) =
      ((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
        wflag tg initial model (next v) budget (storeAll x' (Fin.cons v w) state) := by
    intro v
    rw [← hx'0]
    exact wflag_presampleAll_eq tg initial model (next v) budget (Fin.tail x') hxt (fun i => hk _) _
      fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, wflag tg initial model (next v) budget (state.store (x c) v)
      = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
          wflag tg initial model (next v) budget (storeAll x' (Fin.cons v w) state)) :=
        congrArg (fun A => (Fintype.card R : ℝ≥0∞)⁻¹ * A) (Finset.sum_congr rfl fun v _ => hrest v)
    _ = ((Fintype.card R : ℝ≥0∞) ^ (m + 1))⁻¹ * ∑ u' : Fin (m + 1) → R,
          wflag tg initial model (next (u' 0)) budget (storeAll x' u' state) := by
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
        have hc0 : ((σ.arrowCongr (Equiv.refl R)) u') c = u' 0 := by
          conv_rhs => rw [← hu]
          simp [hσ, Equiv.swap_apply_left]
        have hstore : storeAll x' u' state = storeAll x ((σ.arrowCongr (Equiv.refl R)) u') state := by
          conv_lhs => rw [hx', ← hu]
          exact storeAll_perm x hx _ σ state
        rw [hc0, hstore]

end FORS.Security.HiddenDebt

namespace FORS.Security.GraphView

variable [Params]

open FORS.Base
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner FORS.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable


section LoopSW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- A cached pair holds the blocks of its tuple. -/
theorem pcache_some {state : DebtState HashInput HashOutput Coordinate} {ρ : Randomness}
    {u : DigestCall → HashOutput} (h : pcache parameter data message state ρ = some u)
    (call : DigestCall) : state.cache (pblk parameter data message ρ call) = some (u call) := by
  unfold pcache allSome at h
  split at h
  · rename_i hall
    cases h
    exact (Option.some_get (hall call)).symm
  · cases h

/-- A cached pair stays cached when a fresh input is stored. -/
theorem pcache_store {s' : DebtState HashInput HashOutput Coordinate} {y : HashInput}
    {v : HashOutput} (hy : s'.cache y = none) (ρ : Randomness) {u : DigestCall → HashOutput}
    (h : pcache parameter data message s' ρ = some u) :
    pcache parameter data message (s'.store y v) ρ = some u :=
  allSome_of_eq _ _ fun call => by
    have hcall := pcache_some parameter data message h call
    have hne : pblk parameter data message ρ call ≠ y := fun e => by
      rw [e, hy] at hcall
      exact absurd hcall (by simp)
    rw [store_cache_ne s' y _ hne v]
    exact hcall

/-- **Final assembly from a cached pair, weighted.** -/
theorem finish_boundAllW (randomness : Randomness)
    (state : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput)
    (hc : ∀ call, state.cache (pblk parameter data message randomness call) = some (u call))
    (g : (DigestCall → HashOutput) → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message randomness) budget state] *
        (weight tg initial out.2 * (if out.1.1.isSome then
          (pcache parameter data message out.2 randomness).elim 0 g else 0)) ≤
      weight tg initial state * g u := by
  refine interp_weight_mul_leW tg initial model _ _ state _ _ fun out hout => ?_
  have hpc : pcache parameter data message out.2 randomness = some u :=
    allSome_of_eq _ _ fun call =>
      (interp_extends tg initial model _ budget state out hout).1 _ _ (hc call)
  rw [hpc]
  split_ifs
  · rfl
  · exact bot_le

/-- The arithmetic of one fresh trial: the pair lands with probability `landing` on a uniform view,
and the scan goes on otherwise. -/
theorem trials_sum_le (gf : Lifetime.KeptDigestView → ℝ≥0∞) (bound : ℝ≥0∞) :
    ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
        (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound) ≤
      ForsPrice.landing * Domination.freshAvg Finset.univ gf + (1 - ForsPrice.landing) * bound := by
  have hsplit : (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
      (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound)) =
      (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
        (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else 0)) +
      bound * ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
        (if Landed parameter (blockIndex (u firstCall)) then 0 else 1) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun u => ?_
    split_ifs
    · simp
    · simp [mul_comm]
  rw [hsplit, unlanded_mass parameter, fresh_view_mean parameter gf, mul_comm bound]

/-- **One trial of the scan, weighted**, with any continuation. -/
theorem trial_boundSW
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hVabort : ∀ s', V none s' = 0)
    (hVstore : ∀ r (s' : DebtState HashInput HashOutput Coordinate) (y : HashInput) (v : HashOutput),
      s'.cache y = none → V r s' ≤ V r (s'.store y v))
    (hVfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.1 out.2 ≤ (if out.1.1.isSome then (pcache parameter data message out.2 ρ).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state)
    (hinv : PairInv parameter data message state)
    (hpair : ∀ call, state.cache (pblk parameter data message ρ call) =
      reference.cache (pblk parameter data message ρ call))
    (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' → PairInv parameter data message s' →
      (∀ x, (∀ call, x ≠ pblk parameter data message ρ call) → s'.cache x = state.cache x) → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤ weight tg initial s' * bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        (weight tg initial out.2 * V out.1.1 out.2) ≤
      weight tg initial state * (state.cache (blk parameter data message ρ)).elim
        (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
          (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤
        weight tg initial s' * pairWeight parameter data message reference gf gp ρ u := by
    intro s' u b hrel' hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_)
      (finish_boundAllW tg initial model parameter data message ρ s' u hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (mul_le_mul_right (hVfin s' u b hrel' hs' out hout) _) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ firstCall]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          obtain ⟨u, hu, hucall⟩ :=
            pcache_of_isSome parameter data message state ρ ((hinv ρ).2 u0 hc hl)
          have hu0 : u firstCall = u0 := Option.some_inj.1 ((hucall firstCall).symm.trans hc)
          have href : reference.cache (blk parameter data message ρ) = some u0 := by
            rw [← hpair firstCall]; exact hc
          have hpcsame : pcache parameter data message reference ρ =
              pcache parameter data message state ρ := by
            unfold pcache
            exact congrArg _ (funext fun call => (hpair call).symm)
          have hpv : poolValue parameter data message reference gp ρ = gp ρ (viewOf u) := by
            unfold poolValue
            rw [hpcsame.trans hu]
            simp only [Option.elim, hu0]
            rw [if_pos hl]
          have hpw : pairWeight parameter data message reference gf gp ρ u = gp ρ (viewOf u) := by
            unfold pairWeight
            rw [if_neg (by rw [href]; simp)]
          rw [hpv, ← hpw]
          exact hfinish state u _ (fun ρ' _ => hrel ρ') hucall
        · rw [if_neg hl, if_neg hl]
          exact hih state hrel hinv (fun _ _ => rfl) _
    | none =>
        have hfresh : ∀ call, state.cache (pblk parameter data message ρ call) = none := (hinv ρ).1 hc
        have href : reference.cache (blk parameter data message ρ) = none := by
          rw [← hpair firstCall]; exact hc
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        refine le_trans (interp_presample_newW tg initial model (pblk parameter data message ρ)
          (pblk_injective parameter data message ρ) (hkind ρ) firstCall
          (fun first => if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
            else cont) (budget - 1) state hfresh (fun out => V out.1.1 out.2)
          (fun out y v hy => hVstore out.1.1 out.2 y v hy)) ?_
        have hcard : (Fintype.card (DigestCall → HashOutput) : ℝ≥0∞) =
            (Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls := by
          rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        have hrhs : weight tg initial state *
            (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
              (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound)) =
            ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ *
              ∑ u : DigestCall → HashOutput, weight tg initial state *
                (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound) := by
          rw [tsum_uniform_eq, hcard, mul_left_comm, Finset.mul_sum]
        rw [hrhs]
        refine mul_le_mul_right (Finset.sum_le_sum fun u _ => ?_) _
        rw [← weight_storeAllW tg initial (pblk parameter data message ρ) u state (hkind ρ)]
        by_cases hl : Landed parameter (blockIndex (u firstCall))
        · rw [if_pos hl, if_pos hl]
          have hall : ∀ call, (storeAll (pblk parameter data message ρ) u state).cache
              (pblk parameter data message ρ call) = some (u call) :=
            fun call => storeAll_cache_self _ (pblk_injective parameter data message ρ) u state call
          have hpw : pairWeight parameter data message reference gf gp ρ u = gf (viewOf u) := by
            unfold pairWeight
            rw [if_pos href, if_pos hl]
          rw [← hpw]
          exact hfinish _ u _ (relatedOff_storeAll parameter data message reference state hrel ρ u) hall
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_storeAll parameter data message reference state hrel ρ hc u hl)
            (pairInv_storeAll parameter data message state hinv ρ u hl)
            (fun x hx => storeAll_cache_other _ _ _ _ fun call => Ne.symm (hx call)) _
  · rw [tsum_probOutput_pure_mul]
    rw [hVabort, mul_zero]
    exact zero_le

/-- **The scan from a start, weighted.** The weighted weight of the signed pair is at most the
initial weight times the walk value over the reference cache. The state may differ from the
reference by rejected blocks behind the start. -/
theorem loop_boundSW
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hVabort : ∀ s', V none s' = 0)
    (hVstore : ∀ r (s' : DebtState HashInput HashOutput Coordinate) (y : HashInput) (v : HashOutput),
      s'.cache y = none → V r s' ≤ V r (s'.store y v))
    (hVnone : ∀ s' : DebtState HashInput HashOutput Coordinate, Related parameter data message reference s' →
      V (some none) s' = 0)
    (hVfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate)
      (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.1 out.2 ≤ (if out.1.1.isSome then (pcache parameter data message out.2 ρ).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0)) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      PairInv parameter data message state →
      (∀ i, i < attempts → ∀ call,
        state.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call) =
        reference.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call)) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget state] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤
        weight tg initial state * walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro _ budget state ρ hrel _ _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        (weight tg initial out.2 * V out.1.1 out.2) ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change weight tg initial state * V (some none) state ≤ _
      rw [hVnone state hrel, mul_zero]
      exact bot_le
  | succ attempts ih =>
      intro hA budget state ρ hrel hinv hahead
      rw [signCostSourceLoop_succ]
      have hnext : ∀ s', Related parameter data message reference s' → PairInv parameter data message s' →
          (∀ x, (∀ call, x ≠ pblk parameter data message ρ call) → s'.cache x = state.cache x) → ∀ b,
          ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts (nextRand (data.steps message) ρ)) b s'] *
            (weight tg initial out.2 * V out.1.1 out.2) ≤
          weight tg initial s' * walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
            (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts
            (nextRand (data.steps message) ρ) := by
        intro s' hrel' hinv' hsame b
        refine ih (Nat.le_of_succ_le hA) b s' (nextRand (data.steps message) ρ) hrel' hinv'
          fun i hi call => ?_
        have hpow : (nextRand (data.steps message) ^ i) (nextRand (data.steps message) ρ) = (nextRand (data.steps message) ^ (i + 1)) ρ := by
          rw [pow_succ, Equiv.Perm.mul_apply]
        rw [hpow, hsame _ fun call' => pblk_ne_of_ne parameter data message
          (nextRand_pow_ne (data.steps message) ρ (i + 1) (Nat.succ_pos i) (by omega)) call call']
        exact hahead (i + 1) (Nat.succ_lt_succ hi) call
      refine le_trans (trial_boundSW tg initial model parameter data message hparse hkind reference ρ gf gp V
        hVabort hVstore (hVfin ρ) _ state hrel hinv (hahead 0 (Nat.succ_pos attempts)) _ hnext budget)
        (mul_le_mul_right ?_ _)
      have h0 : state.cache (blk parameter data message ρ) = reference.cache (blk parameter data message ρ) :=
        hahead 0 (Nat.succ_pos attempts) firstCall
      rw [h0]
      cases hc : reference.cache (blk parameter data message ρ) with
      | none =>
          have hst : stOf parameter data message reference ρ = .fresh := by simp [stOf, hc]
          rw [walk_succ_fresh _ _ _ _ hst]
          simp only [Option.elim]
          exact trials_sum_le parameter gf _
      | some u0 =>
          simp only [Option.elim]
          by_cases hl : Landed parameter (blockIndex u0)
          · have hst : stOf parameter data message reference ρ = .hit := by simp [stOf, hc, hl]
            rw [walk_succ_hit _ _ _ _ hst, if_pos hl]
          · have hst : stOf parameter data message reference ρ = .miss := by simp [stOf, hc, hl]
            rw [walk_succ_miss _ _ _ _ hst, if_neg hl]

/-- The combined weight of a non-signing outcome vanishes. -/
theorem comb_none (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (s' : DebtState HashInput HashOutput Coordinate) (hrel : Related parameter data message reference s') :
    freshNewWeight parameter data message reference gf ((some none, [], [], []), s') +
      outWeight parameter data message reference 0 gp ((some none, [], [], []), s') = 0 := by
  simp only [freshNewWeight, outWeight, Option.isSome_some, if_true, add_zero]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  split_ifs with hn
  · cases hpc : pcache parameter data message s' ρ with
    | none => rfl
    | some u =>
        have hfirst := pcache_some parameter data message hpc firstCall
        rcases hrel ρ with h | ⟨_, u0, hu', hnl⟩
        · rw [h, hn] at hfirst
          exact absurd hfirst (by simp)
        · have hwu : u firstCall = u0 := Option.some_inj.1 (hfirst.symm.trans hu')
          simp only [Option.elim, hwu]
          rw [if_neg hnl]
  · rfl

/-- The combined weight of an outcome only grows when a fresh input is stored. -/
theorem comb_store (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (r : Option (Option Signature)) (s' : DebtState HashInput HashOutput Coordinate)
    (y : HashInput) (v : HashOutput) (hy : s'.cache y = none) :
    freshNewWeight parameter data message reference gf ((r, [], [], []), s') +
        outWeight parameter data message reference 0 gp ((r, [], [], []), s') ≤
      freshNewWeight parameter data message reference gf ((r, [], [], []), s'.store y v) +
        outWeight parameter data message reference 0 gp ((r, [], [], []), s'.store y v) := by
  refine add_le_add ?_ ?_
  · simp only [freshNewWeight]
    split_ifs with hs
    · refine Finset.sum_le_sum fun ρ _ => ?_
      split_ifs with hn
      · cases hpc : pcache parameter data message s' ρ with
        | none => exact bot_le
        | some u => rw [pcache_store parameter data message hy ρ hpc]
      · exact le_rfl
    · exact le_rfl
  · rcases r with _ | (_ | sig)
    · exact le_rfl
    · exact le_rfl
    · show (pcache parameter data message s' sig.randomness).elim 0
          (pairWeight parameter data message reference 0 gp sig.randomness) ≤
        (pcache parameter data message (s'.store y v) sig.randomness).elim 0
          (pairWeight parameter data message reference 0 gp sig.randomness)
      cases hpc : pcache parameter data message s' sig.randomness with
      | none => exact bot_le
      | some u => rw [pcache_store parameter data message hy _ hpc]

/-- The combined weight of a completed assembly is the weight of its own pair. -/
theorem comb_fin (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ)
    (hoff : RelatedOff parameter data message reference s' ρ)
    (hs0 : ∀ call, s'.cache (pblk parameter data message ρ call) = some (u call))
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')) :
    freshNewWeight parameter data message reference gf ((out.1.1, [], [], []), out.2) +
      outWeight parameter data message reference 0 gp ((out.1.1, [], [], []), out.2) ≤
      (if out.1.1.isSome then (pcache parameter data message out.2 ρ).elim 0
        (pairWeight parameter data message reference gf gp ρ) else 0) := by
  have hpc : pcache parameter data message out.2 ρ = some u :=
    allSome_of_eq _ _ fun call =>
      (interp_extends tg initial model _ b s' out hout).1 _ _ (hs0 call)
  have hoffsame : ∀ ρ', ρ' ≠ ρ → pcache parameter data message out.2 ρ' =
      pcache parameter data message s' ρ' := by
    intro ρ' hρ'
    unfold pcache
    refine congrArg _ (funext fun call => ?_)
    exact finish_keeps_msg tg initial model parameter data message ρ b s' out hout _
      (msgInput_digestInput parameter data.root message ρ' call)
      fun call' => pblk_ne_of_ne parameter data message hρ' call call'
  by_cases hsome : out.1.1.isSome
  · rw [if_pos hsome, hpc]
    simp only [Option.elim]
    have hfresh : freshNewWeight parameter data message reference gf ((out.1.1, [], [], []), out.2) =
        if reference.cache (blk parameter data message ρ) = none then
          (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else 0) else 0 := by
      simp only [freshNewWeight, if_pos hsome]
      rw [Finset.sum_eq_single ρ]
      · simp only [hpc, Option.elim]
      · intro ρ' _ hne
        split_ifs with hn
        · rw [hoffsame ρ' hne]
          cases hpc' : pcache parameter data message s' ρ' with
          | none => rfl
          | some w =>
              have hfirst := pcache_some parameter data message hpc' firstCall
              rcases hoff ρ' hne with h | ⟨_, u0, hu', hnl⟩
              · rw [h, hn] at hfirst
                exact absurd hfirst (by simp)
              · have hwu : w firstCall = u0 := Option.some_inj.1 (hfirst.symm.trans hu')
                simp only [Option.elim, hwu]
                rw [if_neg hnl]
        · rfl
      · intro h; exact absurd (Finset.mem_univ ρ) h
    rw [hfresh]
    have hout' : outWeight parameter data message reference 0 gp ((out.1.1, [], [], []), out.2) ≤
        if reference.cache (blk parameter data message ρ) = none then 0 else gp ρ (viewOf u) := by
      have := outWeight_finish_le tg initial model parameter data message reference 0 gp ρ b s' out hout
      simp only [if_pos hsome, hpc, Option.elim, pairWeight] at this
      refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_))
      · rfl
      · split_ifs <;> rfl
    refine le_trans (add_le_add_right hout' _) (le_of_eq ?_)
    simp only [pairWeight]
    split_ifs <;> simp
  · rw [if_neg hsome]
    simp only [freshNewWeight, if_neg hsome, zero_add]
    unfold outWeight
    cases hr : out.1.1 with
    | none => rfl
    | some r => simp [hr] at hsome

/-- **The scan from a start, with the fresh pair it completes, weighted.** -/
theorem loop_bound_combSW
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      PairInv parameter data message state →
      (∀ i, i < attempts → ∀ call,
        state.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call) =
        reference.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call)) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget state] *
          (weight tg initial out.2 * (freshNewWeight parameter data message reference gf out +
            outWeight parameter data message reference 0 gp out)) ≤
        weight tg initial state * walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ :=
  loop_boundSW tg initial model parameter data message hparse hkind reference gf gp
    (fun r s' => freshNewWeight parameter data message reference gf ((r, [], [], []), s') +
      outWeight parameter data message reference 0 gp ((r, [], [], []), s'))
    (fun _ => by simp [freshNewWeight, outWeight])
    (fun r s' y v hy => comb_store parameter data message reference gf gp r s' y v hy)
    (comb_none parameter data message reference gf gp)
    (fun ρ s' u b hoff hs0 out hout => comb_fin tg initial model parameter data message reference gf gp
      ρ s' u b hoff hs0 out hout)

end LoopSW

end FORS.Security.GraphView
