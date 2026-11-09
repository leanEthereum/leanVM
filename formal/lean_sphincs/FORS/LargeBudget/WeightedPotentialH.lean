module

public import FORS.LargeBudget.WeightedPotential
public import FORS.CoverPotential.OneCoinH

@[expose] public section

/-! The weighted one-coin potential (`GoodW`) for programs over the honest-reading cost interface
(`CostSpecH`), the signer honest (`advProgH`). A signing call runs `signCostSourceH`, the honest form of the charged signer (`signCostSourceH_eq`):
its runs project onto those of the charged signer at a budget it never exhausts
(`tsum_interp_toHonest`, `mem_support_interp_toHonest`) and spend no budget
(`interp_toHonest_quiet`), so the charged signing bounds transfer, as in `OneCoinH`. -/

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
variable {H : Type} [HonestInputs H D] [Fintype R]

/-! ### Presampling and the weighted payments, with honest reads -/

/-- **Presampling an untargeted input keeps the weighted payments.** The payment of a step reads the
state only through its weight, which an untargeted store leaves alone, and the rest of the run
commutes with the presample (`presample_costStep`). -/
theorem wflag_presample_eq (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι H) α) :
    ∀ (budget : ℕ) (state : DebtState D R ι),
      ∑' s, Pr{let z ← presample x state}[z = s] * wflag tg initial model computation budget s =
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
        rcases input with (draw | (bytes | coordinate)) | (amount | honest)
        · rfl
        · simp only [wpays, h]
        · rfl
        · rfl
        · rfl
      simp only [wflag_query_bind]
      split_ifs with hcost
      · set K : (SourceCostSpec D R ι H).Range input × DebtState D R ι → ℝ≥0∞ := fun r =>
          wpays tg initial state input +
            wflag tg initial model (next r.1) (budget - sourceCost input) r.2 with hK
        have hleft : ∑' s, Pr{let z ← presample x state}[z = s] *
            ∑' r, Pr{let z ← costStep model input s}[z = r] *
              (wpays tg initial s input +
                wflag tg initial model (next r.1) (budget - sourceCost input) r.2) =
            ∑' s, Pr{let z ← presample x state}[z = s] * ∑' r, Pr{let z ← costStep model input s}[z = r] * K r := by
          refine tsum_congr fun s => ?_
          by_cases hs : s ∈ support (presample x state)
          · rw [hpay s hs]
          · rw [prEvent_eq_zero_of_not_mem_support _ hs, zero_mul, zero_mul]
        have hcomm := presample_costStepH model x input state (fun r => (pure r : ProbComp _))
        simp only [bind_pure] at hcomm
        rw [hleft, ← OracleComp.tsum_prEvent_bind_mul]
        calc ∑' r, Pr{let z ← presample x state >>= fun s => costStep model input s}[z = r] * K r
            = ∑' r, Pr{let z ← (costStep model input state >>= fun r =>
                presample x r.2 >>= fun s => (pure (r.1, s) : ProbComp _))}[z = r] * K r :=
              tsum_congr fun r => congrArg (· * K r) (hcomm.prEvent_eq (· = r))
          _ = ∑' r, Pr{let z ← costStep model input state}[z = r] *
                ∑' s, Pr{let z ← presample x r.2}[z = s] * K (r.1, s) := by
              rw [OracleComp.tsum_prEvent_bind_mul]
              refine tsum_congr fun r => congrArg _ ?_
              rw [OracleComp.tsum_prEvent_bind_mul]
              exact tsum_congr fun s => by rw [OracleComp.tsum_prEvent_pure_mul]
          _ = ∑' r, Pr{let z ← costStep model input state}[z = r] * K r := by
              refine tsum_congr fun r => congrArg _ ?_
              simp only [hK]
              have hsplit : (∑' s, Pr{let z ← presample x r.2}[z = s] *
                    (wpays tg initial state input +
                      wflag tg initial model (next r.1) (budget - sourceCost input) s)) =
                  (∑' s, Pr{let z ← presample x r.2}[z = s] * wpays tg initial state input) +
                    ∑' s, Pr{let z ← presample x r.2}[z = s] *
                      wflag tg initial model (next r.1) (budget - sourceCost input) s := by
                rw [← ENNReal.tsum_add]
                exact tsum_congr fun s => mul_add _ _ _
              rw [hsplit, ENNReal.tsum_mul_right, presample_mass, one_mul,
                ih r.1 (budget - sourceCost input) r.2]
      · simp only [mul_zero, tsum_zero]

/-- Presampling one fresh untargeted input keeps the weighted payments. -/
theorem wflag_presample_fresh_eq (x : D) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι H) α) (budget : ℕ) (state : DebtState D R ι)
    (hx : state.cache x = none) :
    wflag tg initial model computation budget state =
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, wflag tg initial model computation budget (state.store x v) := by
  rw [← wflag_presample_eq tg initial model x hk computation budget state, presample_fresh x state hx,
    OracleComp.tsum_prEvent_map_mul, tsum_uniform_eq]

/-- **Presampling an injective family of fresh untargeted inputs** keeps the weighted payments. -/
theorem wflag_presampleAll_eq {α : Type} (computation : OracleComp (SourceCostSpec D R ι H) α) (budget : ℕ) :
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
    (hk : ∀ i, tg.kind (x i) = .none) (c : Fin n) (next : R → OracleComp (SourceCostSpec D R ι H) α)
    (budget : ℕ) (state : DebtState D R ι) (hfresh : ∀ i, state.cache (x i) = none) :
    ∑' v, Pr{let z ← ($ᵗ R : ProbComp R)}[z = v] *
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

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Weighted paid programs with the honest signer -/

section GoodW

variable (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The weighted one-coin potential for programs with honest reads, the count invariant for the live
messages only. -/
def GoodW (L : QueryLog SigningSpec) (prog : OracleComp CostSpecH HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → MInv parameter data s Ms → DInv R d →
      CountInvL parameter data Qtot L s budget →
      ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
        weight tg initial s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wflag tg initial model prog budget s

/-- The weighted final value is at most the initial weight in the mean. -/
theorem finalWH_le (prog : OracleComp CostSpecH HiddenBridge.Outcome) (budget : ℕ) (s : State) (R : List Coordinate) :
    ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] *
        (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤ weight tg initial s := by
  refine le_trans (interp_weight_mul_leW tg initial model prog budget s _ 1 fun out _ => ?_) (mul_one _).le
  unfold finalValue
  cases out.1.1 with
  | none => exact zero_le_one
  | some outcome =>
      simp only [Option.elim]
      split_ifs
      · exact le_rfl
      · exact zero_le_one

theorem goodWH_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (next v)) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L
      (liftM (CostSpecH.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  have hw : wflag tg initial model (liftM (CostSpecH.query (.inl (.inl draw))) >>= next) budget s =
      ∑' v, Pr{let x ← (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))}[x = v] *
        wflag tg initial model (next v) budget s := by
    rw [wflag_query_bind]
    refine (ite_eq_left (Nat.zero_le budget)).trans ?_
    change ∑' r, Pr{let x ← (fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)}[x = r] *
      (0 + wflag tg initial model (next r.1) (budget - 0) r.2) = _
    rw [OracleComp.tsum_prEvent_map_mul]
    simp only [zero_add, Nat.sub_zero]
  rw [hw, interp_drawH, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' v, Pr{let x ← (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))}[x = v] *
        (weight tg initial s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wflag tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hprep hP hM hD hC) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) (le_of_eq ?_)
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

theorem finalValueWH_ordinary (R : List Coordinate) (x : HashInput)
    (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome) (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    ∑' out, Pr{let y ← interp tg initial model (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) budget s}[y = out] *
        (weight tg initial out.2 * finalValue parameter data tg initial R out) =
      ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
        ∑' out, Pr{let x ← interp tg initial model (next r.1) (budget - 1) r.2}[x = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) := by
  rw [interp_ordinaryHB, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
  simp only [OracleComp.tsum_prEvent_map_mul]
  rfl

theorem wflag_ordinary (x : HashInput) (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    wflag tg initial model (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) budget s =
      ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
        (wpays (H := HashInput) tg initial s (.inl (.inr (.inl x))) + wflag tg initial model (next r.1) (budget - 1) r.2) := by
  rw [wflag_query_bind, costStep_ordinary]
  exact ite_eq_left hb

/-- A new pair: one of its blocks is read fresh and the others are presampled, weighted. The blocks
are untargeted, so the presample keeps both the weight (`weight_storeAllW`) and the weighted
payments (`wflag_presample_new_eq`). -/
theorem new_pair_boundW {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hC : CountInvL parameter data Qtot L s budget) (p : Pair) (c : DigestCall)
    (hkind : ∀ call, tg.kind (pblk parameter data p call) = .none)
    (hp0 : s.cache (pblk parameter data p firstCall) = none) :
    ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
        ∑' out, Pr{let z ← (interp tg initial model (next v) (budget - 1)
          (s.store (pblk parameter data p c) v))}[z = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
        b0 * (weight tg initial s +
          ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
            wflag tg initial model (next v) (budget - 1) (s.store (pblk parameter data p c) v)) := by
  set ℓ := (livePairs L P).length with hℓ
  have hfresh : ∀ call, s.cache (pblk parameter data p call) = none := hP.first p hp0
  have hwall : ∀ u : DigestCall → HashOutput,
      weight tg initial (withPair parameter data s p u) = weight tg initial s := fun u =>
    weight_storeAllW tg initial (pblk parameter data p) u s hkind
  have hpairE : ∀ F : (DigestCall → HashOutput) → ℝ≥0∞,
      pairE F = ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * ∑ u, F u := by
    intro F
    unfold pairE
    rw [tsum_uniform_eq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  -- the weighted final value only grows when a block of the pair is presampled
  have hFmono : ∀ (out : Run HashInput Coordinate HiddenBridge.Outcome × State) (i : DigestCall)
      (v : HashOutput), out.2.cache (pblk parameter data p i) = none →
      weight tg initial out.2 * finalValue parameter data tg initial R out ≤
        weight tg initial (out.2.store (pblk parameter data p i) v) *
          finalValue parameter data tg initial R (out.1, out.2.store (pblk parameter data p i) v) := by
    intro out i v hc
    rw [weight_store_untargetedW tg initial out.2 _ v (hkind i)]
    refine mul_le_mul_right ?_ _
    have hgrow := (extends_store out.2 (pblk parameter data p i) v hc).1
    unfold finalValue
    cases out.1.1 with
    | none => exact le_rfl
    | some outcome =>
        simp only [Option.elim]
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd ⟨forsCover_mono parameter data.root outcome _ hgrow h1.1, fun hreal =>
            h1.2 ((realized_store_untargeted tg initial out.2 _ v (hkind i)).1 hreal)⟩ h2
        · exact bot_le
        · exact le_rfl
  have hpre : ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
        ∑' out, Pr{let z ← (interp tg initial model (next v) (budget - 1)
          (s.store (pblk parameter data p c) v))}[z = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      pairE (fun u => ∑' out, Pr{let z ← (interp tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u))}[z = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out)) := by
    rw [hpairE]
    exact interp_presample_newF tg initial model (pblk parameter data p)
      (pblk_call_injective parameter data p) hkind c next (budget - 1) s hfresh _ hFmono
  have hcount : pairE (fun u => wflag tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u)) =
      ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
        wflag tg initial model (next v) (budget - 1) (s.store (pblk parameter data p c) v) := by
    rw [hpairE]
    exact (wflag_presample_new_eq tg initial model (pblk parameter data p)
      (pblk_call_injective parameter data p) hkind c next (budget - 1) s hfresh).symm
  by_cases hcap : 1 ≤ lam Lmax ℓ budget
  · -- more landed pairs than the cap: the cap term pays everything
    calc _ ≤ ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] * weight tg initial s :=
          ENNReal.tsum_le_tsum fun v => mul_le_mul_right
            ((finalWH_le parameter data tg initial model (next v) (budget - 1) _ R).trans
              (weight_store_untargetedW tg initial s _ v (hkind c)).le) _
      _ ≤ weight tg initial s := by
          rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
      _ ≤ weight tg initial s * lam Lmax ℓ budget := le_mul_of_one_le_right' hcap
      _ ≤ _ := by
          unfold potO
          exact le_trans (mul_le_mul' le_rfl le_add_self) le_self_add
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  have hrate : MsgLive L p.1 → Rate parameter data w s p.1 := fun hlive =>
    rate_of_fair hfair s p.1 (by have := hC p.1 hlive; omega) (le_trans (landedCount_le hP L hlive) hlen)
  have hC2 : ∀ a, CountInvL parameter data Qtot L (withPair parameter data s p a) (budget - 1) := by
    intro a mm hmm
    have h1 := count_withPair (parameter := parameter) (data := data) mm s p a
    have h2 := hC mm hmm
    omega
  have hone : ∀ u, ∑' out, Pr{let x ← (interp tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u))}[x = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potO parameter data w b0 Fail tg initial Lmax (withPair parameter data s p u)
          (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) +
        b0 * wflag tg initial model (next (u c)) (budget - 1) (withPair parameter data s p u) := fun u => by
    have := h (u c) (budget - 1) _ _ _ d R
      (fun x v hx => (extends_withPair hP hp0 u).1 x v (hprep x v hx)) (pinv_withPair hP hp0 u)
      (minv_withPair hM p u) hD (hC2 u)
    rwa [hwall u] at this
  refine le_trans (le_trans hpre (pairE_mono hone)) ?_
  rw [pairE_add, pairE_const_mul, pairE_const_mul, hcount, mul_add, ← add_assoc]
  refine add_le_add ?_ le_rfl
  calc weight tg initial s * pairE (fun u => potO parameter data w b0 Fail tg initial Lmax
          (withPair parameter data s p u) (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1))
      ≤ weight tg initial s * (potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * (if Realized tg initial s then 0 else 1)) :=
        mul_le_mul_right (new_pair_core parameter data w b0 Fail Lmax tg initial hfair.le_one L budget hb s P Ms d
          hP hM p hp0 hrate) _
    _ ≤ _ := by
        rw [mul_add]
        refine add_le_add le_rfl ?_
        rw [mul_left_comm]
        refine mul_le_mul_right ?_ _
        split_ifs <;> simp

/-- **One ordinary query, weighted.** -/
theorem goodWH_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (next v)) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L
      (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinaryHB, ite_eq_right hb, OracleComp.tsum_prEvent_pure_mul, finalValue_abort, mul_zero]
    exact bot_le
  rw [finalValueWH_ordinary parameter data tg initial model R x next budget hb s,
    wflag_ordinary tg initial model x next budget hb s]
  by_cases hnew : ∃ (p : Pair) (call : DigestCall), x = pblk parameter data p call ∧
      s.cache (pblk parameter data p firstCall) = none
  · obtain ⟨p, c, rfl, hp0⟩ := hnew
    have hfresh : ∀ call, s.cache (pblk parameter data p call) = none := hP.first p hp0
    rw [ordinaryStep, hparse p c]
    simp only
    rw [readOutside_fresh _ s (hfresh c), OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
    have hpay : wpays (H := HashInput) tg initial s (.inl (.inr (.inl (pblk parameter data p c)))) = weight tg initial s := by
      change (if tg.digest (pblk parameter data p c) then weight tg initial s else 0) = _
      rw [ite_eq_left (hdigest p c)]
    rw [hpay]
    have hsum : ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] *
        (weight tg initial s +
          wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p c) u)) =
        weight tg initial s + ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] *
          wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p c) u) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one _,
        one_mul]
    rw [hsum]
    exact new_pair_boundW parameter data w b0 Fail Qtot Lmax tg initial model hfair hQ L next h budget hb
      s P Ms d R hprep hP hM hD hC p c (hkind p) hp0
  · have hmean : ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] * weight tg initial r.2 ≤ weight tg initial s := by
      exact meanWeight_ordinary_leW tg initial model x s
    calc _ ≤ ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
          (weight tg initial r.2 * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
            b0 * wflag tg initial model (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ?_ _
            have hext := ordinaryStep_extends model x s r hr
            have hblocks := same_blocks (parameter := parameter) (data := data) hext
              (ordinaryStep_cache_ne model x s r hr) hnew
            obtain ⟨hP', -⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hP
            have hcnt : CountInvL parameter data Qtot L r.2 (budget - 1) := by
              intro m hm
              have h1 : cachedCount parameter data m r.2 ≤ cachedCount parameter data m s + 1 := by
                rw [cachedCount_eq, cachedCount_eq]
                exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
              have h2 := hC m hm
              omega
            have hland : ∀ q, LandedIn parameter data s q → ∀ call,
                r.2.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) :=
              fun q hq call => landed_blocks hext hP hq call
            refine le_trans (h r.1 (budget - 1) r.2 P Ms d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' (minv_blocks hblocks hM) hD hcnt) (add_le_add ?_ le_rfl)
            exact mul_le_mul_right
              (potO_grow w b0 Fail tg initial hfair.le_one Lmax hext hblocks hland
                (fun q hq => (hP.mem q).1 hq) Ms L d (Nat.sub_le _ _)) _
          · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add]
          refine add_le_add ?_ ?_
          · calc _ = (∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] * weight tg initial r.2) *
                  potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget := by
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun r => by ring
              _ ≤ _ := mul_le_mul_left hmean _
          · refine le_add_left (le_of_eq ?_)
            simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **Leaf, weighted.** -/
theorem goodWH_pure (hw : w ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R hprep hP hM hD _
  have h := goodO_pure parameter data w b0 Fail (Fintype.card Randomness + budget) Lmax tg initial model hw L
    forgery verified budget s P Ms d R hprep hP hM hD (countInv_card parameter data s budget)
  have hflag : expectedFlagged tg initial model (pure (forgery, L, verified) : OracleComp CostSpec _) budget s = 0 := by
    unfold expectedFlagged
    rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
    simp [flaggedCount]
  rw [hflag, mul_zero, add_zero, interp_pure, OracleComp.tsum_prEvent_pure_mul] at h
  rw [wflag_pure, mul_zero, add_zero, interp_pure, OracleComp.tsum_prEvent_pure_mul]
  exact mul_le_mul_right h _

/-- Hash computations lifted onto the raw summand are sequences of ordinary queries. -/
theorem goodWH_liftRaw (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) {α : Type}
    (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ a, GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (next a)) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L
      (simulateQ (fun q => liftM (CostSpecH.query (.inl (.inr (.inl q)))) :
        QueryImpl HashSpec (OracleComp CostSpecH)) computation >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact goodWH_ordinary parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hdigest hfair hQ L
        query _ ih

/-- **One honest signing call, weighted**, on a message that was never signed before: the charged
bounds through the coupling of the honest signer with the charged one. -/
theorem goodWH_signH (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (m : Message) (L : QueryLog SigningSpec) (hm : MsgLive L m)
    (next : Option Signature → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ r, GoodW parameter data w b0 Fail Qtot Lmax tg initial model (L ++ [⟨m, r⟩]) (next r)) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (signCostSourceH parameter data m >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  have hsignEq := signCostSourceH_eq parameter data m
  set ℓ := (livePairs L P).length with hℓ
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => wflag tg initial model (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
  have hproj : ∀ o1 : Run HashInput Coordinate (Option Signature) × State,
      canonR o1 = canonR ((o1.1.1, o1.1.2.1, [], []), o1.2) := fun o1 => by
    simp only [hcanonR, canonO_congr (o := o1) (o' := ((o1.1.1, o1.1.2.1, [], []), o1.2)) rfl rfl]
  obtain ⟨B, hB, hsum⟩ := tsum_interp_toHonest tg initial model (signCostSource parameter data m)
    (fun p => weight tg initial p.2 * canonR ((p.1.1, p.1.2, [], []), p.2)) budget s
  have hpoint : ∀ o1 ∈ support (interp tg initial model (signCostSourceH parameter data m) budget s),
      ∑' out, Pr{let x ← interpThen tg initial model next budget o1}[x = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
        weight tg initial o1.2 * (canonR o1 + lam Lmax ℓ budget) + b0 * cont o1 := by
    intro o1 ho1
    rw [hsignEq] at ho1
    obtain ⟨htr, -⟩ := interp_toHonest_quiet tg initial model _ budget s o1 ho1
    have hbud : budget - traceCost o1.1.2.2.1 = budget := by rw [htr]; simp [traceCost]
    obtain ⟨o1', ho1', hpr⟩ := mem_support_interp_toHonest tg initial model _ B hB budget s o1 ho1
    have h11 : o1'.1.1 = o1.1.1 := congrArg (fun p => p.1.1) hpr
    have h121 : o1'.1.2.1 = o1.1.2.1 := congrArg (fun p => p.1.2) hpr
    have h2 : o1'.2 = o1.2 := congrArg (fun p => p.2) hpr
    cases hres : o1.1.1 with
    | none =>
        rw [interpThenH_none tg initial model next budget o1 hres, OracleComp.tsum_prEvent_pure_mul]
        have h0 : finalValue parameter data tg initial R ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) = 0 := rfl
        rw [h0, mul_zero]
        exact bot_le
    | some r =>
        rw [interpThenH_some tg initial model next budget o1 r hres, OracleComp.tsum_prEvent_map_mul, hbud]
        have hres' : o1'.1.1 = some r := h11.trans hres
        have hdisc : discAfter parameter data m s d o1' = discAfter parameter data m s d o1 :=
          discAfter_congr h11 h2
        obtain ⟨hprep', hP', hM', hD', -, -⟩ := sign_paramsS tg initial model Fail (Fintype.card Randomness + B)
          hparse (hfail m) B s P Ms d R hprep hP hM hD (countInv_card parameter data s B) o1' ho1' r hres'
        rw [h2] at hprep' hP' hM'
        rw [h121, hdisc] at hD'
        have hC' : CountInvL parameter data Qtot (L ++ [⟨m, r⟩]) o1.2 budget := by
          intro m' hm'
          have hne : m' ≠ m := fun he => hm' ⟨m, r⟩ (List.mem_append_right _ (List.mem_singleton_self _)) he.symm
          have hlive : MsgLive L m' := fun e he => hm' e (List.mem_append_left _ he)
          have hkeep : cachedCount parameter data m' o1.2 = cachedCount parameter data m' s := by
            unfold cachedCount
            refine congrArg Finset.card (Finset.filter_congr fun ρ _ => ?_)
            have hk := other_message_keptS tg initial model B s o1' ho1' (m', ρ) hne firstCall
            rw [h2] at hk
            exact Iff.of_eq (congrArg (· ≠ none) hk)
          have := hC m' hlive
          omega
        have hIH := h r budget o1.2 _ _ _ _ hprep' hP' hM' hD' hC'
        have hpot := sign_pointO2 tg initial model parameter data w b0 Fail (Fintype.card Randomness + B) m hparse
          (hfail m) hw B budget s P Ms L d R hprep hP hM hD (countInv_card parameter data s B) o1' ho1' r hres'
          (le_refl budget)
        rw [h2, hdisc, canonO_congr h11 h2] at hpot
        have hlam : lam Lmax (livePairs (L ++ [⟨m, r⟩]) (newPairs parameter data m s o1.2 ++ P)).length
            budget ≤ lam Lmax ℓ budget := by
          refine lam_mono ?_ le_rfl
          unfold livePairs
          rw [List.filter_append]
          have hnew : (newPairs parameter data m s o1.2).filter
              (fun q => decide (MsgLive (L ++ [⟨m, r⟩]) q.1)) = [] := by
            refine List.filter_eq_nil_iff.2 fun q hq => ?_
            obtain ⟨hqm, _, _⟩ := (mem_newPairs parameter data m s).1 hq
            simp only [decide_eq_true_eq, msgLive_append, not_and, not_not]
            exact fun _ => hqm
          rw [hnew, List.nil_append]
          refine (List.Sublist.length_le ?_)
          refine List.monotone_filter_right _ fun q hq => ?_
          simp only [decide_eq_true_eq, msgLive_append] at hq ⊢
          exact hq.1
        have heq : ∀ o2 : Run HashInput Coordinate HiddenBridge.Outcome × State,
            finalValue parameter data tg initial R
              ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2) =
            finalValue parameter data tg initial (R ++ o1.1.2.1) o2 := by
          intro o2
          unfold finalValue
          simp only [List.append_assoc]
        simp only [heq]
        refine le_trans hIH (add_le_add (mul_le_mul' le_rfl ?_) ?_)
        · unfold potO
          exact add_le_add hpot hlam
        · simp only [hcont, hres, Option.elim, hbud, le_refl]
  have hflag : ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
      cont o1 ≤ wflag tg initial model (signCostSourceH parameter data m >>= next) budget s := by
    rw [wflag_bind]
    exact le_add_self
  have hcanon : ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
      (weight tg initial o1.2 * canonR o1) ≤
      weight tg initial s * (if Realized tg initial s ∨ signatureLimit < L.length then 0
        else coreO parameter data w b0 Fail s P Ms L d (signatureLimit - L.length) budget) := by
    calc _ = ∑' o1, Pr{let x ← (interp tg initial model (simulateQ toHonest (signCostSource parameter data m))
            budget s)}[x = o1] * (weight tg initial (runProj o1).2 *
              canonR (((runProj o1).1.1, (runProj o1).1.2, [], []), (runProj o1).2)) := by
          rw [hsignEq]
          exact tsum_congr fun o1 => by rw [hproj o1]; rfl
      _ = ∑' o1, Pr{let x ← interp tg initial model (signCostSource parameter data m) B s}[x = o1] *
            (weight tg initial (runProj o1).2 *
              canonR (((runProj o1).1.1, (runProj o1).1.2, [], []), (runProj o1).2)) := hsum
      _ = ∑' o1, Pr{let x ← interp tg initial model (signCostSource parameter data m) B s}[x = o1] *
            (weight tg initial o1.2 * canonR o1) :=
          tsum_congr fun o1 => by rw [hproj o1]; rfl
      _ ≤ _ := sign_expectW2 tg initial model parameter data w b0 Fail m hparse hkind B budget s P Ms L hm d hP hM
  rw [interp_bind, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
        (weight tg initial o1.2 * (canonR o1 + lam Lmax ℓ budget) + b0 * cont o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model (signCostSourceH parameter data m) budget s)
        · exact mul_le_mul_right (hpoint o1 ho1) _
        · rw [(prEvent_eq_zero_of_not_mem_support _) ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
            (weight tg initial o1.2 * canonR o1) +
          ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
            (weight tg initial o1.2 * lam Lmax ℓ budget) +
          b0 * ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
            cont o1 := by
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ b0, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        unfold potO
        rw [mul_add]
        exact add_le_add (add_le_add hcanon
          (interp_weight_mul_leW tg initial model (signCostSourceH parameter data m) budget s
            (fun _ => lam Lmax ℓ budget) _ fun _ _ => le_rfl)) (mul_le_mul_right hflag _)

theorem goodWH_finish (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (finishGameH parameter data L forgery) := by
  unfold finishGameH
  exact goodWH_liftRaw parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hdigest hfair hQ L _ _
    fun v => goodWH_pure parameter data w b0 Fail Qtot Lmax tg initial model hfair.le_one L forgery v

/-- **The weighted one-coin potential through any adversary that never repeats a message**, the
signer honest. -/
theorem goodWH_advProgH (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (advProgH parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProgH_pure]
      exact goodWH_finish parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hdigest hfair hQ L
        forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProgH_draw]
        exact goodWH_draw parameter data w b0 Fail Qtot Lmax tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProgH_hash]
        exact goodWH_ordinary parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hdigest hfair hQ
          L bytes _ fun v => ih v L (hnr v)
      · rw [advProgH_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodWH_signH parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hfail hfair.le_one
          message L hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end GoodW

end FORS.Security.ForsPotential
