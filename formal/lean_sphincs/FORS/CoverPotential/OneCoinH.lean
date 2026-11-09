module

public import FORS.CoverPotential.Game
public import FORS.Reduction.NoRepeat
public import FORS.CoverPotential.OneCoin
public import FORS.CoverPotential.GameH
public import FORS.LargeBudget.HonestCoupling
public import FORS.SmallBudget.Contact.HonestBase

@[expose] public section

/-! The one-coin potential (`GoodO`) for programs over the honest-reading cost interface
(`CostSpecH`), the signer honest (`advProgH`). The adversary's steps are those of `GoodO`. A
signing call runs `signCostSourceH`, the honest form of the charged signer (`signCostSourceH_eq`):
its runs project onto those of the charged signer at a budget it never exhausts
(`tsum_interp_toHonest`, `mem_support_interp_toHonest`) and spend no budget
(`interp_toHonest_quiet`), so the charged signing bounds transfer, their budgets decoupled
(`sign_pointO2`, `sign_expectO2`). Honest reads may cache digest blocks of the signed message for
free, so the count invariant is kept for the live messages only (`CountInvL`), which is all the
potential reads. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### The count invariant of the live messages -/

section CountL

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ)

/-- `CountInv` for the messages not signed yet. -/
def CountInvL (L : QueryLog SigningSpec) (s : State) (budget : ℕ) : Prop :=
  ∀ m : Message, MsgLive L m → cachedCount parameter data m s + budget ≤ Qtot

theorem countInvL_of_countInv {L : QueryLog SigningSpec} {s : State} {budget : ℕ}
    (h : CountInv parameter data Qtot s budget) : CountInvL parameter data Qtot L s budget := fun m _ => h m

/-- `CountInv` holds for a total above the number of randomizers. -/
theorem countInv_card (s : State) (budget : ℕ) :
    CountInv parameter data (Fintype.card Randomness + budget) s budget := fun m => by
  have h : cachedCount parameter data m s ≤ Fintype.card Randomness :=
    (Finset.card_filter_le _ _).trans (Finset.card_univ.le)
  omega

end CountL

/-! ### Signing outcomes with the same result and state -/

section Congr

variable {parameter : PublicParameter} {data : PublicData} {w b0 : ℝ≥0∞} {Fail : Finset (Fin (2 ^ subtreeHeight))}
  {m : Message} {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec} {d : Multiset View}

theorem discAfter_congr {o o' : Run HashInput Coordinate (Option Signature) × State} (h1 : o.1.1 = o'.1.1)
    (h2 : o.2 = o'.2) : discAfter parameter data m s d o = discAfter parameter data m s d o' := by
  obtain ⟨⟨a, b, c, e⟩, st⟩ := o
  obtain ⟨⟨a', b', c', e'⟩, st'⟩ := o'
  simp only at h1 h2
  subst h1 h2
  rfl

theorem canonO_congr {o o' : Run HashInput Coordinate (Option Signature) × State} (h1 : o.1.1 = o'.1.1)
    (h2 : o.2 = o'.2) {n k : ℕ} :
    canonO parameter data w b0 Fail m s P Ms L d n k o = canonO parameter data w b0 Fail m s P Ms L d n k o' := by
  obtain ⟨⟨a, b, c, e⟩, st⟩ := o
  obtain ⟨⟨a', b', c', e'⟩, st'⟩ := o'
  simp only at h1 h2
  subst h1 h2
  rfl

end Congr

/-! ### Presampling the other calls of a pair, with honest reads -/

section PresampleFamilyH

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- `interp_presample_fresh_le` with honest reads. -/
theorem interp_presample_fresh_leF (x : HashInput) (hk : tg.kind x = .none) {α : Type}
    (computation : OracleComp CostSpecH α) (budget : ℕ) (state : State) (hx : state.cache x = none)
    (F : Run HashInput Coordinate α × State → ℝ≥0∞)
    (hF : ∀ out (v : HashOutput), out.2.cache x = none → F out ≤ F (out.1, out.2.store x v)) :
    ∑' out, Pr{let z ← interp tg initial model computation budget state}[z = out] * F out ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr{let z ← (interp tg initial model
        computation budget (state.store x v))}[z = out] * F out := by
  refine le_trans (interp_presample_leH tg initial model x hk computation budget state F fun out s hs => ?_) ?_
  · cases hc : out.2.cache x with
    | some w =>
        rw [presample_cached x out.2 w hc, support_pure, Set.mem_singleton_iff] at hs
        rw [hs]
    | none =>
        rw [presample_fresh x out.2 hc, support_map] at hs
        obtain ⟨v, _, rfl⟩ := hs
        exact hF out v hc
  · rw [presample_fresh x state hx, OracleComp.tsum_prEvent_map_mul, tsum_uniform_eq]

set_option maxRecDepth 100000 in
/-- `interp_presampleAll_le` with honest reads. -/
theorem interp_presampleAll_leF {α : Type} (computation : OracleComp CostSpecH α) (budget : ℕ)
    (F : Run HashInput Coordinate α × State → ℝ≥0∞) :
    ∀ {n : ℕ} (x : Fin n → HashInput), Function.Injective x → (∀ i, tg.kind (x i) = .none) →
      (∀ out (i : Fin n) (v : HashOutput), out.2.cache (x i) = none →
        F out ≤ F (out.1, out.2.store (x i) v)) →
      ∀ state : State, (∀ i, state.cache (x i) = none) →
        ∑' out, Pr{let z ← interp tg initial model computation budget state}[z = out] * F out ≤
          ((Fintype.card HashOutput : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → HashOutput,
            ∑' out, Pr{let z ← interp tg initial model computation budget (storeAll x u state)}[z = out] * F out
  | 0, _, _, _, _, _, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hk, hF, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      refine le_trans (interp_presample_fresh_leF tg initial model (x 0) (hk 0) computation budget state
        (hfresh 0) F fun out v hc => hF out 0 v hc) ?_
      have hrest : ∀ v, ∑' out, Pr{let z ← (interp tg initial model computation budget
            (state.store (x 0) v))}[z = out] * F out ≤
          ((Fintype.card HashOutput : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → HashOutput, ∑' out,
            Pr{let z ← (interp tg initial model computation budget
              (storeAll (Fin.tail x) w (state.store (x 0) v)))}[z = out] * F out := fun v =>
        interp_presampleAll_leF computation budget F (Fin.tail x) hxt (fun i => hk i.succ)
          (fun out i v' hc => hF out i.succ v' hc) _ fun i => by
            show (state.store (x 0) v).cache (x i.succ) = none
            rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
            exact hfresh i.succ
      calc (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr{let z ← (interp tg initial model
              computation budget (state.store (x 0) v))}[z = out] * F out
          ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card HashOutput : ℝ≥0∞) ^ n)⁻¹ *
              ∑ w : Fin n → HashOutput, ∑' out, Pr{let z ← (interp tg initial model computation budget
                (storeAll (Fin.tail x) w (state.store (x 0) v)))}[z = out] * F out) := by
            gcongr with v
            exact hrest v
        _ = ((Fintype.card HashOutput : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → HashOutput,
              ∑' out, Pr{let z ← (interp tg initial model computation budget
                (storeAll x (Fin.cons v w) state))}[z = out] * F out := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            refine congrArg (fun z : ℝ≥0∞ => ((Fintype.card HashOutput : ℝ≥0∞) ^ (n + 1))⁻¹ * z) ?_
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => HashOutput) _ _ fun _ => rfl

set_option maxRecDepth 100000 in
/-- `interp_presample_new` with honest reads. -/
theorem interp_presample_newF {α : Type} {n : ℕ} (x : Fin n → HashInput) (hx : Function.Injective x)
    (hk : ∀ i, tg.kind (x i) = .none) (c : Fin n) (next : HashOutput → OracleComp CostSpecH α)
    (budget : ℕ) (state : State) (hfresh : ∀ i, state.cache (x i) = none)
    (F : Run HashInput Coordinate α × State → ℝ≥0∞)
    (hF : ∀ out (i : Fin n) (v : HashOutput), out.2.cache (x i) = none →
      F out ≤ F (out.1, out.2.store (x i) v)) :
    ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
        ∑' out, Pr{let z ← interp tg initial model (next v) budget (state.store (x c) v)}[z = out] * F out ≤
      ((Fintype.card HashOutput : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → HashOutput,
        ∑' out, Pr{let z ← interp tg initial model (next (u c)) budget (storeAll x u state)}[z = out] * F out := by
  obtain ⟨mm, rfl⟩ : ∃ mm, n = mm + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (mm + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (mm + 1) → HashInput := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, ∑' out, Pr{let z ← (interp tg initial model (next v) budget
        (state.store (x c) v))}[z = out] * F out ≤
      ((Fintype.card HashOutput : ℝ≥0∞) ^ mm)⁻¹ * ∑ w : Fin mm → HashOutput, ∑' out,
        Pr{let z ← interp tg initial model (next v) budget (storeAll x' (Fin.cons v w) state)}[z = out] * F out := by
    intro v
    rw [← hx'0]
    exact interp_presampleAll_leF tg initial model (next v) budget F (Fin.tail x') hxt
      (fun i => hk _) (fun out i v' hc => hF out (σ i.succ) v' hc) _ fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr{let z ← (interp tg initial model (next v) budget
          (state.store (x c) v))}[z = out] * F out
      ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card HashOutput : ℝ≥0∞) ^ mm)⁻¹ *
          ∑ w : Fin mm → HashOutput, ∑' out, Pr{let z ← (interp tg initial model (next v) budget
            (storeAll x' (Fin.cons v w) state))}[z = out] * F out) := by
        gcongr with v
        exact hrest v
    _ = ((Fintype.card HashOutput : ℝ≥0∞) ^ (mm + 1))⁻¹ * ∑ v, ∑ w : Fin mm → HashOutput,
          ∑' out, Pr{let z ← (interp tg initial model (next v) budget
            (storeAll x' (Fin.cons v w) state))}[z = out] * F out := by
        rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
          (Or.inl (ENNReal.natCast_ne_top _))]
    _ = ((Fintype.card HashOutput : ℝ≥0∞) ^ (mm + 1))⁻¹ * ∑ u' : Fin (mm + 1) → HashOutput,
          ∑' out, Pr{let z ← interp tg initial model (next (u' 0)) budget (storeAll x' u' state)}[z = out] * F out := by
        refine congrArg (fun z : ℝ≥0∞ => ((Fintype.card HashOutput : ℝ≥0∞) ^ (mm + 1))⁻¹ * z) ?_
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Fin.consEquiv fun _ => HashOutput) _ _ fun _ => rfl
    _ = _ := by
        refine congrArg (fun z : ℝ≥0∞ => ((Fintype.card HashOutput : ℝ≥0∞) ^ (mm + 1))⁻¹ * z) ?_
        refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl HashOutput)) _ _ fun u' => ?_
        have hu : (σ.arrowCongr (Equiv.refl HashOutput)) u' ∘ σ = u' := by
          funext i
          simp [Equiv.arrowCongr_apply, hσ, Equiv.swap_apply_self]
        conv_lhs => rw [← hu]
        rw [storeAll_perm x hx _ σ state]
        congr 3

end PresampleFamilyH

/-! ### One ordinary query with honest reads -/

section OrdinaryH

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData)

theorem finalValue_ordinary (R : List Coordinate) (x : HashInput)
    (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome) (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    ∑' out, Pr{let y ← interp tg initial model (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) budget s}[y = out] *
        finalValue parameter data tg initial R out =
      ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
        ∑' out, Pr{let x ← interp tg initial model (next r.1) (budget - 1) r.2}[x = out] *
          finalValue parameter data tg initial R out := by
  rw [interp_ordinaryHB, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
  simp only [OracleComp.tsum_prEvent_map_mul]
  rfl

theorem flagged_ordinary (x : HashInput) (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    expectedFlagged tg initial model (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) budget s =
      (pays (H := HashInput) tg initial s (.inl (.inr (.inl x))) : ℝ≥0∞) +
        ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
          expectedFlagged tg initial model (next r.1) (budget - 1) r.2 := by
  unfold expectedFlagged
  rw [interp_ordinaryHB, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
  simp only [OracleComp.tsum_prEvent_map_mul, flaggedCount_append, flaggedCount_touch, Nat.cast_add, mul_add,
    ENNReal.tsum_add, ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]

end OrdinaryH

/-! ### Paid programs with the honest signer -/

section GoodOH

variable (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A program whose final value is paid by the potential and the baseline payments. -/
def GoodOH (L : QueryLog SigningSpec) (prog : OracleComp CostSpecH HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → MInv parameter data s Ms → DInv R d →
      CountInvL parameter data Qtot L s budget →
      ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] * finalValue parameter data tg initial R out ≤
        potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * expectedFlagged tg initial model prog budget s

/-- The final value is at most one in the mean. -/
theorem final_le_one (prog : OracleComp CostSpecH HiddenBridge.Outcome) (budget : ℕ) (s : State) (R : List Coordinate) :
    ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] * finalValue parameter data tg initial R out ≤ 1 := by
  calc _ ≤ ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] * 1 := by
        refine ENNReal.tsum_le_tsum fun out => mul_le_mul_right ?_ _
        unfold finalValue
        cases out.1.1 with
        | none => exact zero_le_one
        | some outcome =>
            simp only [Option.elim]
            split_ifs
            · exact le_rfl
            · exact zero_le_one
    _ ≤ 1 := by simp only [mul_one]; exact (OracleComp.tsum_prEvent_le_one _)

theorem goodOH_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L (next v)) :
    GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L
      (liftM (CostSpecH.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  unfold expectedFlagged
  rw [interp_drawH, OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' v, Pr{let x ← (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))}[x = v] *
        (potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * expectedFlagged tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hprep hP hM hD hC) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) (le_of_eq ?_)
        unfold expectedFlagged
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- A new pair: one of its blocks is read fresh, and the others are presampled. -/
theorem new_pair_boundO {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hC : CountInvL parameter data Qtot L s budget) (p : Pair) (c : DigestCall)
    (hkind : ∀ call, tg.kind (pblk parameter data p call) = .none)
    (hp0 : s.cache (pblk parameter data p firstCall) = none) :
    ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
        ∑' out, Pr{let z ← (interp tg initial model (next v) (budget - 1)
          (s.store (pblk parameter data p c) v))}[z = out] * finalValue parameter data tg initial R out ≤
      potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
        b0 * ((if Realized tg initial s then 0 else 1) +
          ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
            expectedFlagged tg initial model (next v) (budget - 1) (s.store (pblk parameter data p c) v)) := by
  set n := signatureLimit - L.length with hn
  set ℓ := (livePairs L P).length with hℓ
  have hfresh : ∀ call, s.cache (pblk parameter data p call) = none := hP.first p hp0
  have hpairE : ∀ F : (DigestCall → HashOutput) → ℝ≥0∞,
      pairE F = ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * ∑ u, F u := by
    intro F
    unfold pairE
    rw [tsum_uniform_eq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  -- the final value only grows when a block of the pair is presampled
  have hFmono : ∀ (out : Run HashInput Coordinate HiddenBridge.Outcome × State) (i : DigestCall)
      (v : HashOutput), out.2.cache (pblk parameter data p i) = none →
      finalValue parameter data tg initial R out ≤
        finalValue parameter data tg initial R (out.1, out.2.store (pblk parameter data p i) v) := by
    intro out i v hc
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
          (s.store (pblk parameter data p c) v))}[z = out] * finalValue parameter data tg initial R out ≤
      pairE (fun u => ∑' out, Pr{let z ← (interp tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u))}[z = out] * finalValue parameter data tg initial R out) := by
    rw [hpairE]
    exact interp_presample_newF tg initial model (pblk parameter data p)
      (pblk_call_injective parameter data p) hkind c next (budget - 1) s hfresh _ hFmono
  have hcount : pairE (fun u => expectedFlagged tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u)) =
      ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
        expectedFlagged tg initial model (next v) (budget - 1) (s.store (pblk parameter data p c) v) := by
    rw [hpairE]
    unfold expectedFlagged
    exact (interp_presample_new_eq tg initial model (pblk parameter data p)
      (pblk_call_injective parameter data p) hkind c next (budget - 1) s hfresh
      fun run => (flaggedCount tg run.2.2.2 : ℝ≥0∞)).symm
  by_cases hcap : 1 ≤ lam Lmax ℓ budget
  · -- more landed pairs than the cap: the cap term pays everything
    calc _ ≤ ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] * 1 :=
          ENNReal.tsum_le_tsum fun v => mul_le_mul_right
            (final_le_one parameter data tg initial model (next v) (budget - 1) _ R) _
      _ ≤ 1 := by simp only [mul_one]; exact OracleComp.tsum_prEvent_le_one _
      _ ≤ lam Lmax ℓ budget := hcap
      _ ≤ _ := le_trans le_add_self le_self_add
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  have hrate : MsgLive L p.1 → Rate parameter data w s p.1 := fun hlive =>
    rate_of_fair hfair s p.1 (by have := hC p.1 hlive; omega) (le_trans (landedCount_le hP L hlive) hlen)
  have hC2 : ∀ a, CountInvL parameter data Qtot L (withPair parameter data s p a) (budget - 1) := by
    intro a m hm
    have h1 := count_withPair (parameter := parameter) (data := data) m s p a
    have h2 := hC m hm
    omega
  have hone : ∀ u, ∑' out, Pr{let x ← (interp tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u))}[x = out] * finalValue parameter data tg initial R out ≤
      potO parameter data w b0 Fail tg initial Lmax (withPair parameter data s p u)
          (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) +
        b0 * expectedFlagged tg initial model (next (u c)) (budget - 1) (withPair parameter data s p u) := fun u =>
    h (u c) (budget - 1) _ _ _ d R
      (fun x v hx => (extends_withPair hP hp0 u).1 x v (hprep x v hx)) (pinv_withPair hP hp0 u)
      (minv_withPair hM p u) hD (hC2 u)
  -- the cap term keeps its mean
  have hlam : pairE (fun u => lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1)) ≤
      lam Lmax ℓ budget := by
    by_cases hlive : MsgLive L p.1
    · have hl : ∀ u : DigestCall → HashOutput,
          lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1) =
          if Landed parameter (blockIndex (u firstCall)) then lam Lmax (ℓ + 1) (budget - 1)
          else lam Lmax ℓ (budget - 1) := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, ite_eq_left (by simpa using hlive), List.length_cons]
          rfl
        · rfl
      simp only [hl]
      have := lam_newPair parameter Lmax ℓ (budget - 1)
      rw [Nat.sub_add_cancel hb] at this
      exact le_of_eq this
    · have hl : ∀ u : DigestCall → HashOutput,
          lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1) =
            lam Lmax ℓ (budget - 1) := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, ite_eq_right (by simpa using hlive)]
          rfl
        · rfl
      simp only [hl, pairE_const]
      exact lam_mono le_rfl (Nat.sub_le _ _)
  refine le_trans (le_trans hpre (pairE_mono hone)) ?_
  rw [pairE_add, pairE_const_mul, hcount, mul_add, ← add_assoc]
  refine add_le_add ?_ le_rfl
  unfold potO
  rw [pairE_add, add_right_comm]
  refine add_le_add ?_ hlam
  by_cases hr : Realized tg initial s ∨ signatureLimit < L.length
  · refine le_of_eq_of_le (b := 0) ?_ bot_le
    unfold pairE
    refine ENNReal.tsum_eq_zero.2 fun u => ?_
    have hr' : Realized tg initial (withPair parameter data s p u) ∨ signatureLimit < L.length :=
      hr.imp (realized_of_extends tg initial (extends_withPair hP hp0 u)) id
    simp only [ite_eq_left hr', mul_zero]
  · have hreal : ¬Realized tg initial s := fun h' => hr (Or.inl h')
    rw [ite_eq_right hreal, mul_one, ite_eq_right hr]
    have hcore : coreO parameter data w b0 Fail s P Ms L d n budget =
        coreO parameter data w b0 Fail s P Ms L d n (budget - 1 + 1) := by rw [Nat.sub_add_cancel hb]
    rw [hcore]
    refine le_trans ?_ (coreO_newPair w b0 Fail hfair.le_one hP hM hp0 L hrate d n (budget - 1))
    refine pairE_mono fun u => ?_
    split_ifs
    · exact bot_le
    · exact le_rfl

/-- **One ordinary query.** -/
theorem goodOH_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L (next v)) :
    GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L
      (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinaryHB, ite_eq_right hb, OracleComp.tsum_prEvent_pure_mul, finalValue_abort]
    exact bot_le
  rw [finalValue_ordinary tg initial model parameter data R x next budget hb s,
    flagged_ordinary tg initial model x next budget hb s]
  by_cases hnew : ∃ (p : Pair) (call : DigestCall), x = pblk parameter data p call ∧
      s.cache (pblk parameter data p firstCall) = none
  · obtain ⟨p, c, rfl, hp0⟩ := hnew
    have hfresh : ∀ call, s.cache (pblk parameter data p call) = none := hP.first p hp0
    rw [ordinaryStep, hparse p c]
    simp only
    rw [readOutside_fresh _ s (hfresh c), OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
    have hpay : (pays (H := HashInput) tg initial s (.inl (.inr (.inl (pblk parameter data p c)))) : ℝ≥0∞) =
        if Realized tg initial s then 0 else 1 := by
      by_cases hr : Realized tg initial s <;> simp [pays, hdigest p c, hr]
    rw [hpay]
    exact new_pair_boundO parameter data w b0 Fail Qtot Lmax tg initial model hfair hQ L next h budget hb s P Ms d R
      hprep hP hM hD hC p c (hkind p) hp0
  · calc _ ≤ ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
          (potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
            b0 * expectedFlagged tg initial model (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ?_ _
            have hext := ordinaryStep_extends model x s r hr
            have hblocks := same_blocks (parameter := parameter) (data := data) hext
              (ordinaryStep_cache_ne model x s r hr) hnew
            obtain ⟨hP', -⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hP
            have hland : ∀ q, LandedIn parameter data s q → ∀ call,
                r.2.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) :=
              fun q hq call => landed_blocks hext hP hq call
            have hcnt : CountInvL parameter data Qtot L r.2 (budget - 1) := by
              intro m hm
              have h1 : cachedCount parameter data m r.2 ≤ cachedCount parameter data m s + 1 := by
                rw [cachedCount_eq, cachedCount_eq]
                exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
              have h2 := hC m hm
              omega
            refine le_trans (h r.1 (budget - 1) r.2 P Ms d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' (minv_blocks hblocks hM) hD hcnt) (add_le_add ?_ le_rfl)
            exact potO_grow w b0 Fail tg initial hfair.le_one Lmax hext hblocks hland
              (fun q hq => (hP.mem q).1 hq) Ms L d (Nat.sub_le _ _)
          · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
          refine add_le_add (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) ?_
          refine le_add_left (le_of_eq ?_)
          simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **Leaf.** A FORS cover with no decided hit is paid by the potential. -/
theorem goodOH_pure (hw : w ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R hprep hP hM hD hC
  rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
  refine le_trans ?_ le_self_add
  unfold finalValue
  simp only [Option.elim, List.append_nil]
  split_ifs with hcov
  swap
  · exact bot_le
  obtain ⟨⟨hvalid, digest, hdig, -, hunsigned, hcovered⟩, hreal⟩ := hcov
  set q : Pair := (forgery.message, forgery.signature.randomness) with hq
  unfold HiddenBridge.cachedDigest at hdig
  cases h0 : pcache parameter data q.1 s q.2 with
  | none =>
      have h0' : (Completeness.allSome (α := fun _ => HashOutput) fun call : DigestCall =>
          s.cache (messageDigestInput parameter data.root forgery.message forgery.signature.randomness
            call)) = none := h0
      rw [h0'] at hdig; cases hdig
  | some a =>
      have h0' : (Completeness.allSome (α := fun _ => HashOutput) fun call : DigestCall =>
          s.cache (messageDigestInput parameter data.root forgery.message forgery.signature.randomness
            call)) = some a := h0
      rw [h0'] at hdig
      have hdig' : truncateMessageDigest a = digest := by
        simpa using hdig
      subst hdig'
      have hlanded : LandedIn parameter data s q :=
        ⟨a firstCall, first_of_pcache parameter data h0, landed_full parameter _⟩
      have hqP := (hP.mem q).2 hlanded
      have hv : pview parameter data s q = Lifetime.localDigestView (truncateMessageDigest a) := by
        simp only [pview, h0, Option.elim, viewOf]
      unfold potO
      rw [ite_eq_right (by
        rintro (h | h)
        · exact hreal h
        · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
      refine le_trans ?_ le_self_add
      unfold coreO
      refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
      unfold candO
      rw [ite_eq_left (show Unsigned L q from hunsigned)]
      split_ifs
      · exact le_rfl
      · unfold candValueO
        calc (1 : ℝ≥0∞) ≤ witnessFn (pview parameter data s q) d := by
              unfold witnessFn
              rw [hv]
              exact witness_pos_of_covered hD _ hcovered
          _ ≤ _ := base_le_termO hw (witness_props _) s Ms L _ d _ _

/-- Hash computations lifted onto the raw summand are sequences of ordinary queries. -/
theorem goodOH_liftRaw (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) {α : Type}
    (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ a, GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L (next a)) :
    GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L
      (simulateQ (fun q => liftM (CostSpecH.query (.inl (.inr (.inl q)))) :
        QueryImpl HashSpec (OracleComp CostSpecH)) computation >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact goodOH_ordinary parameter data w b0 Fail Qtot Lmax tg initial model hparse hdigest hkind hfair hQ L query _ ih

/-- **One honest signing call** on a message that was never signed before: the charged bounds
through the coupling of the honest signer with the charged one. -/
theorem goodOH_signH (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (m : Message) (L : QueryLog SigningSpec) (hm : MsgLive L m)
    (next : Option Signature → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ r, GoodOH parameter data w b0 Fail Qtot Lmax tg initial model (L ++ [⟨m, r⟩]) (next r)) :
    GoodOH parameter data w b0 Fail Qtot Lmax tg initial model L (signCostSourceH parameter data m >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  have hsignEq := signCostSourceH_eq parameter data m
  set ℓ := (livePairs L P).length with hℓ
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => expectedFlagged tg initial model (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
  have hproj : ∀ o1 : Run HashInput Coordinate (Option Signature) × State,
      canonR o1 = canonR ((o1.1.1, o1.1.2.1, [], []), o1.2) := fun o1 => by
    simp only [hcanonR, canonO_congr (o := o1) (o' := ((o1.1.1, o1.1.2.1, [], []), o1.2)) rfl rfl]
  obtain ⟨B, hB, hsum⟩ := tsum_interp_toHonest tg initial model (signCostSource parameter data m)
    (fun p => canonR ((p.1.1, p.1.2, [], []), p.2)) budget s
  have hpoint : ∀ o1 ∈ support (interp tg initial model (signCostSourceH parameter data m) budget s),
      ∑' out, Pr{let x ← interpThen tg initial model next budget o1}[x = out] * finalValue parameter data tg initial R out ≤
        canonR o1 + lam Lmax ℓ budget + b0 * cont o1 := by
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
        refine le_trans hIH (add_le_add ?_ ?_)
        · unfold potO
          exact add_le_add hpot hlam
        · simp only [hcont, hres, Option.elim, hbud, le_refl]
  have hflag : ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
      cont o1 ≤ expectedFlagged tg initial model (signCostSourceH parameter data m >>= next) budget s := by
    unfold expectedFlagged
    rw [interp_bind, OracleComp.tsum_prEvent_bind_mul]
    refine ENNReal.tsum_le_tsum fun o1 => mul_le_mul_right ?_ _
    cases hres : o1.1.1 with
    | none => simp only [hcont, hres, Option.elim]; exact bot_le
    | some r =>
        simp only [hcont, hres, Option.elim]
        rw [interpThenH_some tg initial model next budget o1 r hres, OracleComp.tsum_prEvent_map_mul]
        unfold expectedFlagged
        refine ENNReal.tsum_le_tsum fun o2 => mul_le_mul_right ?_ _
        simp only [flaggedCount_append, Nat.cast_add]
        exact le_add_self
  have hcanon : ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
      canonR o1 ≤
      (if Realized tg initial s ∨ signatureLimit < L.length then 0
        else coreO parameter data w b0 Fail s P Ms L d (signatureLimit - L.length) budget) := by
    calc _ = ∑' o1, Pr{let x ← (interp tg initial model (simulateQ toHonest (signCostSource parameter data m))
            budget s)}[x = o1] * canonR (((runProj o1).1.1, (runProj o1).1.2, [], []), (runProj o1).2) := by
          rw [hsignEq]
          exact tsum_congr fun o1 => by rw [hproj o1]; rfl
      _ = ∑' o1, Pr{let x ← interp tg initial model (signCostSource parameter data m) B s}[x = o1] *
            canonR (((runProj o1).1.1, (runProj o1).1.2, [], []), (runProj o1).2) := hsum
      _ = ∑' o1, Pr{let x ← interp tg initial model (signCostSource parameter data m) B s}[x = o1] * canonR o1 :=
          tsum_congr fun o1 => by rw [hproj o1]; rfl
      _ ≤ _ := sign_expectO2 tg initial model parameter data w b0 Fail m hparse hkind B budget s P Ms L hm d hM
          (pairInv_of_pinv hP m)
  rw [interp_bind, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
        (canonR o1 + lam Lmax ℓ budget + b0 * cont o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model (signCostSourceH parameter data m) budget s)
        · exact mul_le_mul_right (hpoint o1 ho1) _
        · rw [(prEvent_eq_zero_of_not_mem_support _) ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] * canonR o1 +
          (∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1]) *
            lam Lmax ℓ budget +
          b0 * ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
            cont o1 := by
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ b0, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ ≤ _ := by
        unfold potO
        exact add_le_add (add_le_add hcanon (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)))
          (mul_le_mul_right hflag _)

end GoodOH

section InductionH

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem goodOH_finish (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodOH parameter data wbar b0 Fail Qtot Lmax tg initial model L (finishGameH parameter data L forgery) := by
  unfold finishGameH
  exact goodOH_liftRaw parameter data wbar b0 Fail Qtot Lmax tg initial model hparse hdigest hkind hfair hQ L _ _
    fun v => goodOH_pure parameter data wbar b0 Fail Qtot Lmax tg initial model hfair.le_one L forgery v

/-- **The one-coin potential of the scan signer through any adversary that never repeats a
message**, the signer honest. -/
theorem goodOH_advProgH (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodOH parameter data wbar b0 Fail Qtot Lmax tg initial model L (advProgH parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProgH_pure]
      exact goodOH_finish parameter data wbar b0 Fail Qtot Lmax tg initial model hparse hdigest hkind hfair hQ L forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProgH_draw]
        exact goodOH_draw parameter data wbar b0 Fail Qtot Lmax tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProgH_hash]
        exact goodOH_ordinary parameter data wbar b0 Fail Qtot Lmax tg initial model hparse hdigest hkind hfair hQ L
          bytes _ fun v => ih v L (hnr v)
      · rw [advProgH_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodOH_signH parameter data wbar b0 Fail Qtot Lmax tg initial model hparse hkind hfail hfair.le_one
          message L hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end InductionH

end FORS.Security.ForsPotential
