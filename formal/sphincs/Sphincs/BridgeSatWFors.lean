import Sphincs.BridgeSatWSigner
import Sphincs.BridgeForsGameOnce

/-! The one-coin forest potential of the scan signer weighted by the survival weight. The final value
of a run counts a forest cover with weight `w_end`; a new message/randomizer pair costs the baseline
times the current weight; ordinary queries and signing calls do not raise `w * pot` in expectation,
since the potential only depends on the views of the message-digest blocks, whose reads keep the
weight, and the weight is a supermartingale of the run. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner
  SphincsFors.Security.Domination Sphincs.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Signing a message for the first time, weighted -/

section SignScanW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (m : Message)

/-- The weighted mass of a constant. -/
theorem interp_weight_constW {s : State} {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ) (c : ℝ≥0∞) :
    ∑' out, Pr[= out | interp tg initial model computation budget s] * (weight tg initial out.2 * c) ≤
      weight tg initial s * c := by
  calc _ = (∑' out, Pr[= out | interp tg initial model computation budget s] * weight tg initial out.2) * c := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun out => by ring
    _ ≤ _ := mul_le_mul_left (interp_weight_leW tg initial model computation budget s) _

/-- The base value and the averaged walks of a message are below its group after one fresh slot
(the arithmetic of `sign_term`). -/
theorem walk_avg_le_grpM {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (d : Multiset View)
    (excl : Pair → Prop) :
    X d + (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ∑ start, walk nextRand landing (stOf parameter data m s)
        (poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d))
        (freshAvg Finset.univ (fun v => X (d + {v}) - X d)) 0 digestAttemptLimit start ≤
      grpM parameter data s excl m (fun e => freshAvg Finset.univ fun v => X (e + {v})) d := by
  set gf : View → ℝ≥0∞ := fun v => X (d + {v}) - X d with hgf
  set gp : Randomness → View → ℝ≥0∞ := fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d with hgp
  set c := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hc
  have hcard : c * (Fintype.card Randomness : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  have hUX : ∀ e, X e ≤ freshAvg Finset.univ (fun v => X (e + {v})) := by
    intro e
    calc X e = freshAvg Finset.univ (fun _ : View => X e) := (freshAvg_const _ Finset.univ_nonempty _).symm
      _ ≤ _ := freshAvg_mono _ fun v _ => hX _ _ (Multiset.le_add_right _ _)
  -- the base value joins every walk
  have hbase : X d = c * ∑ start : Randomness, walk nextRand landing (stOf parameter data m s) (fun _ => X d)
      (X d) (X d) digestAttemptLimit start := by
    simp only [walk_const landing_le_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, hcard, one_mul]
  rw [hbase, ← mul_add, ← Finset.sum_add_distrib]
  unfold grpM grp gv
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ => ?_)
  rw [← walk_add]
  refine walk_mono _ (fun ρ => ?_) ?_ ?_ _ start
  · -- a cached landed pair
    refine le_trans ?_ (hUX (d + extOf parameter data s excl m ρ))
    unfold poolValue extOf
    cases h0 : s.cache (blk parameter data m ρ) with
    | none =>
        simp only [Option.elim, add_zero]
        exact hX _ _ (Multiset.le_add_right _ _)
    | some u0 =>
        simp only [Option.elim]
        split_ifs with hl hx
        · simp only [hgp, if_pos hx, add_zero, le_refl]
        · have hv : pview parameter data s (m, ρ) = viewOf u0 := pview_of_cached h0
          simp only [hgp, if_neg hx, hv]
          rw [add_tsub_cancel_of_le (hX _ _ (Multiset.le_add_right _ _))]
        · rw [add_zero]
          exact hX _ _ (Multiset.le_add_right _ _)
        · rw [add_zero]
          exact hX _ _ (Multiset.le_add_right _ _)
  · -- a fresh pair
    have hfr : X d + freshAvg Finset.univ gf = freshAvg Finset.univ (fun v => X (d + {v})) := by
      calc X d + freshAvg Finset.univ gf = freshAvg Finset.univ (fun v => X d + gf v) := by
            rw [freshAvg_add, freshAvg_const _ Finset.univ_nonempty]
        _ = _ := by
            congr 1
            funext v
            exact add_tsub_cancel_of_le (hX _ _ (Multiset.le_add_right _ _))
    rw [hfr]
    split_ifs
    · exact le_rfl
    · calc freshAvg Finset.univ (fun v => X (d + {v}))
          = freshAvg Finset.univ (fun _ : View => freshAvg Finset.univ fun v => X (d + {v})) :=
            (freshAvg_const _ Finset.univ_nonempty _).symm
        _ ≤ _ := freshAvg_mono _ fun v' _ => freshAvg_mono _ fun v _ =>
            hX _ _ (add_le_add (Multiset.le_add_right _ _) le_rfl)
  · rw [add_zero]
    exact hUX d

/-- **One signing call, one term, weighted** (the weighted `sign_term`). Averaged over the uniform
start and the scan, the weighted upper value of a monotone function of the disclosures is at most the
initial weight times the group of the message applied to that function after one fresh slot. -/
theorem upper_expectW (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data m ρ) = .none)
    {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (d : Multiset View)
    (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 *
          (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
            outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out))) ≤
      weight tg initial s *
        grpM parameter data s excl m (fun e => freshAvg Finset.univ fun v => X (e + {v})) d := by
  refine le_trans ?_ (mul_le_mul' le_rfl (walk_avg_le_grpM parameter data m hX s d excl))
  set gf : View → ℝ≥0∞ := fun v => X (d + {v}) - X d with hgf
  set gp : Randomness → View → ℝ≥0∞ := fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d with hgp
  set c := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hc
  have hscan : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 *
          (freshNewWeight parameter data m s gf out + outWeight parameter data m s 0 gp out)) ≤
      weight tg initial s * (c * ∑ start, walk nextRand landing (stOf parameter data m s)
        (poolValue parameter data m s gp) (freshAvg Finset.univ gf) 0 digestAttemptLimit start) := by
    unfold signCostSource
    rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
    have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = c := by
      intro ρ
      rw [probOutput_uniformSample]
    simp only [hpr]
    rw [ENNReal.tsum_mul_left, tsum_fintype]
    refine le_trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ =>
      loop_bound_combSW tg initial model parameter data m hparse hkind s gf gp digestAttemptLimit
        (by unfold digestAttemptLimit; norm_num) budget s start (fun _ => Or.inl rfl) (fun _ _ => rfl)))
      (le_of_eq ?_)
    rw [← Finset.mul_sum, mul_left_comm]
  rw [mul_add]
  refine le_trans (le_of_eq ?_) (add_le_add
    (interp_weight_constW tg initial model (s := s) (signCostSource parameter data m) budget (X d)) hscan)
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun out => by ring

/-- The fresh pair completed by a signing call weighs at most its fresh average, weighted. -/
theorem fresh_expectW (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data m ρ) = .none) (s : State) (gf : View → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 * freshNewWeight parameter data m s gf out) ≤
      weight tg initial s * freshAvg Finset.univ gf := by
  unfold signCostSource
  rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
  have hstart : ∀ start : Randomness, ∑' out, Pr[= out | interp tg initial model
      (signCostSourceLoop parameter data m digestAttemptLimit start) budget s] *
      (weight tg initial out.2 * freshNewWeight parameter data m s gf out) ≤
      weight tg initial s * freshAvg Finset.univ gf := by
    intro start
    have h := loop_bound_combSW tg initial model parameter data m hparse hkind s gf (fun _ _ => 0)
      digestAttemptLimit (by unfold digestAttemptLimit; norm_num) budget s start (fun _ => Or.inl rfl)
      (fun _ _ => rfl)
    refine le_trans (ENNReal.tsum_le_tsum fun out => mul_le_mul' le_rfl (mul_le_mul' le_rfl le_self_add))
      (le_trans h (mul_le_mul' le_rfl ?_))
    refine walk_le landing_le_one _ (fun ρ => ?_) le_rfl bot_le _ start
    unfold poolValue
    cases s.cache (blk parameter data m ρ) <;> simp
  calc _ ≤ ∑' start, Pr[= start | ($ᵗ Randomness : ProbComp Randomness)] *
        (weight tg initial s * freshAvg Finset.univ gf) :=
        ENNReal.tsum_le_tsum fun start => mul_le_mul' le_rfl (hstart start)
    _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SignScanW

section SignExpectW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  {parameter : PublicParameter} {data : PublicData} {w : ℝ≥0∞} {m : Message} {s : State} {n : ℕ}
  {d : Multiset View} {f : Multiset View → ℝ≥0∞}

/-- **A dominated term, weighted.** -/
theorem term_expectW (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data m ρ) = .none)
    (hf : MonoFin f) (rest : List Message) (excl : Pair → Prop) (budget k : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 *
          creations Finset.univ landing (fun J => upperO parameter data w m s n d f rest excl out J) k []) ≤
      weight tg initial s * creations Finset.univ landing (fun J => grpAll parameter data s excl (m :: rest)
        (virtualOnce Finset.univ w f (n + 1) J) d) k [] := by
  simp only [← mul_assoc]
  rw [creations_tsum, ← creations_const_mul]
  refine creations_mono (fun J => ?_) k []
  simp only [mul_assoc]
  have hX : Monotone' (restBase parameter data w s n f rest excl J) :=
    grpAll_mono s excl (virtualOnce_mono hf.1 n J) rest
  refine le_trans (upper_expectW tg initial model parameter data m hparse hkind hX s d excl budget)
    (mul_le_mul' le_rfl (le_of_eq ?_))
  simp only [grpAll]
  refine grp_congr _ _ (fun e => ?_) d
  unfold restBase
  symm
  rw [grpAll_congr s excl (virtualOnce_succ_nil J) rest e, grpAll_freshAvg]
  congr 1
  funext v
  exact grpAll_shift s excl _ {v} rest e

end SignExpectW

section SignPointW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) (m : Message)

/-- **The signing step in expectation, weighted**, for a message signed for the first time. -/
theorem sign_expectW (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (hm : MsgLive L m) (d : Multiset View) (hM : MInv parameter data s Ms) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 * (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out)) ≤
      weight tg initial s * (if Realized tg initial s ∨ signatureLimit < L.length then 0
        else coreO parameter data w b0 Fail s P Ms L d (signatureLimit - L.length) budget) := by
  by_cases hcase : Realized tg initial s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬Realized tg initial s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  rw [if_neg (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ, model.parse (blk parameter data m ρ) = none := fun ρ => hparse (m, ρ)
  have hkind' : ∀ ρ, tg.kind (blk parameter data m ρ) = .none := fun ρ => hkind (m, ρ)
  have hconst := fun c => interp_weight_constW tg initial model (s := s)
    (signCostSource parameter data m) budget c
  have hFN : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) ≤
      weight tg initial s * failMass Fail :=
    fresh_expectW tg initial model parameter data m hparse' hkind' s _ budget
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data w m s n d (witnessFn (pview parameter data s q))
          (restMsgs m L Ms) (· = q) out J) budget []) else 0)) ≤
      weight tg initial s * candO parameter data w Fail s Ms L d (n + 1) budget q := by
    intro q _
    unfold candO
    split_ifs
    · exact hconst 1
    · unfold candValueO
      rw [termO_eq_cons hm hM]
      exact term_expectW tg initial model hparse' hkind' (witness_props _) _ _ budget budget
    · exact hconst 0
  have hH : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * creations Finset.univ landing (fun J => upperO parameter data w m s n d (excess b0)
        (restMsgs m L Ms) (fun _ => False) out J) budget []) ≤
      weight tg initial s * hValueO parameter data w b0 s Ms L d (n + 1) budget := by
    unfold hValueO
    rw [termO_eq_cons hm hM]
    exact term_expectW tg initial model hparse' hkind' (excess_props b0) _ _ budget budget
  have hLS : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
        else creations Finset.univ landing (fun J => upperO parameter data w m s n d
          (witnessFn (pview parameter data s q)) (restMsgs m L Ms) (· = q) out J) budget [])
        else 0).sum) ≤
      weight tg initial s * (P.map (candO parameter data w Fail s Ms L d (n + 1) budget)).sum := by
    simp only [← mul_assoc]
    rw [tsum_list_sum, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun q hq => by simpa only [mul_assoc] using hT q hq
  have hHC : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
        (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
          failMass Fail))) ≤
      weight tg initial s * ((budget : ℝ≥0∞) * (hValueO parameter data w b0 s Ms L d (n + 1) budget +
        failMass Fail)) := by
    have hpt : ∀ out : Run HashInput Coordinate (Option Signature) × State,
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
              failMass Fail))) =
        (budget : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [])) +
        (budget : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * failMass Fail)) := by
      intro out
      ring
    simp only [hpt, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    calc _ ≤ (budget : ℝ≥0∞) * (weight tg initial s * hValueO parameter data w b0 s Ms L d (n + 1) budget) +
          (budget : ℝ≥0∞) * (weight tg initial s * failMass Fail) :=
          add_le_add (mul_le_mul' le_rfl hH) (mul_le_mul' le_rfl (hconst _))
      _ = _ := by ring
  have hsplit : ∀ out : Run HashInput Coordinate (Option Signature) × State,
      Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 * canonO parameter data w b0 Fail m s P Ms L d n budget out) =
      Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
            else creations Finset.univ landing (fun J => upperO parameter data w m s n d
              (witnessFn (pview parameter data s q)) (restMsgs m L Ms) (· = q) out J) budget [])
            else 0).sum) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
              failMass Fail))) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * ((n : ℝ≥0∞) * failMass Fail)) := by
    intro out
    unfold canonO
    ring
  simp only [hsplit, ENNReal.tsum_add]
  calc _ ≤ weight tg initial s * failMass Fail +
        weight tg initial s * (P.map (candO parameter data w Fail s Ms L d (n + 1) budget)).sum +
        weight tg initial s * ((budget : ℝ≥0∞) * (hValueO parameter data w b0 s Ms L d (n + 1) budget +
          failMass Fail)) + weight tg initial s * ((n : ℝ≥0∞) * failMass Fail) :=
        add_le_add (add_le_add (add_le_add hFN hLS) hHC) (hconst _)
    _ = _ := by
        unfold coreO
        push_cast
        ring

end SignPointW

/-! ### Weighted paid programs -/

section GoodW

variable (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A program whose final value, weighted by the final survival weight, is paid by the weighted
potential and the weighted baseline payments. -/
def GoodW (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → MInv parameter data s Ms → DInv R d →
      CountInv parameter data Qtot s budget →
      ∑' out, Pr[= out | interp tg initial model prog budget s] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
        weight tg initial s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wflag tg initial model prog budget s

/-- The weighted final value is at most the initial weight in the mean. -/
theorem finalW_le (prog : OracleComp CostSpec HiddenBridge.Outcome) (budget : ℕ) (s : State) (R : List Coordinate) :
    ∑' out, Pr[= out | interp tg initial model prog budget s] *
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

theorem goodW_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (next v)) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  have hw : wflag tg initial model (liftM (CostSpec.query (.inl (.inl draw))) >>= next) budget s =
      ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        wflag tg initial model (next v) budget s := by
    rw [wflag_query_bind]
    refine (if_pos (Nat.zero_le budget)).trans ?_
    change ∑' r, Pr[= r | (fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)] *
      (0 + wflag tg initial model (next r.1) (budget - 0) r.2) = _
    rw [tsum_probOutput_map_mul]
    simp only [zero_add, Nat.sub_zero]
  rw [hw, interp_draw, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (weight tg initial s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wflag tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hprep hP hM hD hC) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) (le_of_eq ?_)
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

theorem finalValueW_ordinary (R : List Coordinate) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome) (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    ∑' out, Pr[= out | interp tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s] *
        (weight tg initial out.2 * finalValue parameter data tg initial R out) =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ∑' out, Pr[= out | interp tg initial model (next r.1) (budget - 1) r.2] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) := by
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  rfl

theorem wflag_ordinary (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    wflag tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (wpays tg initial s (.inl (.inr (.inl x))) + wflag tg initial model (next r.1) (budget - 1) r.2) := by
  rw [wflag_query_bind, costStep_ordinary]
  exact if_pos hb

/-- The potential part of a new pair, when the coin pays the rate of its message. -/
theorem new_pair_core (hw : w ≤ 1) (L : QueryLog SigningSpec)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) (p : Pair)
    (hp0 : s.cache (pblk parameter data p) = none)
    (hrate : MsgLive L p.1 → Rate parameter data w s p.1) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potO parameter data w b0 Fail tg initial Lmax (withPair parameter data s p u) (addPair parameter P p u)
          (addMsg Ms p.1) L d (budget - 1) ≤
      potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
        b0 * (if Realized tg initial s then 0 else 1) := by
  set n := signatureLimit - L.length with hn
  set ℓ := (livePairs L P).length with hℓ
  -- the cap term keeps its mean
  have hlam : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
      lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1) ≤ lam Lmax ℓ budget := by
    by_cases hlive : MsgLive L p.1
    · have hl : ∀ u, lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1) =
          if Landed parameter (blockIndex u) then lam Lmax (ℓ + 1) (budget - 1)
          else lam Lmax ℓ (budget - 1) := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, if_pos (by simpa using hlive), List.length_cons]
          rfl
        · rfl
      simp only [hl]
      have := lam_newPair parameter Lmax ℓ (budget - 1)
      rw [Nat.sub_add_cancel hb] at this
      exact le_of_eq this
    · have hl : ∀ u, lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1) = lam Lmax ℓ (budget - 1) := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, if_neg (by simpa using hlive)]
          rfl
        · rfl
      simp only [hl, ENNReal.tsum_mul_right]
      exact le_trans (mul_le_of_le_one_left' tsum_probOutput_le_one) (lam_mono le_rfl (Nat.sub_le _ _))
  unfold potO
  simp only [mul_add, ENNReal.tsum_add]
  rw [add_right_comm]
  refine add_le_add ?_ hlam
  by_cases hr : Realized tg initial s ∨ signatureLimit < L.length
  · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun u => ?_) bot_le
    have hr' : Realized tg initial (withPair parameter data s p u) ∨ signatureLimit < L.length :=
      hr.imp (realized_of_extends tg initial (extends_store s (pblk parameter data p) u hp0)) id
    rw [if_pos hr', mul_zero]
  · have hreal : ¬Realized tg initial s := fun h' => hr (Or.inl h')
    rw [if_neg hreal, mul_one, if_neg hr]
    have hcore : coreO parameter data w b0 Fail s P Ms L d n budget =
        coreO parameter data w b0 Fail s P Ms L d n (budget - 1 + 1) := by rw [Nat.sub_add_cancel hb]
    rw [hcore]
    refine le_trans ?_ (coreO_newPair w b0 Fail hw hP hM hp0 L hrate d n (budget - 1))
    unfold pairE
    refine ENNReal.tsum_le_tsum fun u => mul_le_mul_right ?_ _
    split_ifs
    · exact bot_le
    · exact le_rfl

/-- A new pair: its block is read fresh, weighted. -/
theorem new_pair_boundW (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p) = none) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
          (s.store (pblk parameter data p) u)] * (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
        b0 * (weight tg initial s +
          ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
            wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p) u)) := by
  have hws : ∀ u, weight tg initial (s.store (pblk parameter data p) u) = weight tg initial s := fun u =>
    weight_store_untargetedW tg initial s _ u (hkind p)
  set ℓ := (livePairs L P).length with hℓ
  by_cases hcap : 1 ≤ lam Lmax ℓ budget
  · -- more landed pairs than the cap: the cap term pays everything
    calc _ ≤ ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * weight tg initial s :=
          ENNReal.tsum_le_tsum fun u => mul_le_mul_right
            ((finalW_le parameter data tg initial model (next u) (budget - 1) _ R).trans (hws u).le) _
      _ ≤ weight tg initial s := by
          rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
      _ ≤ weight tg initial s * lam Lmax ℓ budget := le_mul_of_one_le_right' hcap
      _ ≤ _ := by
          unfold potO
          exact le_trans (mul_le_mul' le_rfl le_add_self) le_self_add
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  have hrate : MsgLive L p.1 → Rate parameter data w s p.1 := fun hlive =>
    rate_of_fair hfair s p.1 (by have := hC p.1; omega) (le_trans (landedCount_le hP L hlive) hlen)
  have hC2 : ∀ a, CountInv parameter data Qtot (withPair parameter data s p a) (budget - 1) := by
    intro a m
    have h1 := count_withPair (parameter := parameter) (data := data) m s p a
    have h2 := hC m
    omega
  have hone : ∀ u, ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
        (s.store (pblk parameter data p) u)] * (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potO parameter data w b0 Fail tg initial Lmax (withPair parameter data s p u)
          (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) +
        b0 * wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p) u) := fun u => by
    have := h u (budget - 1) _ _ _ d R (prepared_store initial s hprep _ u hp0) (pinv_withPair hP hp0 u)
      (minv_withPair hM p u) hD (hC2 u)
    rwa [hws u] at this
  refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hone u) _) ?_
  simp only [mul_add, ENNReal.tsum_add]
  rw [← add_assoc]
  refine add_le_add ?_ (le_of_eq ?_)
  · calc _ = weight tg initial s * ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          potO parameter data w b0 Fail tg initial Lmax (withPair parameter data s p u)
            (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) := by
          simp only [mul_left_comm _ (weight tg initial s), ENNReal.tsum_mul_left]
      _ ≤ weight tg initial s * (potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
            b0 * (if Realized tg initial s then 0 else 1)) :=
          mul_le_mul_right (new_pair_core parameter data w b0 Fail Lmax tg initial hfair.le_one L budget hb s P Ms d
            hP hM p hp0 hrate) _
      _ ≤ _ := by
          rw [mul_add]
          refine add_le_add le_rfl ?_
          rw [mul_left_comm]
          refine mul_le_mul_right ?_ _
          split_ifs <;> simp
  · simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **One ordinary query, weighted.** -/
theorem goodW_ordinary (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (next v)) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L
      (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinary, if_neg hb, tsum_probOutput_pure_mul, finalValue_abort, mul_zero]
    exact bot_le
  rw [finalValueW_ordinary parameter data tg initial model R x next budget hb s,
    wflag_ordinary tg initial model x next budget hb s]
  by_cases hnew : ∃ p, x = pblk parameter data p ∧ s.cache (pblk parameter data p) = none
  · obtain ⟨p, rfl, hp0⟩ := hnew
    rw [ordinaryStep, hparse p]
    simp only
    rw [readOutside_fresh _ s hp0, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
    have hpay : wpays tg initial s (.inl (.inr (.inl (pblk parameter data p)))) = weight tg initial s := by
      change (if tg.digest (pblk parameter data p) then weight tg initial s else 0) = _
      rw [if_pos (hdigest p)]
    rw [hpay]
    have hsum : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (weight tg initial s + wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p) u)) =
        weight tg initial s + ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p) u) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero,
        one_mul]
    rw [hsum]
    exact new_pair_boundW parameter data w b0 Fail Qtot Lmax tg initial model hkind hfair hQ L next h budget hb
      s P Ms d R hprep hP hM hD hC p hp0
  · have hmean : ∑' r, Pr[= r | ordinaryStep model x s.known s] * weight tg initial r.2 ≤ weight tg initial s := by
      have := meanWeight_costStep_leW tg initial model (.inl (.inr (.inl x))) s
      rwa [costStep_ordinary] at this
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (weight tg initial r.2 * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
            b0 * wflag tg initial model (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ?_ _
            have hext := ordinaryStep_extends model x s r hr
            have hblocks := same_blocks (parameter := parameter) (data := data) hext
              (ordinaryStep_cache_ne model x s r hr) hnew
            obtain ⟨hP', -⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hP
            have hcnt : CountInv parameter data Qtot r.2 (budget - 1) := by
              intro m
              have h1 : cachedCount parameter data m r.2 ≤ cachedCount parameter data m s + 1 := by
                rw [cachedCount_eq, cachedCount_eq]
                exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
              have h2 := hC m
              omega
            refine le_trans (h r.1 (budget - 1) r.2 P Ms d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' (minv_blocks hblocks hM) hD hcnt) (add_le_add ?_ le_rfl)
            exact mul_le_mul_right
              (potO_grow w b0 Fail tg initial hfair.le_one Lmax hext hblocks P Ms L d (Nat.sub_le _ _)) _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add]
          refine add_le_add ?_ ?_
          · calc _ = (∑' r, Pr[= r | ordinaryStep model x s.known s] * weight tg initial r.2) *
                  potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget := by
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun r => by ring
              _ ≤ _ := mul_le_mul_left hmean _
          · refine le_add_left (le_of_eq ?_)
            simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **Leaf, weighted.** -/
theorem goodW_pure (hw : w ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R hprep hP hM hD hC
  have h := goodO_pure parameter data w b0 Fail Qtot Lmax tg initial model hw L forgery verified budget s P Ms d R
    hprep hP hM hD hC
  have hflag : expectedFlagged tg initial model (pure (forgery, L, verified) : OracleComp CostSpec _) budget s = 0 := by
    unfold expectedFlagged
    rw [interp_pure, tsum_probOutput_pure_mul]
    simp [flaggedCount]
  rw [hflag, mul_zero, add_zero, interp_pure, tsum_probOutput_pure_mul] at h
  rw [wflag_pure, mul_zero, add_zero, interp_pure, tsum_probOutput_pure_mul]
  exact mul_le_mul_right h _

/-- Lifted hash computations are sequences of ordinary queries. -/
theorem goodW_liftHash (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) {α : Type}
    (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (next a)) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L
      ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodW_ordinary parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hdigest hfair hQ L
        query _ ih

/-- **One signing call, weighted**, on a message that was never signed before. -/
theorem goodW_sign (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (m : Message) (L : QueryLog SigningSpec) (hm : MsgLive L m)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodW parameter data w b0 Fail Qtot Lmax tg initial model (L ++ [⟨m, r⟩]) (next r)) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (signCostSource parameter data m >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  set sign := signCostSource parameter data m with hsign
  set ℓ := (livePairs L P).length with hℓ
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => wflag tg initial model (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
  have hpoint : ∀ o1 ∈ support (interp tg initial model sign budget s),
      ∑' out, Pr[= out | interpThen tg initial model next budget o1] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
        weight tg initial o1.2 * (canonR o1 + lam Lmax ℓ budget) + b0 * cont o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none =>
        rw [interpThen_none tg initial model next budget o1 hres, tsum_probOutput_pure_mul]
        have h0 : finalValue parameter data tg initial R ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) = 0 := rfl
        rw [h0, mul_zero]
        exact bot_le
    | some r =>
        rw [interpThen_some tg initial model next budget o1 r hres, tsum_probOutput_map_mul]
        obtain ⟨hprep', hP', hM', hD', hC', _⟩ := sign_paramsS tg initial model Fail Qtot hparse (hfail m)
          budget s P Ms d R hprep hP hM hD hC o1 ho1 r hres
        have hIH := h r (budget - traceCost o1.1.2.2.1) o1.2 _ _ _ _ hprep' hP' hM' hD' hC'
        have hpot := sign_pointO tg initial model parameter data w b0 Fail Qtot m hparse (hfail m) hw
          budget s P Ms L d R hprep hP hM hD hC o1 ho1 r hres (Nat.sub_le budget (traceCost o1.1.2.2.1))
        have hlam : lam Lmax (livePairs (L ++ [⟨m, r⟩]) (newPairs parameter data m s o1.2 ++ P)).length
            (budget - traceCost o1.1.2.2.1) ≤ lam Lmax ℓ budget := by
          refine lam_mono ?_ (Nat.sub_le _ _)
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
        · simp only [hcont, hres, Option.elim, le_refl]
  have hflag : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 ≤
      wflag tg initial model (sign >>= next) budget s := by
    rw [wflag_bind]
    exact le_add_self
  rw [interp_bind, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
        (weight tg initial o1.2 * (canonR o1 + lam Lmax ℓ budget) + b0 * cont o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model sign budget s)
        · exact mul_le_mul_right (hpoint o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * (weight tg initial o1.2 * canonR o1) +
          ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * (weight tg initial o1.2 * lam Lmax ℓ budget) +
          b0 * ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 := by
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ b0, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        unfold potO
        rw [mul_add]
        exact add_le_add (add_le_add
          (sign_expectW tg initial model parameter data w b0 Fail m hparse hkind budget s P Ms L hm d hM)
          (interp_weight_constW tg initial model (s := s) sign budget _)) (mul_le_mul_right hflag _)

theorem goodW_finish (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (finishGame parameter data L forgery) := by
  unfold finishGame
  exact goodW_liftHash parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hdigest hfair hQ L _ _
    fun v => goodW_pure parameter data w b0 Fail Qtot Lmax tg initial model hfair.le_one L forgery v

/-- **The weighted one-coin potential of the scan signer through any adversary that never repeats a
message.** -/
theorem goodW_advProg (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodW parameter data w b0 Fail Qtot Lmax tg initial model L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      exact goodW_finish parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hdigest hfair hQ L
        forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodW_draw parameter data w b0 Fail Qtot Lmax tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodW_ordinary parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hdigest hfair hQ
          L bytes _ fun v => ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodW_sign parameter data w b0 Fail Qtot Lmax tg initial model hparse hkind hfail hfair.le_one
          message L hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end GoodW

end Sphincs.Security.ForsPotential
