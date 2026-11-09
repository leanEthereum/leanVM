module

public import FORS.LargeBudget.WeightedScan
public import FORS.CoverPotential.Game
public import FORS.Reduction.NoRepeat
public import FORS.CoverPotential.OneCoin

@[expose] public section

/-! The one-coin FORS potential of the scan signer weighted by the survival weight. The final value
of a run counts a FORS cover with weight `w_end`; a new message/randomizer pair costs the baseline
times the current weight; ordinary queries and signing calls do not raise `w * pot` in expectation,
since the potential only depends on the views of the message-digest blocks, whose reads keep the
weight, and the weight is a supermartingale of the run. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Signing a message for the first time, weighted -/

section SignScanW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (m : Message)

/-- The weighted mass of a constant. -/
theorem interp_weight_constW {s : State} {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ) (c : ℝ≥0∞) :
    ∑' out, Pr{let x ← interp tg initial model computation budget s}[x = out] * (weight tg initial out.2 * c) ≤
      weight tg initial s * c := by
  calc _ = (∑' out, Pr{let x ← interp tg initial model computation budget s}[x = out] * weight tg initial out.2) * c := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun out => by ring
    _ ≤ _ := mul_le_mul_left (interp_weight_leW tg initial model computation budget s) _

/-- The base value and the averaged walks of a message are below its group after one fresh slot
(the arithmetic of `sign_term`). -/
theorem walk_avg_le_grpM {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (d : Multiset View)
    (excl : Pair → Prop) :
    X d + (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ∑ start, walk (nextRand (data.steps m)) landing (stOf parameter data m s)
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
  have hbase : X d = c * ∑ start : Randomness, walk (nextRand (data.steps m)) landing (stOf parameter data m s) (fun _ => X d)
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
    cases h0 : pcache parameter data m s ρ with
    | none =>
        simp only [Option.elim, add_zero]
        exact hX _ _ (Multiset.le_add_right _ _)
    | some u =>
        simp only [Option.elim]
        split_ifs with hl hx
        · simp only [hgp, ite_eq_left hx, add_zero, le_refl]
        · have hv : pview parameter data s (m, ρ) = viewOf u := pview_of_pcache (q := (m, ρ)) h0
          simp only [hgp, ite_eq_right hx, hv]
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
theorem upper_expectW (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none)
    {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State)
    (hinv : PairInv parameter data m s) (d : Multiset View)
    (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        (weight tg initial out.2 *
          (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
            outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out))) ≤
      weight tg initial s *
        grpM parameter data s excl m (fun e => freshAvg Finset.univ fun v => X (e + {v})) d := by
  refine le_trans ?_ (mul_le_mul' le_rfl (walk_avg_le_grpM parameter data m hX s d excl))
  set gf : View → ℝ≥0∞ := fun v => X (d + {v}) - X d with hgf
  set gp : Randomness → View → ℝ≥0∞ := fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d with hgp
  set c := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hc
  have hscan : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        (weight tg initial out.2 *
          (freshNewWeight parameter data m s gf out + outWeight parameter data m s 0 gp out)) ≤
      weight tg initial s * (c * ∑ start, walk (nextRand (data.steps m)) landing (stOf parameter data m s)
        (poolValue parameter data m s gp) (freshAvg Finset.univ gf) 0 digestAttemptLimit start) := by
    unfold signCostSource
    rw [interp_liftProb_bind, OracleComp.tsum_prEvent_bind_mul]
    have hpr : ∀ ρ, Pr{let x ← ($ᵗ Randomness : ProbComp Randomness)}[x = ρ] = c := by
      intro ρ
      rw [SampleableType.prEvent_uniformSample_eq_singleton]
    simp only [hpr]
    rw [ENNReal.tsum_mul_left, tsum_fintype]
    refine le_trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ =>
      loop_bound_combSW tg initial model parameter data m hparse hkind s gf gp digestAttemptLimit
        (by unfold digestAttemptLimit; norm_num) budget s start (fun _ => Or.inl rfl) hinv
          (fun _ _ _ => rfl)))
      (le_of_eq ?_)
    rw [← Finset.mul_sum, mul_left_comm]
  rw [mul_add]
  refine le_trans (le_of_eq ?_) (add_le_add
    (interp_weight_constW tg initial model (s := s) (signCostSource parameter data m) budget (X d)) hscan)
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun out => by ring

/-- The fresh pair completed by a signing call weighs at most its fresh average, weighted. -/
theorem fresh_expectW (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none) (s : State)
    (hinv : PairInv parameter data m s) (gf : View → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        (weight tg initial out.2 * freshNewWeight parameter data m s gf out) ≤
      weight tg initial s * freshAvg Finset.univ gf := by
  unfold signCostSource
  rw [interp_liftProb_bind, OracleComp.tsum_prEvent_bind_mul]
  have hstart : ∀ start : Randomness, ∑' out, Pr{let x ← (interp tg initial model
      (signCostSourceLoop parameter data m (data.step m) digestAttemptLimit start) budget s)}[x = out] *
      (weight tg initial out.2 * freshNewWeight parameter data m s gf out) ≤
      weight tg initial s * freshAvg Finset.univ gf := by
    intro start
    have h := loop_bound_combSW tg initial model parameter data m hparse hkind s gf (fun _ _ => 0)
      digestAttemptLimit (by unfold digestAttemptLimit; norm_num) budget s start (fun _ => Or.inl rfl)
      hinv (fun _ _ _ => rfl)
    refine le_trans (ENNReal.tsum_le_tsum fun out => mul_le_mul' le_rfl (mul_le_mul' le_rfl le_self_add))
      (le_trans h (mul_le_mul' le_rfl ?_))
    refine walk_le landing_le_one _ (fun ρ => ?_) le_rfl bot_le _ start
    unfold poolValue
    cases pcache parameter data m s ρ <;> simp
  calc _ ≤ ∑' start, Pr{let x ← ($ᵗ Randomness : ProbComp Randomness)}[x = start] *
        (weight tg initial s * freshAvg Finset.univ gf) :=
        ENNReal.tsum_le_tsum fun start => mul_le_mul' le_rfl (hstart start)
    _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

end SignScanW

section SignExpectW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  {parameter : PublicParameter} {data : PublicData} {w : ℝ≥0∞} {m : Message} {s : State} {n : ℕ}
  {d : Multiset View} {f : Multiset View → ℝ≥0∞}

/-- **A dominated term, weighted.** -/
theorem term_expectW (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none)
    (hinv : PairInv parameter data m s)
    (hf : MonoFin f) (rest : List Message) (excl : Pair → Prop) (budget k : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
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
  refine le_trans (upper_expectW tg initial model parameter data m hparse hkind hX s hinv d excl budget)
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

/-- `sign_expectW` with the signer's interpreter budget `bi` apart from the potential's budget `budget`. -/
theorem sign_expectW2 (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (bi budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (hm : MsgLive L m) (d : Multiset View)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
        (weight tg initial out.2 * (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out)) ≤
      weight tg initial s * (if Realized tg initial s ∨ signatureLimit < L.length then 0
        else coreO parameter data w b0 Fail s P Ms L d (signatureLimit - L.length) budget) := by
  by_cases hcase : Realized tg initial s ∨ signatureLimit ≤ L.length
  · simp only [ite_eq_left hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [ite_eq_right hcase]
  have hcase' : ¬Realized tg initial s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  rw [ite_eq_right (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none :=
    fun ρ call => hparse (m, ρ) call
  have hkind' : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none :=
    fun ρ call => hkind (m, ρ) call
  -- the pair invariant of the state, from `PInv.first` and `PInv.all` at `(m, ρ)`
  have hinv : PairInv parameter data m s := fun ρ =>
    ⟨fun h call => hP.first (m, ρ) h call,
      fun u0 h hl call => Option.ne_none_iff_isSome.1 (hP.all (m, ρ) ⟨u0, h, hl⟩ call)⟩
  have hconst := fun c => interp_weight_constW tg initial model (s := s)
    (signCostSource parameter data m) bi c
  have hFN : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) ≤
      weight tg initial s * failMass Fail :=
    fresh_expectW tg initial model parameter data m hparse' hkind' s hinv _ bi
  have hT : ∀ q ∈ P, ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
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
      exact term_expectW tg initial model hparse' hkind' hinv (witness_props _) _ _ bi budget
    · exact hconst 0
  have hH : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * creations Finset.univ landing (fun J => upperO parameter data w m s n d (excess b0)
        (restMsgs m L Ms) (fun _ => False) out J) budget []) ≤
      weight tg initial s * hValueO parameter data w b0 s Ms L d (n + 1) budget := by
    unfold hValueO
    rw [termO_eq_cons hm hM]
    exact term_expectW tg initial model hparse' hkind' hinv (excess_props b0) _ _ bi budget
  have hLS : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
        else creations Finset.univ landing (fun J => upperO parameter data w m s n d
          (witnessFn (pview parameter data s q)) (restMsgs m L Ms) (· = q) out J) budget [])
        else 0).sum) ≤
      weight tg initial s * (P.map (candO parameter data w Fail s Ms L d (n + 1) budget)).sum := by
    simp only [← mul_assoc]
    rw [tsum_list_sum, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun q hq => by simpa only [mul_assoc] using hT q hq
  have hHC : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
        (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
          failMass Fail))) ≤
      weight tg initial s * ((budget : ℝ≥0∞) * (hValueO parameter data w b0 s Ms L d (n + 1) budget +
        failMass Fail)) := by
    have hpt : ∀ out : Run HashInput Coordinate (Option Signature) × State,
        Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
              failMass Fail))) =
        (budget : ℝ≥0∞) * (Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [])) +
        (budget : ℝ≥0∞) * (Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * failMass Fail)) := by
      intro out
      ring
    simp only [hpt, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    calc _ ≤ (budget : ℝ≥0∞) * (weight tg initial s * hValueO parameter data w b0 s Ms L d (n + 1) budget) +
          (budget : ℝ≥0∞) * (weight tg initial s * failMass Fail) :=
          add_le_add (mul_le_mul' le_rfl hH) (mul_le_mul' le_rfl (hconst _))
      _ = _ := by ring
  have hsplit : ∀ out : Run HashInput Coordinate (Option Signature) × State,
      Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
        (weight tg initial out.2 * canonO parameter data w b0 Fail m s P Ms L d n budget out) =
      Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) +
        Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
            else creations Finset.univ landing (fun J => upperO parameter data w m s n d
              (witnessFn (pview parameter data s q)) (restMsgs m L Ms) (· = q) out J) budget [])
            else 0).sum) +
        Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
              failMass Fail))) +
        Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
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

/-- The potential part of a new pair, when the coin pays the rate of its message. -/
theorem new_pair_core (hw : w ≤ 1) (L : QueryLog SigningSpec)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) (p : Pair)
    (hp0 : s.cache (pblk parameter data p firstCall) = none)
    (hrate : MsgLive L p.1 → Rate parameter data w s p.1) :
    pairE (fun u => potO parameter data w b0 Fail tg initial Lmax (withPair parameter data s p u)
        (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1)) ≤
      potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
        b0 * (if Realized tg initial s then 0 else 1) := by
  set n := signatureLimit - L.length with hn
  set ℓ := (livePairs L P).length with hℓ
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
  unfold potO
  rw [pairE_add, add_right_comm]
  refine add_le_add ?_ hlam
  by_cases hr : Realized tg initial s ∨ signatureLimit < L.length
  · refine le_of_eq_of_le (?_ : _ = (⊥ : ℝ≥0∞)) bot_le
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
    refine le_trans ?_ (coreO_newPair w b0 Fail hw hP hM hp0 L hrate d n (budget - 1))
    refine pairE_mono fun u => ?_
    split_ifs
    · exact bot_le
    · exact le_rfl

end GoodW

end FORS.Security.ForsPotential
