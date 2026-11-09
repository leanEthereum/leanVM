module

public import FORS.LargeBudget.HeavyTerm
public import FORS.LargeBudget.WeightedPotential

@[expose] public section

/-! The survival-weighted one-coin FORS potential of the scan signer with one heavy message. Every
term of the potential is a `termH`: the live message that received more than half of the budget, if
any, acts through the law of its signed view, which needs no coin; while there is none, the future
keeps one spare fresh slot. The rate of the coin is then needed only for the messages with at most
`Qtot / 2` cached digests. -/

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

/-! ### The potential -/

section DefsH

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The forecast of a candidate: its own pair discloses nothing for it. -/
noncomputable def candValueH (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  termH parameter data Qtot w s Ms L (· = p) (witnessFn (pview parameter data s p)) d n k

/-- The excess forecast of a new pair. -/
noncomputable def hValueH (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  termH parameter data Qtot w s Ms L (fun _ => False) (excess b0) d n k

/-- The value of a candidate: one at a failing index, its forecast otherwise; zero once signed. -/
noncomputable def candH (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (p : Pair) : ℝ≥0∞ :=
  if Unsigned L p then
    (if (pview parameter data s p).1 ∈ Fail then 1 else candValueH parameter data Qtot w s Ms L d n k p)
  else 0

/-- The potential without the hit and transcript tests. -/
noncomputable def coreH (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (n k : ℕ) : ℝ≥0∞ :=
  (P.map (candH parameter data Qtot w Fail s Ms L d n k)).sum +
    k * (hValueH parameter data Qtot w b0 s Ms L d n k + failMass Fail) + n * failMass Fail

variable (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- **The potential with one heavy message.** -/
noncomputable def potH (Lmax : ℕ) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  (if Realized tg initial s ∨ signatureLimit < L.length then 0
    else coreH parameter data Qtot w b0 Fail s P Ms L d (signatureLimit - L.length) k) +
  lam Lmax (livePairs L P).length k

end DefsH

/-! ### A new pair -/

section NewPairH

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem candH_mono (hw : w ≤ 1) (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (p : Pair) :
    candH parameter data Qtot w Fail s Ms L d n k p ≤ candH parameter data Qtot w Fail s Ms L d n k' p := by
  unfold candH candValueH
  split_ifs
  · exact le_rfl
  · exact termH_mono hw (witness_props _) s Ms L _ d n hk
  · exact le_rfl

theorem hValueH_mono (hw : w ≤ 1) (s : State) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    hValueH parameter data Qtot w b0 s Ms L d n k ≤ hValueH parameter data Qtot w b0 s Ms L d n k' :=
  termH_mono hw (excess_props b0) s Ms L _ d n hk

theorem coreH_mono (hw : w ≤ 1) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    coreH parameter data Qtot w b0 Fail s P Ms L d n k ≤ coreH parameter data Qtot w b0 Fail s P Ms L d n k' := by
  unfold coreH
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => candH_mono w Fail hw s Ms L d n hk q) ?_) le_rfl
  exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValueH_mono w b0 hw s Ms L d n hk) le_rfl)

end NewPairH

/-! ### Order and congruence -/

section OrderH

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem coreH_blocks {s s' : State}
    (h : ∀ q, s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall))
    (hv : ∀ q, LandedIn parameter data s q → ∀ call,
      s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call))
    {P : List Pair} (hPl : ∀ q ∈ P, LandedIn parameter data s q)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    coreH parameter data Qtot w b0 Fail s' P Ms L d n k = coreH parameter data Qtot w b0 Fail s P Ms L d n k := by
  have hpv : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q :=
    fun q hq => pview_congr parameter data (hv q (hPl q hq))
  unfold coreH hValueH candH candValueH
  rw [termH_blocks h hv,
    List.map_congr_left fun q hq => by rw [hpv q hq, termH_blocks h hv]]

variable (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- A grown state with the same digest blocks has no larger potential. -/
theorem potH_grow (hw : w ≤ 1) (Lmax : ℕ) {s s' : State} (hext : Extends s s')
    (h : ∀ q, s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall))
    (hv : ∀ q, LandedIn parameter data s q → ∀ call,
      s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call))
    {P : List Pair} (hPl : ∀ q ∈ P, LandedIn parameter data s q)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    potH parameter data Qtot w b0 Fail tg initial Lmax s' P Ms L d k ≤
      potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d k' := by
  unfold potH
  refine add_le_add ?_ (lam_mono le_rfl hk)
  by_cases hr : Realized tg initial s' ∨ signatureLimit < L.length
  · rw [ite_eq_left hr]; exact bot_le
  · have hr' : ¬(Realized tg initial s ∨ signatureLimit < L.length) := fun h' =>
      hr (h'.imp (realized_of_extends tg initial hext) id)
    rw [ite_eq_right hr, ite_eq_right hr', coreH_blocks w b0 Fail h hv hPl]
    exact coreH_mono w b0 Fail hw s P Ms L d _ hk

end OrderH

/-! ### Signing a message for the first time, weighted -/

section SignScanHW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (m : Message)

/-- The base value and the averaged walks of a message are below the law of its signed view (the
arithmetic of `sign_termSW`). -/
theorem walk_avg_le_sgnM {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (d : Multiset View)
    (excl : Pair → Prop) :
    X d + (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ∑ start, walk (nextRand (data.steps m)) landing (stOf parameter data m s)
        (poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d))
        (freshAvg Finset.univ (fun v => X (d + {v}) - X d)) 0 digestAttemptLimit start ≤
      sgnM parameter data s excl m X d := by
  set gf : View → ℝ≥0∞ := fun v => X (d + {v}) - X d with hgf
  set gp : Randomness → View → ℝ≥0∞ := fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d with hgp
  set c := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hc
  have hcard : c * (Fintype.card Randomness : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  have hbase : X d = c * ∑ start : Randomness, walk (nextRand (data.steps m)) landing (stOf parameter data m s) (fun _ => X d)
      (X d) (X d) digestAttemptLimit start := by
    simp only [walk_const landing_le_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, hcard, one_mul]
  have hfr : X d + freshAvg Finset.univ gf = freshAvg Finset.univ (fun v => X (d + {v})) := by
    calc X d + freshAvg Finset.univ gf = freshAvg Finset.univ (fun v => X d + gf v) := by
          rw [freshAvg_add, freshAvg_const _ Finset.univ_nonempty]
      _ = _ := by
          congr 1
          funext v
          exact add_tsub_cancel_of_le (hX _ _ (Multiset.le_add_right _ _))
  have hgoal : c * (∑ start : Randomness, walk (nextRand (data.steps m)) landing (stOf parameter data m s) (fun _ => X d)
        (X d) (X d) digestAttemptLimit start) +
      c * ∑ start, walk (nextRand (data.steps m)) landing (stOf parameter data m s) (poolValue parameter data m s gp)
        (freshAvg Finset.univ gf) 0 digestAttemptLimit start ≤ sgnM parameter data s excl m X d := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    unfold sgnM sgn ws
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ => ?_)
    rw [← walk_add]
    refine walk_mono _ (fun ρ => ?_) (le_of_eq hfr) (by rw [add_zero]) _ start
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
  refine le_trans (le_of_eq ?_) hgoal
  rw [← hbase]

/-- The weighted upper value of a signing call is at most the initial weight times the base value
plus the averaged walks of the message (the scan part of `upper_expectW`). -/
theorem upper_scanW (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none)
    (X : Multiset View → ℝ≥0∞) (s : State) (hinv : PairInv parameter data m s) (d : Multiset View)
    (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        (weight tg initial out.2 *
          (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
            outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out))) ≤
      weight tg initial s *
        (X d + (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ∑ start, walk (nextRand (data.steps m)) landing (stOf parameter data m s)
          (poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d))
          (freshAvg Finset.univ (fun v => X (d + {v}) - X d)) 0 digestAttemptLimit start) := by
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

/-- **One signing call, the law of the signed view, weighted**. -/
theorem sign_termSW (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none)
    {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (hinv : PairInv parameter data m s)
    (d : Multiset View) (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        (weight tg initial out.2 *
          (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
            outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out))) ≤
      weight tg initial s * sgnM parameter data s excl m X d :=
  le_trans (upper_scanW tg initial model parameter data m hparse hkind X s hinv d excl budget)
    (mul_le_mul' le_rfl (walk_avg_le_sgnM parameter data m hX s d excl))

end SignScanHW

/-! ### The potential after signing a message for the first time -/

section CanonH

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)

/-- Bound for one outcome of a signing call. -/
noncomputable def canonH (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d (witnessFn (pview parameter data s q))
        L Ms (· = q) out J) k []) else 0).sum +
  k * (creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d (excess b0)
      L Ms (fun _ => False) out J) k [] + failMass Fail) +
  n * failMass Fail

end CanonH

/-! ### Weighted paid programs -/

end FORS.Security.ForsPotential
