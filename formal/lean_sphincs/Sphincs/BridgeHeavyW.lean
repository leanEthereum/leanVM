import Sphincs.BridgeHeavy
import Sphincs.BridgeSatWFors

/-! The survival-weighted one-coin forest potential of the scan signer with one heavy message. Every
term of the potential is a `termH`: the live message that received more than half of the budget, if
any, acts through the law of its signed view, which needs no coin; while there is none, the future
keeps one spare fresh slot. The rate of the coin is then needed only for the messages with at most
`Qtot / 2` cached digests. -/

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

/-- **A new pair.** Touching a new pair costs one future pair and at most the baseline. The rate is
needed only when the message of the pair is live and not heavy. -/
theorem coreH_newPair (hw : w ≤ 1) {s : State} {P : List Pair} {Ms : List Message}
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) {budget : ℕ}
    (hT : TotalInv parameter data Qtot s budget) (hb : 1 ≤ budget) {p : Pair}
    (hp0 : s.cache (pblk parameter data p) = none) (L : QueryLog SigningSpec)
    (hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1)
    (d : Multiset View) (n k : ℕ) :
    pairE (fun u0 => coreH parameter data Qtot w b0 Fail (withPair parameter data s p u0)
      (addPair parameter P p u0) (addMsg Ms p.1) L d n k) ≤
      coreH parameter data Qtot w b0 Fail s P Ms L d n (k + 1) + b0 := by
  set Ms' := addMsg Ms p.1 with hMs'
  set φ := failMass Fail with hφ
  have hpP := not_mem_of_fresh hP hp0
  set Wp : View → ℝ≥0∞ := fun v => termH parameter data Qtot w s Ms L (· = p) (witnessFn v) d n k with hWp
  set H := hValueH parameter data Qtot w b0 s Ms L d n (k + 1) with hH
  set S := (P.map (candH parameter data Qtot w Fail s Ms L d n (k + 1))).sum with hS
  -- the candidates of the old pairs
  have h2 : ∀ q ∈ P, pairE (fun u0 => candH parameter data Qtot w Fail (withPair parameter data s p u0) Ms' L d n k q) ≤
      candH parameter data Qtot w Fail s Ms L d n (k + 1) q := by
    intro q hq
    have hqp : q ≠ p := fun h => hpP (h ▸ hq)
    have hv : ∀ u0, pview parameter data (withPair parameter data s p u0) q = pview parameter data s q :=
      fun u0 => pview_withPair_other s p q hqp u0
    unfold candH candValueH
    simp only [hv]
    split_ifs
    · simp only [pairE_const, le_refl]
    · exact termH_newPair hw (witness_props _) hM hT hb p hp0 L _ hrate d n k
    · simp only [pairE_const, le_refl]
  -- the candidate of the new pair
  have hnew : ∀ u0, Landed parameter (blockIndex u0) →
      candH parameter data Qtot w Fail (withPair parameter data s p u0) Ms' L d n k p ≤
        (if (viewOf u0).1 ∈ Fail then 1 else 0) + Wp (viewOf u0) := by
    intro u0 hl
    unfold candH candValueH
    rw [pview_withPair_self]
    by_cases hu : Unsigned L p
    · rw [if_pos hu]
      by_cases hF : (viewOf u0).1 ∈ Fail
      · rw [if_pos hF, if_pos hF]
        exact le_self_add
      · rw [if_neg hF, if_neg hF, zero_add]
        exact termH_stop (witness_props _) hM hT hb p hp0 L (· = p) rfl u0 hl d n k
    · rw [if_neg hu]
      exact bot_le
  have hpoint : ∀ u0, coreH parameter data Qtot w b0 Fail (withPair parameter data s p u0)
      (addPair parameter P p u0) Ms' L d n k ≤
      ((if Landed parameter (blockIndex u0) then (fun v : View => (if v.1 ∈ Fail then 1 else 0) + Wp v) (viewOf u0)
          else 0) +
        (P.map fun q => candH parameter data Qtot w Fail (withPair parameter data s p u0) Ms' L d n k q).sum) +
      k * (hValueH parameter data Qtot w b0 (withPair parameter data s p u0) Ms' L d n k + φ) + n * φ := by
    intro u0
    unfold coreH
    refine add_le_add (add_le_add ?_ le_rfl) le_rfl
    unfold addPair
    by_cases hl : Landed parameter (blockIndex u0)
    · rw [if_pos hl, if_pos hl, List.map_cons, List.sum_cons]
      exact add_le_add (hnew u0 hl) le_rfl
    · rw [if_neg hl, if_neg hl, zero_add]
  refine le_trans (pairE_mono hpoint) ?_
  simp only [pairE_add, pairE_const_mul, pairE_const, pairE_list_sum]
  have h1 : pairE (fun u0 => if Landed parameter (blockIndex u0) then
      (fun v : View => (if v.1 ∈ Fail then 1 else 0) + Wp v) (viewOf u0) else 0) =
      landing * (φ + freshAvg Finset.univ Wp) := by
    rw [pairE_landed parameter (fun v => (if v.1 ∈ Fail then 1 else 0) + Wp v) 0, mul_zero, add_zero, freshAvg_add]
    rfl
  have h3 : pairE (fun u0 => hValueH parameter data Qtot w b0 (withPair parameter data s p u0) Ms' L d n k) ≤ H :=
    termH_newPair hw (excess_props b0) hM hT hb p hp0 L _ hrate d n k
  have hfresh : landing * freshAvg Finset.univ Wp ≤ b0 + H := by
    refine le_trans (fresh_forecastH hw b0 s Ms L (· = p) d n k) (add_le_add le_rfl ?_)
    refine le_trans (termH_excl_mono (excess_props b0) s Ms L (fun _ h => False.elim h) d n k) ?_
    exact hValueH_mono w b0 hw s Ms L d n (Nat.le_succ k)
  have hφ1 : landing * φ ≤ φ := mul_le_of_le_one_left' landing_le_one
  have hSle : (P.map fun q => pairE fun u0 => candH parameter data Qtot w Fail (withPair parameter data s p u0) Ms' L d n k q).sum ≤
      S := List.sum_le_sum fun q hq => h2 q hq
  rw [h1]
  unfold coreH
  calc landing * (φ + freshAvg Finset.univ Wp) +
        (P.map fun q => pairE fun u0 => candH parameter data Qtot w Fail (withPair parameter data s p u0) Ms' L d n k q).sum +
        k * (pairE (fun u0 => hValueH parameter data Qtot w b0 (withPair parameter data s p u0) Ms' L d n k) + φ) + n * φ
      ≤ φ + (b0 + H) + S + k * (H + φ) + n * φ := by
        rw [mul_add]
        gcongr
    _ = S + ((k : ℝ≥0∞) + 1) * (H + φ) + n * φ + b0 := by ring
    _ = _ := by push_cast; ring

end NewPairH

/-! ### Order and congruence -/

section OrderH

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem coreH_blocks {s s' : State} (h : ∀ q, s'.cache (pblk parameter data q) = s.cache (pblk parameter data q))
    (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    coreH parameter data Qtot w b0 Fail s' P Ms L d n k = coreH parameter data Qtot w b0 Fail s P Ms L d n k := by
  have hv : ∀ q, pview parameter data s' q = pview parameter data s q := fun q => by unfold pview; rw [h q]
  unfold coreH hValueH candH candValueH
  simp only [hv, termH_blocks h]

variable (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- A grown state with the same digest blocks has no larger potential. -/
theorem potH_grow (hw : w ≤ 1) (Lmax : ℕ) {s s' : State} (hext : Extends s s')
    (h : ∀ q, s'.cache (pblk parameter data q) = s.cache (pblk parameter data q)) (P : List Pair)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    potH parameter data Qtot w b0 Fail tg initial Lmax s' P Ms L d k ≤
      potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d k' := by
  unfold potH
  refine add_le_add ?_ (lam_mono le_rfl hk)
  by_cases hr : Realized tg initial s' ∨ signatureLimit < L.length
  · rw [if_pos hr]; exact bot_le
  · have hr' : ¬(Realized tg initial s ∨ signatureLimit < L.length) := fun h' =>
      hr (h'.imp (realized_of_extends tg initial hext) id)
    rw [if_neg hr, if_neg hr', coreH_blocks w b0 Fail h]
    exact coreH_mono w b0 Fail hw s P Ms L d _ hk

end OrderH

/-! ### Signing a message for the first time, weighted -/

section SignScanHW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (m : Message)

/-- The base value and the averaged walks of a message are below the law of its signed view (the
arithmetic of `sign_termS`). -/
theorem walk_avg_le_sgnM {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (d : Multiset View)
    (excl : Pair → Prop) :
    X d + (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ∑ start, walk nextRand landing (stOf parameter data m s)
        (poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d))
        (freshAvg Finset.univ (fun v => X (d + {v}) - X d)) 0 digestAttemptLimit start ≤
      sgnM parameter data s excl m X d := by
  set gf : View → ℝ≥0∞ := fun v => X (d + {v}) - X d with hgf
  set gp : Randomness → View → ℝ≥0∞ := fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d with hgp
  set c := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hc
  have hcard : c * (Fintype.card Randomness : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  have hbase : X d = c * ∑ start : Randomness, walk nextRand landing (stOf parameter data m s) (fun _ => X d)
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
  have hgoal : c * (∑ start : Randomness, walk nextRand landing (stOf parameter data m s) (fun _ => X d)
        (X d) (X d) digestAttemptLimit start) +
      c * ∑ start, walk nextRand landing (stOf parameter data m s) (poolValue parameter data m s gp)
        (freshAvg Finset.univ gf) 0 digestAttemptLimit start ≤ sgnM parameter data s excl m X d := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    unfold sgnM sgn ws
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ => ?_)
    rw [← walk_add]
    refine walk_mono _ (fun ρ => ?_) (le_of_eq hfr) (by rw [add_zero]) _ start
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
  refine le_trans (le_of_eq ?_) hgoal
  rw [← hbase]

/-- The weighted upper value of a signing call is at most the initial weight times the base value
plus the averaged walks of the message (the scan part of `upper_expectW`). -/
theorem upper_scanW (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data m ρ) = .none)
    (X : Multiset View → ℝ≥0∞) (s : State) (d : Multiset View)
    (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 *
          (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
            outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out))) ≤
      weight tg initial s *
        (X d + (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ∑ start, walk nextRand landing (stOf parameter data m s)
          (poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d))
          (freshAvg Finset.univ (fun v => X (d + {v}) - X d)) 0 digestAttemptLimit start) := by
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

/-- **One signing call, the law of the signed view, weighted** (the weighted `sign_termS`). -/
theorem sign_termSW (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data m ρ) = .none)
    {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (d : Multiset View)
    (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 *
          (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
            outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out))) ≤
      weight tg initial s * sgnM parameter data s excl m X d :=
  le_trans (upper_scanW tg initial model parameter data m hparse hkind X s d excl budget)
    (mul_le_mul' le_rfl (walk_avg_le_sgnM parameter data m hX s d excl))

end SignScanHW

section SignExpectHW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} {w : ℝ≥0∞} {m : Message} {s : State} {n : ℕ}
  {d : Multiset View} {f : Multiset View → ℝ≥0∞}

/-- **A dominated term, weighted** (the weighted `term_expectH`). -/
theorem term_expectHW (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data m ρ) = .none) (hf : MonoFin f)
    {Ms : List Message} (hM : MInv parameter data s Ms) {budgetT : ℕ} (hT : TotalInv parameter data Qtot s budgetT)
    {L : QueryLog SigningSpec} (hm : MsgLive L m) (excl : Pair → Prop) (budget k : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 *
          creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d f L Ms excl out J) k []) ≤
      weight tg initial s * termH parameter data Qtot w s Ms L excl f d (n + 1) k := by
  rw [← termH_addMsg hM L excl m f d (n + 1) k]
  unfold termH
  simp only [← mul_assoc]
  rw [creations_tsum, ← creations_const_mul]
  refine creations_mono (fun J => ?_) k []
  simp only [mul_assoc]
  have hperm : (live L (addMsg Ms m)).Perm (m :: restMsgs m L Ms) := live_perm hm hM.nodup
  have hrestne : ∀ m' ∈ restMsgs m L Ms, m' ≠ m := by
    intro m' hm'
    unfold restMsgs at hm'
    simpa using (List.mem_filter.1 hm').2
  have hX : Monotone' (restH parameter data Qtot w m s n f L Ms excl J) := valH_mono hf.1 s excl _ _ n J
  by_cases hH : Heavy parameter data Qtot s m
  · -- the signed message is heavy: the law of its signed view
    have hnoneR : heavyMsg parameter data Qtot s (restMsgs m L Ms) = none :=
      heavyMsg_eq_none.2 fun m' hm' hh => hrestne m' hm' (heavy_unique hT hh hH)
    have hlightR : lightMsgs parameter data Qtot s (restMsgs m L Ms) = restMsgs m L Ms := lightMsgs_of_none hnoneR
    have hsomeV : heavyMsg parameter data Qtot s (live L (addMsg Ms m)) = some m :=
      (heavyMsg_eq_some_iff hT).2 ⟨hperm.mem_iff.2 (List.mem_cons_self ..), hH⟩
    have hlightV : (lightMsgs parameter data Qtot s (live L (addMsg Ms m))).Perm (restMsgs m L Ms) := by
      have h1 := hperm.filter (fun m' => decide (¬Heavy parameter data Qtot s m'))
      rw [List.filter_cons, if_neg (by simpa using hH)] at h1
      rw [← hlightR]
      exact h1
    refine le_trans (sign_termSW tg initial model parameter data m hparse hkind hX s d excl budget)
      (mul_le_mul' le_rfl (le_of_eq ?_))
    have hL : sgnM parameter data s excl m (restH parameter data Qtot w m s n f L Ms excl J) d =
        sgnM parameter data s excl m
          (grpAll parameter data s excl (restMsgs m L Ms) (virtualOnce Finset.univ w f (n + 1) J)) d := by
      unfold restH
      rw [hnoneR, hlightR]
      rfl
    have hR : baseH parameter data Qtot w s (addMsg Ms m) L excl f d (n + 1) J =
        sgnM parameter data s excl m
          (grpAll parameter data s excl (restMsgs m L Ms) (virtualOnce Finset.univ w f (n + 1) J)) d := by
      unfold baseH
      rw [hsomeV, valH_perm_msgs s excl hlightV, valH_heavy_eq]
    rw [hL, hR]
  · -- the signed message is light: its group and one fresh slot
    have hhv : heavyMsg parameter data Qtot s (live L (addMsg Ms m)) =
        heavyMsg parameter data Qtot s (restMsgs m L Ms) := by
      cases hR : heavyMsg parameter data Qtot s (restMsgs m L Ms) with
      | none =>
          refine heavyMsg_eq_none.2 fun m' hm' => ?_
          rcases List.mem_cons.1 (hperm.mem_iff.1 hm') with h | h
          · rw [h]; exact hH
          · exact heavyMsg_eq_none.1 hR m' h
      | some h =>
          exact (heavyMsg_eq_some_iff hT).2
            ⟨hperm.mem_iff.2 (List.mem_cons_of_mem _ (heavyMsg_some hR).1), (heavyMsg_some hR).2⟩
    have hlightV : (lightMsgs parameter data Qtot s (live L (addMsg Ms m))).Perm
        (m :: lightMsgs parameter data Qtot s (restMsgs m L Ms)) := by
      have h1 := hperm.filter (fun m' => decide (¬Heavy parameter data Qtot s m'))
      rw [List.filter_cons, if_pos (by simpa using hH)] at h1
      exact h1
    refine le_trans (upper_expectW tg initial model parameter data m hparse hkind hX s d excl budget)
      (mul_le_mul' le_rfl (le_of_eq ?_))
    have hR : baseH parameter data Qtot w s (addMsg Ms m) L excl f d (n + 1) J =
        grpM parameter data s excl m (valH parameter data w s excl
          (lightMsgs parameter data Qtot s (restMsgs m L Ms))
          (heavyMsg parameter data Qtot s (restMsgs m L Ms)) f (n + 1) J) d := by
      unfold baseH
      rw [hhv, valH_perm_msgs s excl hlightV]
      rfl
    rw [hR]
    unfold grpM
    exact grp_congr _ _ (fun e => (valH_succ excl _ _ J e).symm) d

end SignExpectHW

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

section SignPointHW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight))) (m : Message)

/-- **The potential after one signing outcome.** -/
theorem sign_pointH (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d) (hT : TotalInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' : ℕ} (hk : k' ≤ budget) :
    (if Realized tg initial out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length then 0
      else coreH parameter data Qtot w b0 Fail out.2 (newPairs parameter data m s out.2 ++ P) (addMsg Ms m)
        (L ++ [⟨m, r⟩]) (discAfter parameter data m s d out)
        (signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length) k') ≤
      if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
      else canonH parameter data Qtot w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out := by
  obtain ⟨_, hP', _, _, _, hview⟩ := sign_paramsS tg initial model Fail Qtot hparse hfail budget
    s P Ms d R hprep hP hM hD hT.countInv out hout r hr
  have hext := interp_extends tg initial model _ budget s out hout
  have hpost := source_post tg initial model parameter data m (fun ρ => hparse (m, ρ)) Fail hfail
    budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  by_cases hcase : Realized tg initial out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length
  · rw [if_pos hcase]; exact bot_le
  rw [if_neg hcase]
  have hreal : ¬Realized tg initial s := fun h => hcase (Or.inl (realized_of_extends tg initial hext h))
  have hlen : L.length < signatureLimit := by
    have := hcase
    simp only [List.length_append, List.length_singleton, not_or, not_lt] at this
    omega
  rw [if_neg (by push Not; exact ⟨hreal, hlen⟩)]
  have hn : signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length = signatureLimit - (L.length + 1) := by simp
  rw [hn]
  set n := signatureLimit - (L.length + 1) with hndef
  unfold coreH canonH
  rw [List.map_append, List.sum_append]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · -- new pairs: only a failed fresh pair stays a candidate
    rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u0, hnew, _, h0, hl, hs0, _, hfl, hsig⟩ | ⟨_, _, _, hnew, _⟩
    · unfold newPairs; rw [hnew]; simp
    · have hv : pview parameter data out.2 (m, ρ) = viewOf u0 := pview_of_cached h0
      have hlist : newPairs parameter data m s out.2 = [(m, ρ)] := by
        unfold newPairs; rw [hnew, Finset.toList_singleton]; rfl
      rw [hlist]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      refine le_trans ?_ (freshNewWeight_ge hr hs0 h0 hl (fun v => if v.1 ∈ Fail then 1 else 0))
      unfold candH
      rw [hv]
      split_ifs with hu hF hF'
      · exact le_rfl
      · exfalso
        rcases r with _ | sig
        · exact hF (hfl rfl)
        · exact not_unsigned_signed (m := m) (L := L) (sig := sig) (by rw [hsig sig rfl]; exact hu)
      · exact bot_le
      · exact le_rfl
    · unfold newPairs; rw [hnew]; simp
  · -- old candidates
    refine List.sum_le_sum fun q hq => ?_
    unfold candH
    by_cases hU' : Unsigned (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q
    · have hU := unsigned_of_append hU'
      rw [if_pos hU', if_pos hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValueH
        rw [hview q hq]
        refine post_term_leH tg initial model parameter data Qtot w Fail m hw (witness_props _) hparse hfail budget
          s Ms L d hprep out hout r hr (· = q) (fun sig hsig _ heq => ?_) n hk
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [if_neg hU']
      exact bot_le
  · -- the excess forecast
    refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValueH
    exact post_term_leH tg initial model parameter data Qtot w Fail m hw (excess_props b0) hparse hfail budget
      s Ms L d hprep out hout r hr (fun _ => False) (fun _ _ _ h => h) n hk

/-- **The signing step in expectation, weighted**, for a message signed for the first time. -/
theorem sign_expectHW (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (hm : MsgLive L m) (d : Multiset View) (hM : MInv parameter data s Ms)
    {budgetT : ℕ} (hT : TotalInv parameter data Qtot s budgetT) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 * (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canonH parameter data Qtot w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out)) ≤
      weight tg initial s * (if Realized tg initial s ∨ signatureLimit < L.length then 0
        else coreH parameter data Qtot w b0 Fail s P Ms L d (signatureLimit - L.length) budget) := by
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
  have hTm : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d (witnessFn (pview parameter data s q))
          L Ms (· = q) out J) budget []) else 0)) ≤
      weight tg initial s * candH parameter data Qtot w Fail s Ms L d (n + 1) budget q := by
    intro q _
    unfold candH
    split_ifs
    · exact hconst 1
    · unfold candValueH
      exact term_expectHW tg initial model hparse' hkind' (witness_props _) hM hT hm _ budget budget
    · exact hconst 0
  have hH : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d (excess b0)
        L Ms (fun _ => False) out J) budget []) ≤
      weight tg initial s * hValueH parameter data Qtot w b0 s Ms L d (n + 1) budget := by
    unfold hValueH
    exact term_expectHW tg initial model hparse' hkind' (excess_props b0) hM hT hm _ budget budget
  have hLS : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
        else creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d
          (witnessFn (pview parameter data s q)) L Ms (· = q) out J) budget [])
        else 0).sum) ≤
      weight tg initial s * (P.map (candH parameter data Qtot w Fail s Ms L d (n + 1) budget)).sum := by
    simp only [← mul_assoc]
    rw [tsum_list_sum, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun q hq => by simpa only [mul_assoc] using hTm q hq
  have hHC : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
        (fun J => upperH parameter data Qtot w m s n d (excess b0) L Ms (fun _ => False) out J) budget [] +
          failMass Fail))) ≤
      weight tg initial s * ((budget : ℝ≥0∞) * (hValueH parameter data Qtot w b0 s Ms L d (n + 1) budget +
        failMass Fail)) := by
    have hpt : ∀ out : Run HashInput Coordinate (Option Signature) × State,
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperH parameter data Qtot w m s n d (excess b0) L Ms (fun _ => False) out J) budget [] +
              failMass Fail))) =
        (budget : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * creations Finset.univ landing
            (fun J => upperH parameter data Qtot w m s n d (excess b0) L Ms (fun _ => False) out J) budget [])) +
        (budget : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * failMass Fail)) := by
      intro out
      ring
    simp only [hpt, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    calc _ ≤ (budget : ℝ≥0∞) * (weight tg initial s * hValueH parameter data Qtot w b0 s Ms L d (n + 1) budget) +
          (budget : ℝ≥0∞) * (weight tg initial s * failMass Fail) :=
          add_le_add (mul_le_mul' le_rfl hH) (mul_le_mul' le_rfl (hconst _))
      _ = _ := by ring
  have hsplit : ∀ out : Run HashInput Coordinate (Option Signature) × State,
      Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (weight tg initial out.2 * canonH parameter data Qtot w b0 Fail m s P Ms L d n budget out) =
      Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
            else creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d
              (witnessFn (pview parameter data s q)) L Ms (· = q) out J) budget [])
            else 0).sum) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperH parameter data Qtot w m s n d (excess b0) L Ms (fun _ => False) out J) budget [] +
              failMass Fail))) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (weight tg initial out.2 * ((n : ℝ≥0∞) * failMass Fail)) := by
    intro out
    unfold canonH
    ring
  simp only [hsplit, ENNReal.tsum_add]
  calc _ ≤ weight tg initial s * failMass Fail +
        weight tg initial s * (P.map (candH parameter data Qtot w Fail s Ms L d (n + 1) budget)).sum +
        weight tg initial s * ((budget : ℝ≥0∞) * (hValueH parameter data Qtot w b0 s Ms L d (n + 1) budget +
          failMass Fail)) + weight tg initial s * ((n : ℝ≥0∞) * failMass Fail) :=
        add_le_add (add_le_add (add_le_add hFN hLS) hHC) (hconst _)
    _ = _ := by
        unfold coreH
        push_cast
        ring

end SignPointHW

/-! ### Weighted paid programs -/

section GoodHW

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A program whose final value, weighted by the final survival weight, is paid by the weighted
potential with one heavy message and the weighted baseline payments. -/
def GoodHW (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → MInv parameter data s Ms → DInv R d →
      TotalInv parameter data Qtot s budget →
      ∑' out, Pr[= out | interp tg initial model prog budget s] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
        weight tg initial s * potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wflag tg initial model prog budget s

theorem goodHW_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (next v)) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hT
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
        (weight tg initial s * potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wflag tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hprep hP hM hD hT) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) (le_of_eq ?_)
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- The potential part of a new pair, when the coin pays the rate of its message if it is live and
not heavy. -/
theorem new_pair_coreH (hw : w ≤ 1) (L : QueryLog SigningSpec)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms)
    (hT : TotalInv parameter data Qtot s budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p) = none)
    (hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potH parameter data Qtot w b0 Fail tg initial Lmax (withPair parameter data s p u) (addPair parameter P p u)
          (addMsg Ms p.1) L d (budget - 1) ≤
      potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
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
  unfold potH
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
    have hcore : coreH parameter data Qtot w b0 Fail s P Ms L d n budget =
        coreH parameter data Qtot w b0 Fail s P Ms L d n (budget - 1 + 1) := by rw [Nat.sub_add_cancel hb]
    rw [hcore]
    refine le_trans ?_ (coreH_newPair w b0 Fail hw hP hM hT hb hp0 L hrate d n (budget - 1))
    unfold pairE
    refine ENNReal.tsum_le_tsum fun u => mul_le_mul_right ?_ _
    split_ifs
    · exact bot_le
    · exact le_rfl

/-- A new pair: its block is read fresh, weighted. The coin pays the rate of a message with at most
`Qtot / 2` cached digests. -/
theorem new_pair_boundHW (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hT : TotalInv parameter data Qtot s budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p) = none) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
          (s.store (pblk parameter data p) u)] * (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
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
          unfold potH
          exact le_trans (mul_le_mul' le_rfl le_add_self) le_self_add
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  have hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1 :=
    fun hlive hnh => rate_of_fair hfair s p.1 (le_trans (cachedCount_le_of_not_heavy hnh) hQ)
      (le_trans (landedCount_le hP L hlive) hlen)
  have hone : ∀ u, ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
        (s.store (pblk parameter data p) u)] * (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potH parameter data Qtot w b0 Fail tg initial Lmax (withPair parameter data s p u)
          (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) +
        b0 * wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p) u) := fun u => by
    have := h u (budget - 1) _ _ _ d R (prepared_store initial s hprep _ u hp0) (pinv_withPair hP hp0 u)
      (minv_withPair hM p u) hD (totalInv_withPair hT hb p u)
    rwa [hws u] at this
  refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hone u) _) ?_
  simp only [mul_add, ENNReal.tsum_add]
  rw [← add_assoc]
  refine add_le_add ?_ (le_of_eq ?_)
  · calc _ = weight tg initial s * ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          potH parameter data Qtot w b0 Fail tg initial Lmax (withPair parameter data s p u)
            (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) := by
          simp only [mul_left_comm _ (weight tg initial s), ENNReal.tsum_mul_left]
      _ ≤ weight tg initial s * (potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
            b0 * (if Realized tg initial s then 0 else 1)) :=
          mul_le_mul_right (new_pair_coreH parameter data Qtot w b0 Fail Lmax tg initial hfair.le_one L budget hb
            s P Ms d hP hM hT p hp0 hrate) _
      _ ≤ _ := by
          rw [mul_add]
          refine add_le_add le_rfl ?_
          rw [mul_left_comm]
          refine mul_le_mul_right ?_ _
          split_ifs <;> simp
  · simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **One ordinary query, weighted.** -/
theorem goodHW_ordinary (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (next v)) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L
      (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hT
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
    exact new_pair_boundHW parameter data Qtot w b0 Fail Lmax tg initial model hkind hfair hQ L next h budget hb
      s P Ms d R hprep hP hM hD hT p hp0
  · have hmean : ∑' r, Pr[= r | ordinaryStep model x s.known s] * weight tg initial r.2 ≤ weight tg initial s := by
      have := meanWeight_costStep_leW tg initial model (.inl (.inr (.inl x))) s
      rwa [costStep_ordinary] at this
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (weight tg initial r.2 * potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
            b0 * wflag tg initial model (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ?_ _
            have hext := ordinaryStep_extends model x s r hr
            have hblocks := same_blocks (parameter := parameter) (data := data) hext
              (ordinaryStep_cache_ne model x s r hr) hnew
            obtain ⟨hP', -⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hP
            refine le_trans (h r.1 (budget - 1) r.2 P Ms d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' (minv_blocks hblocks hM) hD
              (totalInv_ordinary model hT hb x r hr)) (add_le_add ?_ le_rfl)
            exact mul_le_mul_right
              (potH_grow w b0 Fail tg initial hfair.le_one Lmax hext hblocks P Ms L d (Nat.sub_le _ _)) _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add]
          refine add_le_add ?_ ?_
          · calc _ = (∑' r, Pr[= r | ordinaryStep model x s.known s] * weight tg initial r.2) *
                  potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget := by
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun r => by ring
              _ ≤ _ := mul_le_mul_left hmean _
          · refine le_add_left (le_of_eq ?_)
            simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **Leaf, weighted.** A forest cover with no decided hit is paid by the potential. -/
theorem goodHW_pure (hw : w ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R hprep hP hM hD hT
  rw [wflag_pure, mul_zero, add_zero, interp_pure, tsum_probOutput_pure_mul]
  refine mul_le_mul_right ?_ _
  unfold finalValue
  simp only [Option.elim, List.append_nil]
  split_ifs with hcov
  swap
  · exact bot_le
  obtain ⟨⟨hvalid, digest, hdig, hland, hunsigned, hcovered⟩, hreal⟩ := hcov
  set q : Pair := (forgery.message, forgery.signature.randomness) with hq
  unfold HiddenBridge.cachedDigest at hdig
  cases h0 : s.cache (pblk parameter data q) with
  | none =>
      have h0' : s.cache (tweakableHashInput parameter .message
          (messageDigestPayload data.root forgery.message forgery.signature.randomness)) = none := h0
      rw [h0'] at hdig; cases hdig
  | some a =>
      have h0' : s.cache (tweakableHashInput parameter .message
          (messageDigestPayload data.root forgery.message forgery.signature.randomness)) = some a := h0
      rw [h0'] at hdig
      have hdig' : truncateMessageDigest a = digest := by
        simpa using hdig
      subst hdig'
      have hlanded : LandedIn parameter data s q := ⟨a, h0, by rwa [Completeness.digestIndex_truncate] at hland⟩
      have hqP := (hP.mem q).2 hlanded
      have hv : pview parameter data s q = Lifetime.localDigestView (truncateMessageDigest a) := by
        simp only [pview, h0, Option.elim, viewOf]
      unfold potH
      rw [if_neg (by
        rintro (h | h)
        · exact hreal h
        · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
      refine le_trans ?_ le_self_add
      unfold coreH
      refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
      unfold candH
      rw [if_pos (show Unsigned L q from hunsigned)]
      split_ifs
      · exact le_rfl
      · unfold candValueH
        calc (1 : ℝ≥0∞) ≤ witnessFn (pview parameter data s q) d := by
              unfold witnessFn
              rw [hv]
              exact witness_pos_of_covered hD _ hcovered
          _ ≤ _ := base_le_termH hw (witness_props _) s Ms L _ d _ _

/-- Lifted hash computations are sequences of ordinary queries. -/
theorem goodHW_liftHash (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) (L : QueryLog SigningSpec) {α : Type}
    (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (next a)) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L
      ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodHW_ordinary parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hdigest hfair hQ L
        query _ ih

/-- **One signing call, weighted**, on a message that was never signed before. -/
theorem goodHW_sign (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (m : Message) (L : QueryLog SigningSpec) (hm : MsgLive L m)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model (L ++ [⟨m, r⟩]) (next r)) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (signCostSource parameter data m >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hT
  set sign := signCostSource parameter data m with hsign
  set ℓ := (livePairs L P).length with hℓ
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => wflag tg initial model (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canonH parameter data Qtot w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
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
        obtain ⟨hprep', hP', hM', hD', _, _⟩ := sign_paramsS tg initial model Fail Qtot hparse (hfail m)
          budget s P Ms d R hprep hP hM hD hT.countInv o1 ho1 r hres
        have hT' : TotalInv parameter data Qtot o1.2 (budget - traceCost o1.1.2.2.1) :=
          totalInv_interp tg initial model sign hT o1 ho1
        have hIH := h r (budget - traceCost o1.1.2.2.1) o1.2 _ _ _ _ hprep' hP' hM' hD' hT'
        have hpot := sign_pointH tg initial model parameter data Qtot w b0 Fail m hparse (hfail m) hw
          budget s P Ms L d R hprep hP hM hD hT o1 ho1 r hres (Nat.sub_le budget (traceCost o1.1.2.2.1))
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
        · unfold potH
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
        unfold potH
        rw [mul_add]
        exact add_le_add (add_le_add
          (sign_expectHW tg initial model parameter data Qtot w b0 Fail m hparse hkind budget s P Ms L hm d hM hT)
          (interp_weight_constW tg initial model (s := s) sign budget _)) (mul_le_mul_right hflag _)

theorem goodHW_finish (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (finishGame parameter data L forgery) := by
  unfold finishGame
  exact goodHW_liftHash parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hdigest hfair hQ L _ _
    fun v => goodHW_pure parameter data Qtot w b0 Fail Lmax tg initial model hfair.le_one L forgery v

/-- **The weighted one-coin potential with one heavy message, through any adversary that never
repeats a message.** The coin only pays the rate of a message with at most `Qtot / 2` cached
digests. -/
theorem goodHW_advProg (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      exact goodHW_finish parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hdigest hfair hQ L
        forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodHW_draw parameter data Qtot w b0 Fail Lmax tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodHW_ordinary parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hdigest hfair hQ
          L bytes _ fun v => ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodHW_sign parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hfail hfair.le_one
          message L hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end GoodHW

end Sphincs.Security.ForsPotential
