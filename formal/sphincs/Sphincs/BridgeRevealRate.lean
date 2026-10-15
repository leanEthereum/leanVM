import Sphincs.BridgeRunFacts
import Sphincs.BridgeForestNear
import Sphincs.H0Mark
import Sphincs.BridgeRevealAll

/-! **One signing call opens a given forest chain rarely.** A fresh landed digest opens chain `i` of
the WOTS key `a` of subtree `j` under the leaf `sp` of tree `c` at the index of a given step, at or
below a position `k ≤ 3`, with probability at most `2^-b · 2^-4 · 2^-3 · 123/256`: the digest picks
the index, the leaf and the WOTS key uniformly, and at most 123 of the 256 codewords have digit `i`
at least one. The cached landed pairs of the signed message add the probability that the scan from a
uniform start signs with one of them (`hitMass`). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenBridge
open Sphincs.LoopWalk
open SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Counting codewords -/

/-- The codewords whose digit `i` is at least one. -/
def litCount (i : FChain) : ℕ := (Finset.univ.filter fun w : LutIdx => 1 ≤ (lut w i).val).card

omit [Params] in
theorem litCount_le_all : ∀ i : FChain, litCount i ≤ 123 := by
  unfold litCount
  decide +kernel

omit [Params] in
theorem sub_eq_or_other (j j' : SubIdx) : j' = j ∨ j' = otherSub j := by
  fin_cases j <;> fin_cases j' <;> decide

omit [Params] in
/-- The fields opening a given chain at or below position `k < 4`. -/
theorem card_opens_le (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (hk : k < chainTop) :
    (Finset.univ.filter fun x : FieldVal => (decodeMark x).super = sp ∧ (decodeMark x).child j = a ∧
      chainTop - (lut ((decodeMark x).word j) i).val ≤ k).card ≤ 2048 * 123 := by
  set S := Finset.univ.filter fun x : FieldVal => (decodeMark x).super = sp ∧ (decodeMark x).child j = a ∧
    chainTop - (lut ((decodeMark x).word j) i).val ≤ k with hS
  set T := (Finset.univ : Finset (ChildIdx × LutIdx)) ×ˢ (Finset.univ.filter fun w : LutIdx => 1 ≤ (lut w i).val)
    with hT
  set g : FieldVal → (ChildIdx × LutIdx) × LutIdx := fun x =>
    (((decodeMark x).child (otherSub j), (decodeMark x).word (otherSub j)), (decodeMark x).word j) with hg
  have hmaps : Set.MapsTo g (S : Set FieldVal) (T : Set ((ChildIdx × LutIdx) × LutIdx)) := by
    intro x hx
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    rw [Finset.mem_coe]
    simp only [hT, hg, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter]
    have := hx.2.2
    simp only [chainTop] at this
    omega
  have hinj : Set.InjOn g S := by
    intro x hx y hy hxy
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    simp only [hg, Prod.mk.injEq] at hxy
    obtain ⟨⟨hc, hw⟩, hwj⟩ := hxy
    have hm : decodeMark x = decodeMark y := by
      have hsup : (decodeMark x).super = (decodeMark y).super := hx.1.trans hy.1.symm
      have hch : (decodeMark x).child = (decodeMark y).child := by
        funext j'
        rcases sub_eq_or_other j j' with rfl | rfl
        · exact hx.2.1.trans hy.2.1.symm
        · exact hc
      have hwd : (decodeMark x).word = (decodeMark y).word := by
        funext j'
        rcases sub_eq_or_other j j' with rfl | rfl
        · exact hwj
        · exact hw
      cases hX : decodeMark x
      cases hY : decodeMark y
      rw [hX, hY] at hsup hch hwd
      simp only at hsup hch hwd
      rw [hsup, hch, hwd]
    exact markEquiv.injective hm
  calc S.card ≤ T.card := Finset.card_le_card_of_injOn g hmaps hinj
    _ = 2048 * litCount i := by
        rw [hT, Finset.card_product, Finset.card_univ, Fintype.card_prod]
        rfl
    _ ≤ 2048 * 123 := Nat.mul_le_mul_left _ (litCount_le_all i)

/-! ### Hitting one chain -/

/-- A kept view opens a forest chain at or below position `k`. -/
noncomputable def opensAt (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (k : ℕ) (v : View) : ℝ≥0∞ :=
  if v.1 = localIdx index ∧ (decodeMark (v.2 c)).super = sp ∧ (decodeMark (v.2 c)).child j = a ∧
    chainTop - (lut ((decodeMark (v.2 c)).word j) i).val ≤ k then 1 else 0

/-- The reveal rate `123 · 2^-b · 2^-15`. -/
noncomputable def revRate : ℝ≥0∞ := 123 * ((2 ^ subtreeHeight * 2 ^ 15 : ℕ) : ℝ≥0∞)⁻¹

theorem opensAt_le_one (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (k : ℕ) (v : View) : opensAt index c sp j a i k v ≤ 1 := by
  unfold opensAt
  split_ifs <;> simp

/-- **A uniform kept view opens a given chain with probability at most the reveal rate.** -/
theorem freshAvg_opensAt (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (k : ℕ) (hk : k < chainTop) : freshAvg Finset.univ (opensAt index c sp j a i k) ≤ revRate := by
  set P : FieldVal → Prop := fun x => (decodeMark x).super = sp ∧ (decodeMark x).child j = a ∧
    chainTop - (lut ((decodeMark x).word j) i).val ≤ k with hP
  have hsplit : ∀ v : View, opensAt index c sp j a i k v =
      (if v.1 = localIdx index then 1 else 0) *
        ∏ c', (fun c' (t : FieldVal) => if c' = c then (if P t then (1 : ℝ≥0∞) else 0) else 1) c' (v.2 c') := by
    intro v
    rw [Finset.prod_eq_single c (fun c' _ hc' => by simp only [if_neg hc']) (fun h => absurd (Finset.mem_univ c) h)]
    simp only [if_true, opensAt, hP]
    split_ifs <;> simp_all
  have hfield : freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0) ≤
      ((2 ^ 26 : ℕ) : ℝ≥0∞)⁻¹ * (2048 * 123 : ℕ) := by
    unfold freshAvg
    rw [Finset.card_univ]
    have hc : Fintype.card FieldVal = 2 ^ 26 := by simp [FieldVal, coordBits]
    rw [hc]
    refine mul_le_mul_right ?_ _
    rw [Finset.sum_boole]
    exact_mod_cast card_opens_le sp j a i k hk
  rw [show (Finset.univ : Finset View) = (Finset.univ : Finset (Fin (2 ^ subtreeHeight) × (Coord → FieldVal)))
    from rfl, H0Avg.freshAvg_prod]
  simp only [hsplit]
  have hinner : ∀ l : Fin (2 ^ subtreeHeight), (freshAvg (Finset.univ : Finset (Coord → FieldVal)) fun τ =>
      (if (l, τ).1 = localIdx index then (1 : ℝ≥0∞) else 0) *
        ∏ c', (fun c' (t : FieldVal) => if c' = c then (if P t then (1 : ℝ≥0∞) else 0) else 1) c' ((l, τ).2 c')) =
      (if l = localIdx index then 1 else 0) *
        freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0) := by
    intro l
    have hmul : ∀ (C : ℝ≥0∞) (G : (Coord → FieldVal) → ℝ≥0∞),
        freshAvg (Finset.univ : Finset (Coord → FieldVal)) (fun τ => C * G τ) =
          C * freshAvg (Finset.univ : Finset (Coord → FieldVal)) G := by
      intro C G
      unfold freshAvg
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    refine (hmul (if l = localIdx index then 1 else 0) (fun τ => ∏ c', (fun c' (t : FieldVal) =>
      if c' = c then (if P t then (1 : ℝ≥0∞) else 0) else 1) c' (τ c'))).trans ?_
    rw [H0Avg.freshAvg_pi_prod (fun c' (t : FieldVal) => if c' = c then (if P t then (1 : ℝ≥0∞) else 0) else 1)]
    congr 1
    rw [Finset.prod_eq_single c (fun c' _ hc' => by simp only [if_neg hc']; exact H0Avg.freshAvg_const' 1)
      (fun h => absurd (Finset.mem_univ c) h)]
    simp only [if_true]
  simp only [hinner]
  have hidx : freshAvg (Finset.univ : Finset (Fin (2 ^ subtreeHeight))) (fun l =>
      (if l = localIdx index then (1 : ℝ≥0∞) else 0) *
        freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0)) =
      ((2 ^ subtreeHeight : ℕ) : ℝ≥0∞)⁻¹ *
        freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0) := by
    unfold freshAvg
    rw [Finset.card_univ, Fintype.card_fin]
    congr 1
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (localIdx index), if_pos (Finset.mem_univ _)]
  rw [hidx]
  calc ((2 ^ subtreeHeight : ℕ) : ℝ≥0∞)⁻¹ *
        freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0)
      ≤ ((2 ^ subtreeHeight : ℕ) : ℝ≥0∞)⁻¹ * (((2 ^ 26 : ℕ) : ℝ≥0∞)⁻¹ * (2048 * 123 : ℕ)) :=
        mul_le_mul_right hfield _
    _ = revRate := by
        unfold revRate
        have h26 : ((2 ^ 26 : ℕ) : ℝ≥0∞) = ((2 ^ 15 : ℕ) : ℝ≥0∞) * 2048 := by norm_num
        rw [h26, ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num)), Nat.cast_mul, Nat.cast_mul,
          Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
        have h2048 : (2048 : ℝ≥0∞)⁻¹ * 2048 = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        rw [ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num))]
        calc ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * (((2 : ℝ≥0∞) ^ 15)⁻¹ * (2048 : ℝ≥0∞)⁻¹ * (2048 * 123))
            = 123 * (((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ 15)⁻¹) * ((2048 : ℝ≥0∞)⁻¹ * 2048) := by ring
          _ = _ := by rw [h2048, mul_one]

/-! ### One signing call -/

section Reveal

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) (parameter : PublicParameter) (data : PublicData)
  (m : Message)

/-- The probability that the scan from a uniform start signs with a cached landed pair of the
message: the mean over the starts of the walk value with payoff 1 at every cached landed pair and 0
elsewhere. -/
noncomputable def hitMass (s : State) (m : Message) : ℝ≥0∞ :=
  (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
    ∑ ρ, walk nextRand landing (stOf parameter data m s) (fun _ => 1) 0 0 digestAttemptLimit ρ

theorem hitMass_le_one (s : State) : hitMass parameter data s m ≤ 1 := by
  unfold hitMass
  have hcard : (Fintype.card Randomness : ℝ≥0∞)⁻¹ * (Fintype.card Randomness : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  calc _ ≤ (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ∑ _ρ : Randomness, (1 : ℝ≥0∞) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun ρ _ =>
          walk_le landing_le_one _ (fun _ => le_rfl) bot_le bot_le _ ρ)
    _ = 1 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]

/-- A walk paying 1 at the cached landed pairs and `x` at a fresh landing pays at most `x` plus the
walk of the cached landed pairs alone. -/
theorem walk_hit_split (st : Randomness → St) (x : ℝ≥0∞) (attempts : ℕ) (ρ : Randomness) :
    walk nextRand landing st (fun _ => 1) x 0 attempts ρ ≤
      x + walk nextRand landing st (fun _ => 1) 0 0 attempts ρ := by
  have h := walk_add (σ := nextRand) (p := landing) st (fun _ => 0) (fun _ => 1) x 0 0 0 attempts ρ
  simp only [zero_add, add_zero] at h
  rw [h]
  exact add_le_add (walk_le landing_le_one st (fun _ => bot_le) le_rfl bot_le attempts ρ) le_rfl

/-- A completed signing call that opens a chain selected a pair whose view opens it, fresh or cached. -/
theorem reveal_point (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    {s : State} (hprep : Prepared initial s)
    (attempts budget : ℕ) (start : Randomness) (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts start) budget s))
    (r : Option Signature) (hr : o1.1.1 = some r)
    (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (q : FPos)
    (hq : q.val ≤ k) (hrev : Coordinate.fchain index c sp j a i q ∈ o1.1.2.1) :
    1 ≤ freshNewWeight parameter data m s (opensAt index c sp j a i k) o1 +
      outWeight parameter data m s (fun _ => 0) (fun _ v => opensAt index c sp j a i k v) o1 := by
  have hpost := scan_post tg initial model parameter data m (fun ρ => hparse (m, ρ)) Finset.univ
    (fun _ _ _ _ _ _ _ _ => Finset.mem_univ _) attempts budget s start hprep o1 ho1 r hr
  rcases hpost with ⟨_, hnil, _⟩ | ⟨ρ, u0, hsel, hfts, hsig, hfl⟩
  · rw [hnil] at hrev
    cases hrev
  · obtain ⟨hi, hs, ha, hpos⟩ := hfts _ hrev index c sp j a i q rfl
    have hmarks := digestMarks_eq (truncateMessageDigest u0) c
    have hhit : opensAt index c sp j a i k (viewOf u0) = 1 := by
      unfold opensAt viewOf
      rw [if_pos]
      refine ⟨by rw [localDigestView_fst, hi], ?_, ?_, ?_⟩
      · rw [localDigestView_snd, ← hmarks, hs]
      · rw [localDigestView_snd, ← hmarks, ha]
      · rw [localDigestView_snd, ← hmarks]
        exact le_trans hpos hq
    rcases hsel.2.2.1 with hs0 | hs0
    · have h := freshNewWeight_ge hr hs0 hsel.1 hsel.2.1 (opensAt index c sp j a i k)
      rw [hhit] at h
      exact le_trans h le_self_add
    · rcases r with _ | sig
      · rw [(hfl rfl).1] at hrev
        cases hrev
      · have hρ := hsig sig rfl
        refine le_trans (le_of_eq ?_) le_add_self
        unfold outWeight
        rw [hr]
        simp only
        rw [hρ, hsel.1]
        simp only [Option.elim, pairWeight, hs0, reduceCtorEq, if_false]
        exact hhit.symm

/-- Every reveal of a run of the final assembly from a cached digest block is opened by its digest. -/
theorem finish_reveals_ok (ρ : Randomness) (b : ℕ) (s' : State) (u0 : HashOutput)
    (hparse : model.parse (blk parameter data m ρ) = none)
    (hc0 : s'.cache (blk parameter data m ρ) = some u0)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data m ρ) b s')) :
    ∀ c ∈ out.1.2.1, ForestOk (truncateMessageDigest u0) c := by
  rw [finishCostSource_eq, interp_ordinary] at hout
  split_ifs at hout with h1
  · rw [ordinaryStep, hparse] at hout
    simp only at hout
    rw [readOutside_cached _ s' u0 hc0, pure_bind, support_map] at hout
    obtain ⟨o, ho, rfl⟩ := hout
    exact interp_reveals tg initial model _ (revealsIn_finishRest parameter data m ρ _) _ _ o ho
  · rw [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    intro c hc
    cases hc

/-- **The scan from a start, every run.** The scan from a start, completed or not, reveals a given
chain at or below `k < 4` with probability at most the walk value paying the reveal rate at a fresh
landing and 1 at a cached landed pair of the message. -/
theorem reveal_scan_all (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    {s : State} (attempts : ℕ) (hA : attempts ≤ 2 ^ 128) (budget : ℕ) (start : Randomness)
    (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (hk : k < chainTop) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m attempts start) budget s] *
        (if ∃ q : FPos, q.val ≤ k ∧ Coordinate.fchain index c sp j a i q ∈ o1.1.2.1 then 1 else 0) ≤
      walk nextRand landing (stOf parameter data m s) (fun _ => 1) revRate 0 attempts start := by
  have hparse' : ∀ ρ, model.parse (blk parameter data m ρ) = none := fun ρ => hparse (m, ρ)
  set g : View → ℝ≥0∞ := opensAt index c sp j a i k with hgdef
  set gp : Randomness → View → ℝ≥0∞ := fun _ v => g v with hgp
  set V : List Coordinate → ℝ≥0∞ := fun L =>
    if ∃ q : FPos, q.val ≤ k ∧ Coordinate.fchain index c sp j a i q ∈ L then 1 else 0 with hV
  have hV0 : V [] = 0 := by
    simp only [hV]
    rw [if_neg]
    rintro ⟨q, _, h⟩
    cases h
  have hVfin : ∀ (ρ : Randomness) (s' : State) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data m s s' ρ → s'.cache (blk parameter data m ρ) = some u0 →
      Landed parameter (blockIndex u0) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data m ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data m s g gp ρ u0 := by
    intro ρ s' u0 b _ hc0 hl out hout
    simp only [hV]
    split_ifs with hrev
    swap
    · exact bot_le
    obtain ⟨q, hq, hmem⟩ := hrev
    obtain ⟨hi, hs, ha, hpos⟩ := finish_reveals_ok tg initial model parameter data m ρ b s' u0 (hparse' ρ) hc0 out
      hout _ hmem index c sp j a i q rfl
    have hmarks := digestMarks_eq (truncateMessageDigest u0) c
    have hhit : opensAt index c sp j a i k (viewOf u0) = 1 := by
      unfold opensAt viewOf
      rw [if_pos]
      refine ⟨by rw [localDigestView_fst, hi], ?_, ?_, ?_⟩
      · rw [localDigestView_snd, ← hmarks, hs]
      · rw [localDigestView_snd, ← hmarks, ha]
      · rw [localDigestView_snd, ← hmarks]
        exact le_trans hpos hq
    unfold pairWeight
    split_ifs
    · rw [hgdef, hhit]
    · simp only [hgp, hgdef, hhit, le_refl]
  have hbound := loop_boundV tg initial model parameter data m hparse' s g gp V hV0 hVfin attempts hA budget s start
    (fun _ => Or.inl rfl) (fun _ _ => rfl)
  have hpool : ∀ ρ, poolValue parameter data m s gp ρ ≤ 1 := by
    intro ρ
    unfold poolValue
    cases s.cache (blk parameter data m ρ) with
    | none => exact bot_le
    | some u0 =>
        simp only [Option.elim]
        split_ifs
        · exact opensAt_le_one index c sp j a i k _
        · exact bot_le
  exact le_trans hbound (walk_mono _ hpool (freshAvg_opensAt index c sp j a i k hk) le_rfl attempts start)

/-- **One signing call, every run.** A signing call, completed or not, reveals a given chain at or
below `k < 4` with probability at most the reveal rate plus the probability that the scan signs with
a cached landed pair of the message. -/
theorem reveal_le_all (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    {s : State} (budget : ℕ)
    (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (hk : k < chainTop) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSource parameter data m) budget s] *
        (if ∃ q : FPos, q.val ≤ k ∧ Coordinate.fchain index c sp j a i q ∈ o1.1.2.1 then 1 else 0) ≤
      revRate + hitMass parameter data s m := by
  set cinv := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hc
  have hcard : cinv * (Fintype.card Randomness : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  unfold signCostSource
  rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
  have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = cinv := by
    intro ρ
    rw [probOutput_uniformSample]
  simp only [hpr]
  rw [ENNReal.tsum_mul_left, tsum_fintype]
  calc _ ≤ cinv * ∑ start : Randomness, (revRate +
          walk nextRand landing (stOf parameter data m s) (fun _ => 1) 0 0 digestAttemptLimit start) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ =>
          le_trans (reveal_scan_all tg initial model parameter data m hparse digestAttemptLimit
            (by unfold digestAttemptLimit; norm_num) budget start index c sp j a i k hk)
            (walk_hit_split _ _ _ _))
    _ = revRate + hitMass parameter data s m := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add, ← mul_assoc, hcard,
          one_mul]
        rfl

/-- **One signing call** completes and opens a given chain at or below `k < 4` with probability at
most the reveal rate plus the probability that the scan signs with a cached landed pair of the
signed message. -/
theorem reveal_le (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    {s : State} (budget : ℕ)
    (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (hk : k < chainTop) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSource parameter data m) budget s] *
        (if o1.1.1.isSome ∧ ∃ q : FPos, q.val ≤ k ∧ Coordinate.fchain index c sp j a i q ∈ o1.1.2.1 then 1 else 0) ≤
      revRate + hitMass parameter data s m := by
  refine le_trans (ENNReal.tsum_le_tsum fun o1 => mul_le_mul' le_rfl ?_)
    (reveal_le_all tg initial model parameter data m hparse budget index c sp j a i k hk)
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd h1.2 h2
  · exact bot_le
  · exact le_rfl

end Reveal

end Sphincs.Security.ForsPotential
