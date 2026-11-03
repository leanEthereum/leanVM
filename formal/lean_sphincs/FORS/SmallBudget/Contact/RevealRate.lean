import FORS.SmallBudget.Contact.RunFacts
import FORS.SmallBudget.Contact.NearWitness
import FORS.ScanSigner.ScanReveals

/-! **One signing call opens a given FORS leaf rarely.** A fresh landed digest selects leaf `leaf` of
tree `κ` at the index of a given secret with probability `2^-b · 2^-a`: the digest picks the index
and the leaf of every tree uniformly. The cached landed pairs of the signed message add the
probability that the scan from a uniform start signs with one of them (`hitMass`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenBridge
open FORS.LoopWalk
open FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-! ### Hitting one leaf -/

/-- A kept view selects leaf `leaf` of tree `κ` at the index of `index`. -/
noncomputable def opensAt (index : Index) (κ : FTree) (leaf : FLeaf) (v : View) : ℝ≥0∞ :=
  if v.1 = localIdx index ∧ v.2 κ = leaf then 1 else 0

/-- The reveal rate `2^-b · 2^-a`. -/
noncomputable def revRate : ℝ≥0∞ := ((2 ^ subtreeHeight * 2 ^ forsHeight : ℕ) : ℝ≥0∞)⁻¹

theorem opensAt_le_one (index : Index) (κ : FTree) (leaf : FLeaf) (v : View) : opensAt index κ leaf v ≤ 1 := by
  unfold opensAt
  split_ifs <;> simp

/-- **A uniform kept view selects a given leaf with probability the reveal rate.** -/
theorem freshAvg_opensAt (index : Index) (κ : FTree) (leaf : FLeaf) :
    freshAvg Finset.univ (opensAt index κ leaf) ≤ revRate := by
  have hsplit : ∀ v : View, opensAt index κ leaf v =
      (if v.1 = localIdx index then 1 else 0) *
        ∏ κ', (fun κ' (t : FLeaf) => if κ' = κ then (if t = leaf then (1 : ℝ≥0∞) else 0) else 1) κ' (v.2 κ') := by
    intro v
    rw [Finset.prod_eq_single κ (fun κ' _ hκ' => by simp only [if_neg hκ']) (fun h => absurd (Finset.mem_univ κ) h)]
    simp only [if_true, opensAt]
    split_ifs <;> simp_all
  have hleaf : freshAvg (Finset.univ : Finset FLeaf) (fun t => if t = leaf then (1 : ℝ≥0∞) else 0) =
      ((2 ^ forsHeight : ℕ) : ℝ≥0∞)⁻¹ := by
    unfold freshAvg
    rw [Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq' Finset.univ leaf, if_pos (Finset.mem_univ _), mul_one]
  rw [show (Finset.univ : Finset View) = (Finset.univ : Finset (Fin (2 ^ subtreeHeight) × (FTree → FLeaf)))
    from rfl, H0Avg.freshAvg_prod]
  simp only [hsplit]
  have hmul : ∀ (C : ℝ≥0∞) (G : (FTree → FLeaf) → ℝ≥0∞),
      freshAvg (Finset.univ : Finset (FTree → FLeaf)) (fun τ => C * G τ) =
        C * freshAvg (Finset.univ : Finset (FTree → FLeaf)) G := by
    intro C G
    unfold freshAvg
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hinner : ∀ l : Fin (2 ^ subtreeHeight), (freshAvg (Finset.univ : Finset (FTree → FLeaf)) fun τ =>
      (if (l, τ).1 = localIdx index then (1 : ℝ≥0∞) else 0) *
        ∏ κ', (fun κ' (t : FLeaf) => if κ' = κ then (if t = leaf then (1 : ℝ≥0∞) else 0) else 1) κ' ((l, τ).2 κ')) =
      (if l = localIdx index then 1 else 0) * ((2 ^ forsHeight : ℕ) : ℝ≥0∞)⁻¹ := by
    intro l
    refine (hmul (if l = localIdx index then 1 else 0) (fun τ => ∏ κ', (fun κ' (t : FLeaf) =>
      if κ' = κ then (if t = leaf then (1 : ℝ≥0∞) else 0) else 1) κ' (τ κ'))).trans ?_
    rw [H0Avg.freshAvg_pi_prod (fun κ' (t : FLeaf) => if κ' = κ then (if t = leaf then (1 : ℝ≥0∞) else 0) else 1)]
    congr 1
    rw [Finset.prod_eq_single κ (fun κ' _ hκ' => by simp only [if_neg hκ']; exact H0Avg.freshAvg_const' 1)
      (fun h => absurd (Finset.mem_univ κ) h)]
    simp only [if_true]
    exact hleaf
  simp only [hinner]
  unfold freshAvg revRate
  rw [Finset.card_univ, Fintype.card_fin]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (localIdx index), if_pos (Finset.mem_univ _), Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp))]

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
    ∑ ρ, walk (nextRand (data.steps m)) landing (stOf parameter data m s) (fun _ => 1) 0 0 digestAttemptLimit ρ

/-- A walk paying 1 at the cached landed pairs and `x` at a fresh landing pays at most `x` plus the
walk of the cached landed pairs alone. -/
theorem walk_hit_split (half : Randomness) (st : Randomness → St) (x : ℝ≥0∞) (attempts : ℕ) (ρ : Randomness) :
    walk (nextRand half) landing st (fun _ => 1) x 0 attempts ρ ≤
      x + walk (nextRand half) landing st (fun _ => 1) 0 0 attempts ρ := by
  have h := walk_add (σ := (nextRand half)) (p := landing) st (fun _ => 0) (fun _ => 1) x 0 0 0 attempts ρ
  simp only [zero_add, add_zero] at h
  rw [h]
  exact add_le_add (walk_le landing_le_one st (fun _ => bot_le) le_rfl bot_le attempts ρ) le_rfl

/-- **Reads of cached inputs keep the reveals**: a run that stops inside them reveals nothing, and
any other run reveals what a run of the continuation at the cached values reveals. -/
theorem cached_reads_reveals {α : Type} : ∀ {n : ℕ} (x : Fin n → HashInput) (w : Fin n → HashOutput)
    (state : State), (∀ i, model.parse (x i) = none) → (∀ i, state.cache (x i) = some (w i)) →
    ∀ (rest : (Fin n → HashOutput) → OracleComp CostSpec α) (budget : ℕ)
      (out : Run HashInput Coordinate α × State),
      out ∈ support (interp tg initial model (Concrete.sequenceFin (fun i =>
        (liftM (CostSpec.query (.inl (.inr (.inl (x i))))) : OracleComp CostSpec HashOutput)) >>= rest)
        budget state) →
      out.1.2.1 = [] ∨ ∃ b o, o ∈ support (interp tg initial model (rest w) b state) ∧
        out.1.2.1 = o.1.2.1
  | 0, _, w, state, _, _, rest, budget, out, hout => by
      rw [Concrete.sequenceFin, pure_bind] at hout
      refine Or.inr ⟨budget, out, ?_, rfl⟩
      rwa [show w = Fin.elim0 from funext fun i => i.elim0]
  | n + 1, x, w, state, hp, hc, rest, budget, out, hout => by
      have hstep : (Concrete.sequenceFin (fun i =>
          (liftM (CostSpec.query (.inl (.inr (.inl (x i))))) : OracleComp CostSpec HashOutput)) >>= rest) =
          liftM (CostSpec.query (.inl (.inr (.inl (x 0))))) >>= fun head =>
            (Concrete.sequenceFin fun i : Fin n =>
              (liftM (CostSpec.query (.inl (.inr (.inl (x i.succ))))) : OracleComp CostSpec HashOutput)) >>=
              fun values => rest (Fin.cons head values) := by
        rw [Concrete.sequenceFin]
        simp only [bind_assoc, pure_bind]
        rfl
      rw [hstep, interp_ordinary] at hout
      split_ifs at hout with hbudget
      · rw [ordinaryStep, hp 0] at hout
        simp only at hout
        rw [readOutside_cached _ state (w 0) (hc 0), pure_bind, support_map] at hout
        obtain ⟨o1, ho1, rfl⟩ := hout
        rcases cached_reads_reveals (Fin.tail x) (Fin.tail w) state (fun i => hp i.succ)
          (fun i => hc i.succ) (fun values => rest (Fin.cons (w 0) values)) (budget - 1) o1 ho1 with
          h | ⟨b, o, ho, heq⟩
        · exact Or.inl h
        · rw [Fin.cons_self_tail] at ho
          exact Or.inr ⟨b, o, ho, heq⟩
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact Or.inl rfl

/-- Every reveal of a run of the final assembly from a wholly cached pair is opened by the digest of
that pair. -/
theorem finish_reveals_ok (ρ : Randomness) (b : ℕ) (s' : State) (u : DigestCall → HashOutput)
    (hparse : ∀ call, model.parse (pblk parameter data (m, ρ) call) = none)
    (hc : ∀ call, s'.cache (pblk parameter data (m, ρ) call) = some (u call))
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data m ρ) b s')) :
    ∀ c ∈ out.1.2.1, ForsOk (truncateMessageDigest u) c := by
  rw [finishCostSource_eq] at hout
  rcases cached_reads_reveals tg initial model (pblk parameter data (m, ρ)) u s' hparse hc _ b out hout with
    h | ⟨b', o, ho, heq⟩
  · intro c hcmem
    rw [h] at hcmem
    cases hcmem
  · intro c hcmem
    rw [heq] at hcmem
    exact interp_reveals tg initial model _ (revealsIn_finishRest parameter data m ρ _) b' s' o ho c hcmem

/-- **The scan from a start, every run.** The scan from a start, completed or not, reveals a given
FORS leaf with probability at most the walk value paying the reveal rate at a fresh
landing and 1 at a cached landed pair of the message. -/
theorem reveal_scan_all (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    {s : State} (hpi : PairInv parameter data m s) (attempts : ℕ) (hA : attempts ≤ 2 ^ 128) (budget : ℕ)
    (start : Randomness) (index : Index) (κ : FTree) (leaf : FLeaf) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m (data.step m) attempts start) budget s] *
        (if ∃ q, Coordinate.fors index κ leaf q ∈ o1.1.2.1 then 1 else 0) ≤
      walk (nextRand (data.steps m)) landing (stOf parameter data m s) (fun _ => 1) revRate 0 attempts start := by
  have hparse' : ∀ ρ call, model.parse (pblk parameter data (m, ρ) call) = none := fun ρ => hparse (m, ρ)
  have hkind' : ∀ ρ call, tg.kind (pblk parameter data (m, ρ) call) = .none := fun ρ => hkind (m, ρ)
  set g : View → ℝ≥0∞ := opensAt index κ leaf with hgdef
  set gp : Randomness → View → ℝ≥0∞ := fun _ v => g v with hgp
  set V : List Coordinate → ℝ≥0∞ := fun L =>
    if ∃ q, Coordinate.fors index κ leaf q ∈ L then 1 else 0 with hV
  have hV0 : V [] = 0 := by
    simp only [hV]
    rw [if_neg]
    rintro ⟨q, h⟩
    cases h
  have hVfin : ∀ (ρ : Randomness) (s' : State) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data m s s' ρ →
      (∀ call, s'.cache (pblk parameter data (m, ρ) call) = some (u call)) →
      Landed parameter (blockIndex (u firstCall)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data m ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data m s g gp ρ u := by
    intro ρ s' u b _ hc hl out hout
    simp only [hV]
    split_ifs with hrev
    swap
    · exact bot_le
    obtain ⟨q, hmem⟩ := hrev
    obtain ⟨hi, hleaf⟩ := finish_reveals_ok tg initial model parameter data m ρ b s' u (hparse' ρ) hc out
      hout _ hmem index κ leaf q rfl
    have hhit : opensAt index κ leaf (viewOf u) = 1 := by
      unfold opensAt viewOf
      rw [if_pos]
      exact ⟨by rw [localDigestView_fst, hi], by rw [localDigestView_snd, hleaf]⟩
    unfold pairWeight
    split_ifs
    · rw [hgdef, hhit]
    · simp only [hgp, hgdef, hhit, le_refl]
  have hbound := loop_boundV tg initial model parameter data m hparse' hkind' s g gp V hV0 hVfin attempts hA
    budget s start (fun _ => Or.inl rfl) hpi (fun _ _ _ => rfl)
  have hpool : ∀ ρ, poolValue parameter data m s gp ρ ≤ 1 := by
    intro ρ
    unfold poolValue
    cases pcache parameter data m s ρ with
    | none => exact bot_le
    | some u =>
        simp only [Option.elim]
        split_ifs
        · exact opensAt_le_one index κ leaf _
        · exact bot_le
  exact le_trans hbound (walk_mono _ hpool (freshAvg_opensAt index κ leaf) le_rfl attempts start)

/-- **One signing call, every run.** A signing call, completed or not, reveals a given FORS leaf
with probability at most the reveal rate plus the probability that the scan signs with
a cached landed pair of the message. -/
theorem reveal_le_all (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    {s : State} (hpi : PairInv parameter data m s) (budget : ℕ)
    (index : Index) (κ : FTree) (leaf : FLeaf) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSource parameter data m) budget s] *
        (if ∃ q, Coordinate.fors index κ leaf q ∈ o1.1.2.1 then 1 else 0) ≤
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
          walk (nextRand (data.steps m)) landing (stOf parameter data m s) (fun _ => 1) 0 0 digestAttemptLimit start) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ =>
          le_trans (reveal_scan_all tg initial model parameter data m hparse hkind hpi digestAttemptLimit
            (by unfold digestAttemptLimit; norm_num) budget start index κ leaf)
            (walk_hit_split _ _ _ _ _))
    _ = revRate + hitMass parameter data s m := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add, ← mul_assoc, hcard,
          one_mul]
        rfl

end Reveal

end FORS.Security.ForsPotential
