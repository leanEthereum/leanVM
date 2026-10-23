import Sphincs.BridgeScan
import Sphincs.BridgeForsPotential

/-! The groups of the unsigned messages in the virtual future of the scan signer. Every message with
cached digests acts on a base function by its group operator (`LoopWalk.grp`, over the randomizers
of the message, the statuses read from the cache); the virtual future of a term is the groups of the
live messages applied to the one-coin virtual future of the future pairs. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner
  SphincsFors.Security.Domination Sphincs.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

instance : Nonempty Randomness := ⟨0⟩

section Defs

variable (parameter : PublicParameter) (data : PublicData)

/-- What a cached landed pair discloses when it is signed: its view, or nothing for an excluded
pair (a candidate does not count its own signature). -/
noncomputable def extOf (s : State) (excl : Pair → Prop) (m : Message) (ρ : Randomness) : Multiset View :=
  if excl (m, ρ) then 0 else {pview parameter data s (m, ρ)}

/-- **The group of a message.** -/
noncomputable def grpM (s : State) (excl : Pair → Prop) (m : Message) (F : Multiset View → ℝ≥0∞)
    (d : Multiset View) : ℝ≥0∞ :=
  grp nextRand landing digestAttemptLimit Finset.univ (stOf parameter data m s) (extOf parameter data s excl m) F d

/-- The groups of a list of messages. -/
noncomputable def grpAll (s : State) (excl : Pair → Prop) : List Message → (Multiset View → ℝ≥0∞) →
    Multiset View → ℝ≥0∞
  | [], F => F
  | m :: Ms, F => grpM parameter data s excl m (grpAll s excl Ms F)

/-- The mass that the group of a message leaves on the identity. -/
noncomputable def idMassM (s : State) (m : Message) : ℝ≥0∞ :=
  idMass nextRand landing digestAttemptLimit (stOf parameter data m s)

end Defs

section Basic

variable {parameter : PublicParameter} {data : PublicData}

theorem grpAll_le_of_le (s : State) (excl : Pair → Prop) {F G : Multiset View → ℝ≥0∞} (h : ∀ e, F e ≤ G e) :
    ∀ (Ms : List Message) (d : Multiset View), grpAll parameter data s excl Ms F d ≤ grpAll parameter data s excl Ms G d
  | [], d => h d
  | _ :: Ms, d => grp_le_of_le _ _ (grpAll_le_of_le s excl h Ms) d

theorem grpAll_congr (s : State) (excl : Pair → Prop) {F G : Multiset View → ℝ≥0∞} (h : ∀ e, F e = G e)
    (Ms : List Message) (d : Multiset View) : grpAll parameter data s excl Ms F d = grpAll parameter data s excl Ms G d :=
  le_antisymm (grpAll_le_of_le s excl (fun e => (h e).le) Ms d) (grpAll_le_of_le s excl (fun e => (h e).ge) Ms d)

theorem grpAll_add (s : State) (excl : Pair → Prop) (F G : Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message) (d : Multiset View), grpAll parameter data s excl Ms (fun e => F e + G e) d =
      grpAll parameter data s excl Ms F d + grpAll parameter data s excl Ms G d
  | [], _ => rfl
  | m :: Ms, d => by
      simp only [grpAll, grpM]
      rw [grp_congr _ _ (fun e => grpAll_add s excl F G Ms e), grp_add]

theorem grpAll_const_mul (s : State) (excl : Pair → Prop) (c : ℝ≥0∞) (F : Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message) (d : Multiset View), grpAll parameter data s excl Ms (fun e => c * F e) d =
      c * grpAll parameter data s excl Ms F d
  | [], _ => rfl
  | m :: Ms, d => by
      simp only [grpAll, grpM]
      rw [grp_congr _ _ (fun e => grpAll_const_mul s excl c F Ms e), grp_const_mul]

theorem grpAll_const (s : State) (excl : Pair → Prop) (c : ℝ≥0∞) :
    ∀ (Ms : List Message) (d : Multiset View), grpAll parameter data s excl Ms (fun _ => c) d = c
  | [], _ => rfl
  | m :: Ms, d => by
      simp only [grpAll, grpM]
      rw [grp_congr _ _ (fun e => grpAll_const s excl c Ms e), grp_const landing_le_one Finset.univ_nonempty]

theorem grpAll_shift (s : State) (excl : Pair → Prop) (F : Multiset View → ℝ≥0∞) (x : Multiset View) :
    ∀ (Ms : List Message) (d : Multiset View), grpAll parameter data s excl Ms (fun e => F (e + x)) d =
      grpAll parameter data s excl Ms F (d + x)
  | [], _ => rfl
  | m :: Ms, d => by
      simp only [grpAll, grpM]
      rw [grp_congr _ _ (fun e => grpAll_shift s excl F x Ms e), grp_shift]

theorem grpAll_freshAvg {W : Type} [DecidableEq W] (T : Finset W) (s : State) (excl : Pair → Prop)
    (h : W → Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message) (d : Multiset View),
      grpAll parameter data s excl Ms (fun e => freshAvg T fun t => h t e) d =
        freshAvg T (fun t => grpAll parameter data s excl Ms (h t) d)
  | [], _ => rfl
  | m :: Ms, d => by
      simp only [grpAll, grpM]
      rw [grp_congr _ _ (fun e => grpAll_freshAvg T s excl h Ms e), grp_freshAvg]

theorem grpAll_mono (s : State) (excl : Pair → Prop) {F : Multiset View → ℝ≥0∞} (hF : Monotone' F) :
    ∀ Ms : List Message, Monotone' (grpAll parameter data s excl Ms F)
  | [] => hF
  | _ :: Ms => grp_mono _ _ (grpAll_mono s excl hF Ms)

theorem grpAll_ne_top (s : State) (excl : Pair → Prop) {F : Multiset View → ℝ≥0∞} (hF : ∀ e, F e ≠ ⊤) :
    ∀ (Ms : List Message) (d : Multiset View), grpAll parameter data s excl Ms F d ≠ ⊤
  | [], d => hF d
  | _ :: Ms, d => grp_ne_top landing_le_one Finset.univ_nonempty _ _ (grpAll_ne_top s excl hF Ms) d

theorem le_grpAll (s : State) (excl : Pair → Prop) {F : Multiset View → ℝ≥0∞} (hF : Monotone' F) :
    ∀ (Ms : List Message) (d : Multiset View), F d ≤ grpAll parameter data s excl Ms F d
  | [], _ => le_rfl
  | _ :: Ms, d => le_trans (le_grpAll s excl hF Ms d)
      (le_grp landing_le_one Finset.univ_nonempty _ _ (grpAll_mono s excl hF Ms) d)

/-- The group of a message commutes with the groups of a list. -/
theorem grpM_grpAll (s : State) (excl : Pair → Prop) (m : Message) (F : Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message) (d : Multiset View),
      grpM parameter data s excl m (grpAll parameter data s excl Ms F) d =
        grpAll parameter data s excl Ms (grpM parameter data s excl m F) d
  | [], _ => rfl
  | m' :: Ms, d => by
      have h1 : grpM parameter data s excl m (grpM parameter data s excl m' (grpAll parameter data s excl Ms F)) d =
          grpM parameter data s excl m' (grpM parameter data s excl m (grpAll parameter data s excl Ms F)) d :=
        grp_comm nextRand digestAttemptLimit _ _ _ _ _ d
      exact h1.trans (grp_congr _ _ (fun e => grpM_grpAll s excl m F Ms e) d)

/-- The groups do not depend on the order of the messages. -/
theorem grpAll_perm (s : State) (excl : Pair → Prop) (F : Multiset View → ℝ≥0∞) {Ms Ms' : List Message}
    (h : Ms.Perm Ms') : ∀ d, grpAll parameter data s excl Ms F d = grpAll parameter data s excl Ms' F d := by
  induction h with
  | nil => intro d; rfl
  | cons m _ ih =>
      intro d
      simp only [grpAll, grpM]
      exact grp_congr _ _ ih d
  | swap a b l =>
      intro d
      exact grp_comm nextRand digestAttemptLimit _ _ _ _ _ d
  | trans _ _ ih1 ih2 => intro d; rw [ih1, ih2]

/-- A message without cached digest has the identity as its group. -/
theorem grpM_untouched (s : State) (excl : Pair → Prop) (m : Message)
    (h : ∀ ρ, s.cache (blk parameter data m ρ) = none) (F : Multiset View → ℝ≥0∞) (d : Multiset View) :
    grpM parameter data s excl m F d = F d := by
  unfold grpM
  refine grp_fresh landing_le_one _ (fun ρ => ?_) _ F d
  simp [stOf, h ρ]

end Basic

/-! ### One digest query on a new pair -/

section Probe

variable {parameter : PublicParameter} {data : PublicData}

theorem stOf_withPair_self (s : State) (p : Pair) (u0 : HashOutput) :
    stOf parameter data p.1 (withPair parameter data s p u0) =
      Function.update (stOf parameter data p.1 s) p.2 (if Landed parameter (blockIndex u0) then .hit else .miss) := by
  funext ρ
  by_cases hρ : ρ = p.2
  · subst hρ
    rw [Function.update_self]
    have h : (withPair parameter data s p u0).cache (blk parameter data p.1 p.2) = some u0 := withPair_self s p u0
    simp only [stOf, h, Option.elim]
  · rw [Function.update_of_ne hρ]
    have hne : (p.1, ρ) ≠ p := fun h => hρ (congrArg Prod.snd h)
    have h : (withPair parameter data s p u0).cache (blk parameter data p.1 ρ) = s.cache (blk parameter data p.1 ρ) :=
      withPair_other_pair s p (p.1, ρ) hne u0
    simp only [stOf, h]

theorem stOf_withPair_other (s : State) (p : Pair) (u0 : HashOutput) {m : Message} (hm : m ≠ p.1) :
    stOf parameter data m (withPair parameter data s p u0) = stOf parameter data m s := by
  funext ρ
  have hne : (m, ρ) ≠ p := fun h => hm (congrArg Prod.fst h)
  have h : (withPair parameter data s p u0).cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ) :=
    withPair_other_pair s p (m, ρ) hne u0
  simp only [stOf, h]

theorem extOf_withPair_other (s : State) (p : Pair) (u0 : HashOutput) (excl : Pair → Prop) {m : Message} {ρ : Randomness}
    (hne : (m, ρ) ≠ p) :
    extOf parameter data (withPair parameter data s p u0) excl m ρ = extOf parameter data s excl m ρ := by
  unfold extOf
  rw [pview_withPair_other s p (m, ρ) hne u0]

theorem grpM_withPair_other (s : State) (p : Pair) (u0 : HashOutput) (excl : Pair → Prop) {m : Message}
    (hm : m ≠ p.1) (F : Multiset View → ℝ≥0∞) (d : Multiset View) :
    grpM parameter data (withPair parameter data s p u0) excl m F d = grpM parameter data s excl m F d := by
  unfold grpM
  rw [stOf_withPair_other s p u0 hm]
  exact grp_congr_ext _ (fun ρ _ => extOf_withPair_other s p u0 excl fun h => hm (congrArg Prod.fst h)) F d

theorem grpAll_withPair_other (s : State) (p : Pair) (u0 : HashOutput) (excl : Pair → Prop)
    (F : Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message), p.1 ∉ Ms → ∀ d,
      grpAll parameter data (withPair parameter data s p u0) excl Ms F d = grpAll parameter data s excl Ms F d
  | [], _, _ => rfl
  | m :: Ms, hm, d => by
      have hm1 : m ≠ p.1 := fun h => hm (h ▸ List.mem_cons_self ..)
      have hm2 : p.1 ∉ Ms := fun h => hm (List.mem_cons_of_mem _ h)
      simp only [grpAll]
      rw [grpM_withPair_other s p u0 excl hm1]
      exact grp_congr _ _ (fun e => grpAll_withPair_other s p u0 excl F Ms hm2 e) d

theorem grpM_withPair_self (s : State) (p : Pair) (u0 : HashOutput) (excl : Pair → Prop)
    (F : Multiset View → ℝ≥0∞) (d : Multiset View) :
    grpM parameter data (withPair parameter data s p u0) excl p.1 F d =
      grp nextRand landing digestAttemptLimit Finset.univ
        (Function.update (stOf parameter data p.1 s) p.2 (if Landed parameter (blockIndex u0) then .hit else .miss))
        (Function.update (extOf parameter data s excl p.1) p.2 (if excl p then 0 else {viewOf u0})) F d := by
  unfold grpM
  rw [stOf_withPair_self]
  congr 1
  funext ρ
  by_cases hρ : ρ = p.2
  · subst hρ
    rw [Function.update_self]
    unfold extOf
    rw [show ((p.1, p.2) : Pair) = p from rfl, pview_withPair_self]
  · rw [Function.update_of_ne hρ]
    exact extOf_withPair_other s p u0 excl fun h => hρ (congrArg Prod.snd h)

/-- One more future pair in front of the future. -/
theorem creations_one {U : Finset View} {land : ℝ≥0∞} (G : List View → ℝ≥0∞) :
    ∀ k J, creations U land (fun I => (1 - land) * G I + land * freshAvg U fun v => G (v :: I)) k J =
      creations U land G (k + 1) J
  | 0, _ => rfl
  | k + 1, J => by
      have h : (fun v => creations U land (fun I => (1 - land) * G I + land * freshAvg U fun v => G (v :: I)) k (v :: J)) =
          fun v => creations U land G (k + 1) (v :: J) := funext fun v => creations_one G k (v :: J)
      rw [creations, creations_one G k J, h]
      rfl

/-- **One digest query, one term.** The block of a new pair of a listed message is read: in the mean
the groups applied to the virtual future are paid by one more future pair, provided the coin `w`
pays `(2 − landing)/2^128` through the mass that the group of the message leaves on the identity. -/
theorem grpAll_probe {w : ℝ≥0∞} (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : Monotone' f) (hfin : ∀ D, f D ≠ ⊤)
    (s : State) (p : Pair) (hp0 : s.cache (pblk parameter data p) = none) (excl : Pair → Prop)
    (Ms : List Message) (hMs : Ms.Nodup) (hp : p.1 ∈ Ms)
    (hrate : (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ((1 - landing) + 1) ≤ landing * w * idMassM parameter data s p.1)
    (n : ℕ) (I : List View) (d : Multiset View) :
    pairE (fun u0 => grpAll parameter data (withPair parameter data s p u0) excl Ms
        (virtualOnce Finset.univ w f n I) d) ≤
      (1 - landing) * grpAll parameter data s excl Ms (virtualOnce Finset.univ w f n I) d +
        landing * freshAvg Finset.univ (fun v => grpAll parameter data s excl Ms
          (virtualOnce Finset.univ w f n (v :: I)) d) := by
  set Ms' := Ms.erase p.1 with hMs'
  have hperm : Ms.Perm (p.1 :: Ms') := List.perm_cons_erase hp
  have hnot : p.1 ∉ Ms' := fun h => (List.Nodup.mem_erase_iff hMs).1 h |>.1 rfl
  set X : Multiset View → ℝ≥0∞ := grpAll parameter data s excl Ms' (virtualOnce Finset.univ w f n I) with hX
  have hXmono : Monotone' X := grpAll_mono s excl (virtualOnce_mono hf n I) Ms'
  have hXfin : ∀ e, X e ≠ ⊤ :=
    grpAll_ne_top s excl (virtualOnce_ne_top Finset.univ_nonempty hw hfin n I) Ms'
  have hst : stOf parameter data p.1 s p.2 = .fresh := by
    have h : s.cache (blk parameter data p.1 p.2) = none := hp0
    simp [stOf, h]
  -- the left-hand side through the group of the message
  set Fh : View → ℝ≥0∞ := fun v => grp nextRand landing digestAttemptLimit Finset.univ
    (Function.update (stOf parameter data p.1 s) p.2 .hit)
    (Function.update (extOf parameter data s excl p.1) p.2 (if excl p then 0 else {v})) X d with hFh
  set Cm : ℝ≥0∞ := grp nextRand landing digestAttemptLimit Finset.univ
    (Function.update (stOf parameter data p.1 s) p.2 .miss) (extOf parameter data s excl p.1) X d with hCm
  have hleft : ∀ u0, grpAll parameter data (withPair parameter data s p u0) excl Ms
      (virtualOnce Finset.univ w f n I) d =
      if Landed parameter (blockIndex u0) then Fh (viewOf u0) else Cm := by
    intro u0
    rw [grpAll_perm _ excl _ hperm d]
    simp only [grpAll]
    rw [grpM_withPair_self,
      grp_congr _ _ (fun e => grpAll_withPair_other s p u0 excl (virtualOnce Finset.univ w f n I) Ms' hnot e) d]
    by_cases hl : Landed parameter (blockIndex u0)
    · simp only [hl, ite_true]
      rfl
    · simp only [hl, ite_false]
      exact grp_congr_ext _ (fun ρ hρ => by
        by_cases h : ρ = p.2
        · subst h; rw [Function.update_self] at hρ; cases hρ
        · rw [Function.update_of_ne h]) X d
  rw [show (fun u0 => grpAll parameter data (withPair parameter data s p u0) excl Ms
      (virtualOnce Finset.univ w f n I) d) = fun u0 => if Landed parameter (blockIndex u0) then Fh (viewOf u0) else Cm
      from funext hleft, pairE_landed parameter Fh Cm]
  have hstep := probe_step (σ := nextRand) (p := landing) (A := digestAttemptLimit) (U := (Finset.univ : Finset View))
    landing_le_one Finset.univ_nonempty (stOf parameter data p.1 s) (extOf parameter data s excl p.1) hXmono hXfin d
    p.2 hst (fun j h0 hj => nextRand_pow_ne p.2 j h0 (lt_trans hj (by unfold digestAttemptLimit; norm_num))) w hw
    (fun v => if excl p then 0 else {v}) (fun v => by split_ifs <;> simp) hrate
  refine le_trans hstep (le_of_eq ?_)
  -- the right-hand side through the group of the message
  have hcoin : ∀ (v : View) (e : Multiset View), virtualOnce Finset.univ w f n (v :: I) e =
      w * virtualOnce Finset.univ w f n I (e + {v}) + (1 - w) * virtualOnce Finset.univ w f n I e := fun _ _ => rfl
  have hXv : ∀ (v : View) (e : Multiset View), grpAll parameter data s excl Ms' (virtualOnce Finset.univ w f n (v :: I)) e =
      w * X (e + {v}) + (1 - w) * X e := by
    intro v e
    rw [grpAll_congr s excl (hcoin v) Ms' e,
      grpAll_add s excl (fun e => w * virtualOnce Finset.univ w f n I (e + {v})), grpAll_const_mul, grpAll_const_mul,
      grpAll_shift]
  have hR1 : grpAll parameter data s excl Ms (virtualOnce Finset.univ w f n I) d = grpM parameter data s excl p.1 X d := by
    rw [grpAll_perm _ excl _ hperm d]; rfl
  have hR2 : ∀ v, grpAll parameter data s excl Ms (virtualOnce Finset.univ w f n (v :: I)) d =
      grpM parameter data s excl p.1 (fun e => w * X (e + {v}) + (1 - w) * X e) d := by
    intro v
    rw [grpAll_perm _ excl _ hperm d]
    simp only [grpAll]
    exact grp_congr _ _ (hXv v) d
  rw [hR1, show (fun v => grpAll parameter data s excl Ms (virtualOnce Finset.univ w f n (v :: I)) d) = _ from funext hR2]
  unfold grpM
  rw [grp_add _ _ (fun e => (1 - landing) * X e), grp_const_mul, grp_const_mul, grp_freshAvg]

end Probe

/-! ### One signing call -/

section SignScan

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (m : Message)

/-- **The scan from a start, with the fresh pair it completes.** -/
theorem scan_bound_comb
    (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none) (s : State)
    (gf : View → ℝ≥0∞) (gp : Randomness → View → ℝ≥0∞) (attempts : ℕ) (hA : attempts ≤ 2 ^ 128)
    (budget : ℕ) (start : Randomness) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSourceLoop parameter data m attempts start) budget s}[x = out] *
        (freshNewWeight parameter data m s gf out + outWeight parameter data m s 0 gp out) ≤
      walk nextRand landing (stOf parameter data m s) (poolValue parameter data m s gp)
        (freshAvg Finset.univ gf) 0 attempts start := by
  refine scan_boundW tg initial model parameter data m hparse s gf gp
    (fun r s' => freshNewWeight parameter data m s gf ((r, [], [], []), s') +
      outWeight parameter data m s 0 gp ((r, [], [], []), s'))
    (fun _ => by simp [freshNewWeight, outWeight]) ?_ ?_ attempts hA budget s start (fun _ => Or.inl rfl)
    (fun _ _ => rfl)
  · intro s' hrel
    simp only [freshNewWeight, outWeight, Option.isSome_some, ite_true, add_zero]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    split_ifs with hn
    · rcases hrel ρ with h | ⟨_, u, hu', hnl⟩
      · rw [h, hn]; rfl
      · simp only [hu', Option.elim, ite_eq_right hnl]
    · rfl
  · intro ρ s' u0 b hoff hs0 out hout
    have hkeep := finish_keeps_msg tg initial model parameter data m hparse ρ b s' u0 hs0 out hout
    have hk : ∀ ρ', out.2.cache (blk parameter data m ρ') = s'.cache (blk parameter data m ρ') :=
      fun ρ' => hkeep _ (msgInput_digestInput parameter data.root m ρ')
    show freshNewWeight parameter data m s gf ((out.1.1, [], [], []), out.2) +
      outWeight parameter data m s 0 gp ((out.1.1, [], [], []), out.2) ≤ _
    by_cases hsome : out.1.1.isSome
    · rw [ite_eq_left hsome, hk ρ, hs0]
      simp only [Option.elim]
      have hfresh : freshNewWeight parameter data m s gf ((out.1.1, [], [], []), out.2) =
          if s.cache (blk parameter data m ρ) = none then
            (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0) else 0 := by
        simp only [freshNewWeight, ite_eq_left hsome]
        rw [Finset.sum_eq_single ρ]
        · simp only [hk ρ, hs0, Option.elim]
        · intro ρ' _ hne
          split_ifs with hn
          · rcases hoff ρ' hne with h | ⟨_, u, hu', hnl⟩
            · rw [hk ρ', h, hn]; rfl
            · simp only [hk ρ', hu', Option.elim, ite_eq_right hnl]
          · rfl
        · intro h; exact absurd (Finset.mem_univ ρ) h
      rw [hfresh]
      have hout' : outWeight parameter data m s 0 gp ((out.1.1, [], [], []), out.2) ≤
          if s.cache (blk parameter data m ρ) = none then 0 else gp ρ (viewOf u0) := by
        have := outWeight_finish_le tg initial model parameter data m s 0 gp ρ b s' out hout
        simp only [ite_eq_left hsome, hk ρ, hs0, Option.elim, pairWeight] at this
        refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_))
        · rfl
        · split_ifs <;> rfl
      refine le_trans (add_le_add_right hout' _) (le_of_eq ?_)
      simp only [pairWeight]
      split_ifs <;> simp [-SampleableType.prEvent_uniformSample]
    · rw [ite_eq_right hsome]
      simp only [freshNewWeight, ite_eq_right hsome, zero_add]
      unfold outWeight
      cases hr : out.1.1 with
      | none => rfl
      | some r => simp [hr] at hsome

variable {parameter data m}

/-- **Pointwise upper value of a signing outcome** for a monotone function of the disclosures. -/
theorem upper_pointX {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) {s : State} (d : Multiset View)
    (excl : Pair → Prop) (out : Run HashInput Coordinate (Option Signature) × State)
    (r : Option Signature) (hres : out.1.1 = some r) (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (shape : (newRand parameter data m s out.2 = ∅ ∧ poolDisc parameter data m s out = 0) ∨
      (∃ ρ u0, newRand parameter data m s out.2 = {ρ} ∧ poolDisc parameter data m s out = 0 ∧
        out.2.cache (blk parameter data m ρ) = some u0 ∧ Landed parameter (blockIndex u0) ∧
        s.cache (blk parameter data m ρ) = none ∧
        (∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s out.2 ρ') ∧
        (r = none → (viewOf u0).1 ∈ Fail) ∧ (∀ sig, r = some sig → sig.randomness = ρ)) ∨
      (∃ ρ u0 sig, newRand parameter data m s out.2 = ∅ ∧ poolDisc parameter data m s out = {viewOf u0} ∧
        r = some sig ∧ sig.randomness = ρ ∧ s.cache (blk parameter data m ρ) = some u0 ∧
        out.2.cache (blk parameter data m ρ) = some u0))
    (hex : ∀ sig, r = some sig → s.cache (blk parameter data m sig.randomness) ≠ none → ¬excl (m, sig.randomness)) :
    X (discAfter parameter data m s d out) ≤
      X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
        outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out) := by
  unfold discAfter newPairs
  rcases shape with ⟨hnew, hpool⟩ | ⟨ρ, u0, hnew, hpool, h0, hl, hs0, hothers, _, _⟩ |
      ⟨ρ, u0, sig, hnew, hpool, hr, hsig, hs0, h0⟩
  · rw [hnew, hpool]
    simp only [Finset.toList_empty, List.map_nil, Multiset.coe_nil, add_zero]
    exact le_self_add
  · rw [hnew, hpool, Finset.toList_singleton]
    have hv : pview parameter data out.2 (m, ρ) = viewOf u0 := pview_of_cached h0
    simp only [List.map_cons, List.map_nil, hv, add_zero]
    rw [show ((([viewOf u0] : List View)) : Multiset View) = {viewOf u0} from rfl]
    have hbase : X d ≤ X (d + {viewOf u0}) := hX _ _ (Multiset.le_add_right _ _)
    rw [← add_tsub_cancel_of_le hbase]
    refine add_le_add le_rfl (le_trans ?_ le_self_add)
    unfold freshNewWeight
    rw [ite_eq_left (by rw [hres]; rfl)]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun ρ' => if s.cache (blk parameter data m ρ') = none then
      (out.2.cache (blk parameter data m ρ')).elim 0 (fun u0 =>
        if Landed parameter (blockIndex u0) then X (d + {viewOf u0}) - X d else 0) else 0)
      (fun _ _ => bot_le) (Finset.mem_univ ρ))
    simp only [hs0, h0, Option.elim, ite_true, ite_eq_left hl]
  · rw [hnew, hpool]
    simp only [Finset.toList_empty, List.map_nil, Multiset.coe_nil, add_zero]
    have hbase : X d ≤ X (d + {viewOf u0}) := hX _ _ (Multiset.le_add_right _ _)
    rw [← add_tsub_cancel_of_le hbase]
    refine add_le_add le_rfl (le_trans ?_ le_add_self)
    unfold outWeight
    rw [hres, hr]
    simp only
    rw [hsig, h0]
    simp only [Option.elim, pairWeight, hs0, reduceCtorEq, ite_false]
    have hne : s.cache (blk parameter data m sig.randomness) ≠ none := by
      rw [hsig, hs0]; exact Option.some_ne_none _
    have hx := hex sig hr hne
    rw [hsig] at hx
    rw [ite_eq_right hx]

variable (parameter data m)

/-- **One signing call, one term.** Averaged over the uniform start and the scan, the upper value of
a monotone function of the disclosures is at most the group of the message applied to that function
after one fresh slot. -/
theorem sign_term (hparse : ∀ ρ, model.parse (blk parameter data m ρ) = none)
    {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State) (d : Multiset View)
    (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr{let x ← (interp tg initial model
          ((liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpec Randomness) >>= fun start =>
            signCostSourceLoop parameter data m digestAttemptLimit start) budget s)}[x = out] *
        (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
          outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out)) ≤
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
  -- the scan part
  have hscan : ∑' out, Pr{let x ← (interp tg initial model
        ((liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpec Randomness) >>= fun start =>
          signCostSourceLoop parameter data m digestAttemptLimit start) budget s)}[x = out] *
        (freshNewWeight parameter data m s gf out + outWeight parameter data m s 0 gp out) ≤
      c * ∑ start, walk nextRand landing (stOf parameter data m s) (poolValue parameter data m s gp)
        (freshAvg Finset.univ gf) 0 digestAttemptLimit start := by
    rw [interp_liftProb_bind, OracleComp.tsum_prEvent_bind_mul]
    have hpr : ∀ ρ, Pr{let x ← ($ᵗ Randomness : ProbComp Randomness)}[x = ρ] = c := by
      intro ρ
      rw [SampleableType.prEvent_uniformSample_eq_singleton]
    simp only [hpr]
    rw [ENNReal.tsum_mul_left, tsum_fintype]
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ => ?_)
    exact scan_bound_comb tg initial model parameter data m hparse s gf gp digestAttemptLimit
      (by unfold digestAttemptLimit; norm_num) budget start
  have hsum : ∑' out, Pr{let x ← (interp tg initial model
        ((liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpec Randomness) >>= fun start =>
          signCostSourceLoop parameter data m digestAttemptLimit start) budget s)}[x = out] *
        (X d + (freshNewWeight parameter data m s gf out + outWeight parameter data m s 0 gp out)) ≤
      X d + c * ∑ start, walk nextRand landing (stOf parameter data m s) (poolValue parameter data m s gp)
        (freshAvg Finset.univ gf) 0 digestAttemptLimit start := by
    rw [tsum_congr fun out => mul_add _ _ _, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    exact add_le_add (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) hscan
  refine le_trans hsum ?_
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
        · simp only [hgp, ite_eq_left hx, add_zero, le_refl]
        · have hv : pview parameter data s (m, ρ) = viewOf u0 := pview_of_cached h0
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

end SignScan

end Sphincs.Security.ForsPotential
