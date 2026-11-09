module

public import FORS.LargeBudget.HeavyPotential
public import FORS.LargeBudget.WeightedPotentialH

@[expose] public section

/-! The weighted heavy potential (`GoodHW`) for programs over the honest-reading cost interface, the
signer honest (`advProgH`), as `WeightedPotentialH` does for the weighted one-coin potential. Honest reads may cache digest
blocks of the signed message for free, so the total invariant counts the cached index blocks of the
live messages only (`TotalInvL`): the heavy message is unique among the live messages, which is all
the potential reads. -/

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

/-! ### The total invariant of the live messages -/

section CountL

variable (parameter : PublicParameter) (data : PublicData)

/-- The pairs of live messages whose index block is cached. -/
noncomputable def totalCountL (L : QueryLog SigningSpec) (s : State) : ℕ :=
  (Finset.univ.filter fun q : Pair => MsgLive L q.1 ∧ s.cache (pblk parameter data q firstCall) ≠ none).card

/-- `TotalInv` for the live messages. -/
def TotalInvL (Qtot : ℕ) (L : QueryLog SigningSpec) (s : State) (budget : ℕ) : Prop :=
  totalCountL parameter data L s + budget ≤ Qtot

variable {parameter data}

/-- The live total invariant follows from the total one. -/
theorem totalInvL_of_totalInv {Qtot : ℕ} {L : QueryLog SigningSpec} {s : State} {budget : ℕ}
    (h : TotalInv parameter data Qtot s budget) : TotalInvL parameter data Qtot L s budget := by
  have hle : totalCountL parameter data L s ≤ totalCount parameter data s :=
    Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ hq => hq.2)
  unfold TotalInv at h
  unfold TotalInvL
  omega

theorem cachedCount_add_leL {L : QueryLog SigningSpec} {m m' : Message} (h : m ≠ m') (hm : MsgLive L m)
    (hm' : MsgLive L m') (s : State) :
    cachedCount parameter data m s + cachedCount parameter data m' s ≤ totalCountL parameter data L s := by
  have h1 : cachedCount parameter data m s =
      ((Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data m ρ) ≠ none).image
        fun ρ => ((m, ρ) : Pair)).card :=
    (Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.1 hab).2)).symm
  have h2 : cachedCount parameter data m' s =
      ((Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data m' ρ) ≠ none).image
        fun ρ => ((m', ρ) : Pair)).card :=
    (Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.1 hab).2)).symm
  have hdisj : Disjoint
      ((Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data m ρ) ≠ none).image
        fun ρ => ((m, ρ) : Pair))
      ((Finset.univ.filter fun ρ : Randomness => s.cache (blk parameter data m' ρ) ≠ none).image
        fun ρ => ((m', ρ) : Pair)) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.1 hq1
    obtain ⟨ρ', _, h'⟩ := Finset.mem_image.1 hq2
    exact h (congrArg Prod.fst h').symm
  rw [h1, h2, ← Finset.card_union_of_disjoint hdisj]
  unfold totalCountL
  refine Finset.card_le_card fun q hq => ?_
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hq
  rw [Finset.mem_filter]
  rcases hq with ⟨ρ, hρ, rfl⟩ | ⟨ρ, hρ, rfl⟩
  · have h2 : s.cache (pblk parameter data (m, ρ) firstCall) ≠ none := (Finset.mem_filter.1 hρ).2
    exact ⟨by simp, hm, h2⟩
  · have h2 : s.cache (pblk parameter data (m', ρ) firstCall) ≠ none := (Finset.mem_filter.1 hρ).2
    exact ⟨by simp, hm', h2⟩

/-- **At most one live message is heavy.** -/
theorem heavy_uniqueL {Qtot : ℕ} {L : QueryLog SigningSpec} {s : State} {budget : ℕ}
    (hT : TotalInvL parameter data Qtot L s budget) {m m' : Message} (hm : MsgLive L m) (hm' : MsgLive L m')
    (h : Heavy parameter data Qtot s m) (h' : Heavy parameter data Qtot s m') : m = m' := by
  by_contra hne
  have := cachedCount_add_leL (parameter := parameter) (data := data) hne hm hm' s
  unfold Heavy at h h'
  unfold TotalInvL at hT
  omega

/-- `heavyMsg_eq_some_iff` for a list of live messages. -/
theorem heavyMsg_eq_some_iffL {Qtot : ℕ} {L : QueryLog SigningSpec} {s : State} {budget : ℕ}
    (hT : TotalInvL parameter data Qtot L s budget) {l : List Message} (hl : ∀ m ∈ l, MsgLive L m) {h : Message} :
    heavyMsg parameter data Qtot s l = some h ↔ h ∈ l ∧ Heavy parameter data Qtot s h :=
  ⟨heavyMsg_some, fun hh => heavyMsg_eq_some hh.1 hh.2 fun m hm hm' =>
    heavy_uniqueL hT (hl m hm) (hl h hh.1) hm' hh.2⟩

/-- A state whose index blocks change at one pair only has at most one more cached live pair. -/
theorem totalCountL_off (L : QueryLog SigningSpec) (s s' : State) (p : Pair)
    (h : ∀ q : Pair, q ≠ p → s'.cache (pblk parameter data q firstCall) =
      s.cache (pblk parameter data q firstCall)) :
    totalCountL parameter data L s' ≤ totalCountL parameter data L s + 1 := by
  unfold totalCountL
  exact card_filter_le_off p fun q hq => by rw [h q hq]

/-- **A new pair keeps the live total invariant.** -/
theorem totalInvL_withPair {Qtot : ℕ} {L : QueryLog SigningSpec} {s : State} {budget : ℕ}
    (hT : TotalInvL parameter data Qtot L s budget) (hb : 1 ≤ budget) (p : Pair) (u : DigestCall → HashOutput) :
    TotalInvL parameter data Qtot L (withPair parameter data s p u) (budget - 1) := by
  have := totalCountL_off (parameter := parameter) (data := data) L s _ p fun q hqp => withPair_other_pair s p q hqp u firstCall
  unfold TotalInvL at hT ⊢
  omega

/-- **An ordinary query keeps the live total invariant.** -/
theorem totalInvL_ordinary {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) {Qtot : ℕ}
    {L : QueryLog SigningSpec} {s : State} {budget : ℕ} (hT : TotalInvL parameter data Qtot L s budget)
    (hb : 1 ≤ budget) (x : HashInput) (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model x s.known s)) :
    TotalInvL parameter data Qtot L r.2 (budget - 1) := by
  have hne := ordinaryStep_cache_ne model x s r hr
  have h1 : totalCountL parameter data L r.2 ≤ totalCountL parameter data L s + 1 := by
    by_cases hx : ∃ p : Pair, pblk parameter data p firstCall = x
    · obtain ⟨p, rfl⟩ := hx
      exact totalCountL_off (parameter := parameter) (data := data) L s r.2 p fun q hqp => hne _ fun h => hqp (pblk_injective parameter data h).1
    · have heq : totalCountL parameter data L r.2 = totalCountL parameter data L s := by
        unfold totalCountL
        exact congrArg Finset.card (Finset.filter_congr fun q _ => by rw [hne _ fun h => hx ⟨q, h⟩])
      omega
  unfold TotalInvL at hT ⊢
  omega

/-- **Signing a message keeps the live total invariant** when it leaves the index blocks of the other
messages alone. -/
theorem totalInvL_append {Qtot : ℕ} {L : QueryLog SigningSpec} {m : Message} {r : Option Signature} {s s' : State}
    {budget : ℕ} (hT : TotalInvL parameter data Qtot L s budget)
    (hkeep : ∀ q : Pair, q.1 ≠ m → s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall)) :
    TotalInvL parameter data Qtot (L ++ [⟨m, r⟩] : QueryLog SigningSpec) s' budget := by
  have h : totalCountL parameter data (L ++ [⟨m, r⟩] : QueryLog SigningSpec) s' ≤ totalCountL parameter data L s := by
    unfold totalCountL
    refine Finset.card_le_card (Finset.monotone_filter_right _ fun q _ hq => ?_)
    have hlive : MsgLive (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q.1 := hq.1
    have hc : s'.cache (pblk parameter data q firstCall) ≠ none := hq.2
    have hqm : q.1 ≠ m := fun he => hlive ⟨m, r⟩ (List.mem_append_right _ (List.mem_singleton_self _)) he.symm
    have hc' : s.cache (pblk parameter data q firstCall) ≠ none := by rw [← hkeep q hqm]; exact hc
    exact ⟨fun e he => hlive e (List.mem_append_left _ he), hc'⟩
  unfold TotalInvL at hT ⊢
  omega

end CountL

/-! ### Signing outcomes with the same result and state -/

section CongrH

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} {w b0 : ℝ≥0∞}
  {Fail : Finset (Fin (2 ^ subtreeHeight))} {m : Message} {s : State} {P : List Pair} {Ms : List Message}
  {L : QueryLog SigningSpec} {d : Multiset View}

theorem canonH_congr {o o' : Run HashInput Coordinate (Option Signature) × State} (h1 : o.1.1 = o'.1.1)
    (h2 : o.2 = o'.2) {n k : ℕ} :
    canonH parameter data Qtot w b0 Fail m s P Ms L d n k o = canonH parameter data Qtot w b0 Fail m s P Ms L d n k o' := by
  obtain ⟨⟨a, b, c, e⟩, st⟩ := o
  obtain ⟨⟨a', b', c', e'⟩, st'⟩ := o'
  simp only at h1 h2
  subst h1 h2
  rfl

end CongrH

/-! ### A new pair, under the live total invariant -/

section NewPairTermL

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} {w : ℝ≥0∞}

/-- **The cases of a new pair.** Either the light and heavy messages are the same before and after
(the message of the pair is light before and after, or not live), or the message of the pair is the
heavy one after: it was heavy before, or it was light and no live message was heavy. -/
theorem newPair_casesL {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) {budget : ℕ}
    (hb : 1 ≤ budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec)
    (hT : TotalInvL parameter data Qtot L s budget) (excl : Pair → Prop)
    (f : Multiset View → ℝ≥0∞) (d : Multiset View) (n : ℕ) :
    ((∀ u I, baseH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n I =
        valH parameter data w (withPair parameter data s p u) excl
          (lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)))
          (heavyMsg parameter data Qtot s (live L (addMsg Ms p.1))) f n I d) ∧
      heavyMsg parameter data Qtot s (live L (addMsg Ms p.1)) ≠ some p.1 ∧
      (p.1 ∈ lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)) ∨ p.1 ∉ live L (addMsg Ms p.1))) ∨
    (∃ rest : List Message, p.1 ∉ rest ∧
      (∀ u I, baseH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n I =
        valH parameter data w (withPair parameter data s p u) excl rest (some p.1) f n I d) ∧
      ((∀ I, valH parameter data w s excl rest (some p.1) f n I d =
          baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I) ∨
        (∀ I, valH parameter data w s excl (p.1 :: rest) none f n I d =
          baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I))) := by
  set Lv := live L (addMsg Ms p.1) with hLv
  have hnd : Lv.Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  have hoth : ∀ u m, m ≠ p.1 → (Heavy parameter data Qtot (withPair parameter data s p u) m ↔
      Heavy parameter data Qtot s m) := fun u m hm => heavy_withPair_other s p u hm
  have hself : ∀ u, Heavy parameter data Qtot (withPair parameter data s p u) p.1 ↔
      Qtot < 2 * (cachedCount parameter data p.1 s + 1) := fun u => heavy_withPair_self hp0 u
  by_cases hmem : p.1 ∈ Lv
  swap
  · -- the message is not live
    left
    have hc : ∀ u, ∀ m ∈ Lv, (Heavy parameter data Qtot (withPair parameter data s p u) m ↔
        Heavy parameter data Qtot s m) := fun u m hm => hoth u m (fun h => hmem (h ▸ hm))
    refine ⟨fun u I => ?_, fun h => hmem (heavyMsg_some h).1, Or.inr hmem⟩
    unfold baseH
    rw [lightMsgs_congr (hc u), heavyMsg_congr (hc u)]
  by_cases hH : Heavy parameter data Qtot s p.1
  · -- heavy before and after
    right
    have hsome : heavyMsg parameter data Qtot s Lv = some p.1 := (heavyMsg_eq_some_iffL hT fun _ hx => (mem_live.1 hx).2).2 ⟨hmem, hH⟩
    have hA : Qtot < 2 * (cachedCount parameter data p.1 s + 1) := by unfold Heavy at hH; omega
    have hc : ∀ u, ∀ m ∈ Lv, (Heavy parameter data Qtot (withPair parameter data s p u) m ↔
        Heavy parameter data Qtot s m) := by
      intro u m hm
      by_cases hmp : m = p.1
      · rw [hmp]; exact ⟨fun _ => hH, fun _ => (hself u).2 hA⟩
      · exact hoth u m hmp
    refine ⟨lightMsgs parameter data Qtot s Lv, fun h => (mem_lightMsgs.1 h).2 hH, fun u I => ?_, Or.inl fun I => ?_⟩
    · unfold baseH
      rw [lightMsgs_congr (hc u), heavyMsg_congr (hc u), hsome]
    · unfold baseH
      rw [hsome]
  by_cases hA : Qtot < 2 * (cachedCount parameter data p.1 s + 1)
  · -- light before, heavy after: no other live message is heavy
    right
    have hlight : ∀ m ∈ Lv, m ≠ p.1 → ¬Heavy parameter data Qtot s m := by
      intro m hmLv hne hm
      have := cachedCount_add_leL (parameter := parameter) (data := data) hne (mem_live.1 hmLv).2 (mem_live.1 hmem).2 s
      unfold Heavy at hm
      unfold TotalInvL at hT
      omega
    have hnone : heavyMsg parameter data Qtot s Lv = none := by
      refine heavyMsg_eq_none.2 fun m hm => ?_
      by_cases hmp : m = p.1
      · rw [hmp]; exact hH
      · exact hlight m hm hmp
    have hsome : ∀ u, heavyMsg parameter data Qtot (withPair parameter data s p u) Lv = some p.1 := fun u =>
      heavyMsg_eq_some hmem ((hself u).2 hA) fun m hm hm' => by
        by_contra hne
        exact hlight m hm hne ((hoth u m hne).1 hm')
    have hrest : ∀ u, lightMsgs parameter data Qtot (withPair parameter data s p u) Lv = Lv.erase p.1 := by
      intro u
      rw [hnd.erase_eq_filter]
      unfold lightMsgs
      refine List.filter_congr fun m hm => ?_
      rw [Bool.eq_iff_iff]
      simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact ⟨fun hnh heq => hnh (heq ▸ (hself u).2 hA), fun hne hm' => hlight m hm hne ((hoth u m hne).1 hm')⟩
    refine ⟨Lv.erase p.1, fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl, fun u I => ?_, Or.inr fun I => ?_⟩
    · unfold baseH
      rw [hrest u, hsome u]
    · unfold baseH
      rw [hnone, lightMsgs_of_none hnone]
      exact valH_perm_msgs s excl (List.perm_cons_erase hmem).symm none f n I d
  · -- light before and after
    left
    have hc : ∀ u, ∀ m ∈ Lv, (Heavy parameter data Qtot (withPair parameter data s p u) m ↔
        Heavy parameter data Qtot s m) := by
      intro u m hm
      by_cases hmp : m = p.1
      · rw [hmp]; exact ⟨fun h => absurd ((hself u).1 h) hA, fun h => absurd h hH⟩
      · exact hoth u m hmp
    refine ⟨fun u I => ?_, fun h => hH (heavyMsg_some h).2, Or.inl (mem_lightMsgs.2 ⟨hmem, hH⟩)⟩
    unfold baseH
    rw [lightMsgs_congr (hc u), heavyMsg_congr (hc u)]

/-- **A new pair, the base of a term**, in the mean over its block. -/
theorem baseH_newPairL (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) {budget : ℕ} (hb : 1 ≤ budget)
    (p : Pair) (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec)
    (hT : TotalInvL parameter data Qtot L s budget) (excl : Pair → Prop)
    (hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1)
    (d : Multiset View) (n : ℕ) (I : List View) :
    pairE (fun u => baseH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n I) ≤
      (1 - landing) * baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I +
        landing * freshAvg Finset.univ (fun v => baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n (v :: I)) := by
  have hnd : (live L (addMsg Ms p.1)).Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  have hmix : ∀ B : ℝ≥0∞, B ≤ baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I →
      B ≤ (1 - landing) * baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I +
        landing * freshAvg Finset.univ (fun v => baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n (v :: I)) :=
    fun B hB => le_trans hB (mix_ge fun v => baseH_cons hw hf s _ L excl d n v I)
  rcases newPair_casesL (w := w) hM hb p hp0 L hT excl f d n with ⟨hsame, hne, hor⟩ | ⟨rest, hnot, hsame, halt⟩
  · have hbl : ∀ u h, heavyMsg parameter data Qtot s (live L (addMsg Ms p.1)) = some h →
        ∀ ρ call, (withPair parameter data s p u).cache (pblk parameter data (h, ρ) call) =
          s.cache (pblk parameter data (h, ρ) call) :=
      fun u h hh ρ call => withPair_other_pair s p (h, ρ)
        (fun heq => hne (hh.trans (congrArg some (congrArg Prod.fst heq)))) u call
    rcases hor with hlight | hnotin
    · -- the message is light before and after: one coin pays
      obtain ⟨hmem, hnh⟩ := mem_lightMsgs.1 hlight
      have hlive : MsgLive L p.1 := (mem_live.1 hmem).2
      rw [show (fun u => baseH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n I) =
          fun u => grpAll parameter data (withPair parameter data s p u) excl
            (lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)))
            (innerH parameter data w s excl (heavyMsg parameter data Qtot s (live L (addMsg Ms p.1))) f n I) d
          from funext fun u => (hsame u I).trans
            (grpAll_congr _ excl
              (fun e => innerH_blocksOn excl (fun h hh ρ => hbl u h hh ρ firstCall)
                (fun h hh ρ _ => hbl u h hh ρ) f n I e) _ d)]
      exact grpAll_probeG hw s p hp0 excl _ (lightMsgs_nodup hnd) hlight (hrate hlive hnh)
        (fun I => innerH parameter data w s excl (heavyMsg parameter data Qtot s (live L (addMsg Ms p.1))) f n I)
        (fun I => innerH_mono hf.1 s excl _ n I) (fun I e => innerH_ne_top hw hf.2 s excl _ n I e)
        (fun v I e => innerH_coin s excl _ f n v I e) I d
    · -- the message is not live: nothing changes
      have hoth : ∀ (u : DigestCall → HashOutput) m,
          m ∈ lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)) → ∀ ρ call,
            (withPair parameter data s p u).cache (pblk parameter data (m, ρ) call) =
              s.cache (pblk parameter data (m, ρ) call) :=
        fun u m hm ρ call => withPair_other_pair s p (m, ρ)
          (fun heq => by
            have h1 : m = p.1 := congrArg Prod.fst heq
            have hmm := (mem_lightMsgs.1 hm).1
            rw [h1] at hmm
            exact hnotin hmm) u call
      have hpt : ∀ u, baseH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n I =
          baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I := fun u =>
        (hsame u I).trans (valH_blocksOn excl (hoth u) (hbl u) f n I d)
      simp only [hpt, pairE_const]
      exact hmix _ le_rfl
  · -- the message is the heavy one after: the law of its signed view keeps its mean
    have hX : Monotone' (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) :=
      grpAll_mono s excl (virtualOnce_mono hf.1 n I) rest
    have hXfin : ∀ e, grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I) e ≠ ⊤ :=
      grpAll_ne_top s excl (virtualOnce_ne_top Finset.univ_nonempty hw hf.2 n I) rest
    rw [show (fun u => baseH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n I) =
        fun u => sgnM parameter data (withPair parameter data s p u) excl p.1
          (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) d
        from funext fun u => (hsame u I).trans (valH_heavy_withPair s p u excl hnot f n I d)]
    exact hmix _ (le_trans (sgnM_probe s p hp0 excl hX hXfin d) (heavy_alt_le hf.1 s excl p.1 rest n d halt I))

/-- **A new pair, one term.** In the mean the forecast of a term after the block of a new pair is at
most its forecast with one more future pair. The rate is needed only for a live message that is not
heavy. -/
theorem termH_newPairL (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) {budget : ℕ} (hb : 1 ≤ budget)
    (p : Pair) (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec)
    (hT : TotalInvL parameter data Qtot L s budget) (excl : Pair → Prop)
    (hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1)
    (d : Multiset View) (n k : ℕ) :
    pairE (fun u => termH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n k) ≤
      termH parameter data Qtot w s Ms L excl f d n (k + 1) := by
  rw [← termH_addMsg hM L excl p.1 f d n (k + 1)]
  unfold termH pairE
  rw [creations_tsum, ← creations_one]
  refine creations_mono (fun I => ?_) k []
  exact baseH_newPairL hw hf hM hb p hp0 L hT excl hrate d n I

/-- **The new candidate.** A new landed pair that is excluded stops the walks of its message
without disclosing anything: its forecast in the new state is at most its forecast in the old one. -/
theorem termH_stopL {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) {budget : ℕ} (hb : 1 ≤ budget)
    (p : Pair) (hp0 : s.cache (pblk parameter data p firstCall) = none)
    (L : QueryLog SigningSpec) (hT : TotalInvL parameter data Qtot L s budget) (excl : Pair → Prop) (hx : excl p) (u : DigestCall → HashOutput)
    (hl : Landed parameter (blockIndex (u firstCall))) (d : Multiset View) (n k : ℕ) :
    termH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n k ≤
      termH parameter data Qtot w s Ms L excl f d n k := by
  rw [← termH_addMsg hM L excl p.1 f d n k]
  have hnd : (live L (addMsg Ms p.1)).Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  refine creations_mono (fun I => ?_) k []
  rcases newPair_casesL (w := w) hM hb p hp0 L hT excl f d n with ⟨hsame, hne, hor⟩ | ⟨rest, hnot, hsame, halt⟩
  · have hbl : ∀ h, heavyMsg parameter data Qtot s (live L (addMsg Ms p.1)) = some h →
        ∀ ρ call, (withPair parameter data s p u).cache (pblk parameter data (h, ρ) call) =
          s.cache (pblk parameter data (h, ρ) call) :=
      fun h hh ρ call => withPair_other_pair s p (h, ρ)
        (fun heq => hne (hh.trans (congrArg some (congrArg Prod.fst heq)))) u call
    rcases hor with hlight | hnotin
    · set Ls := lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)) with hLs
      set G := innerH parameter data w s excl (heavyMsg parameter data Qtot s (live L (addMsg Ms p.1))) f n I with hG
      have hGmono : Monotone' G := innerH_mono hf.1 s excl _ n I
      have hLnd : Ls.Nodup := lightMsgs_nodup hnd
      set rest := Ls.erase p.1 with hrest
      have hperm : Ls.Perm (p.1 :: rest) := List.perm_cons_erase hlight
      have hnot : p.1 ∉ rest := fun h => (List.Nodup.mem_erase_iff hLnd).1 h |>.1 rfl
      have hst : stOf parameter data p.1 s p.2 = .fresh := by
        have h : s.cache (blk parameter data p.1 p.2) = none := hp0
        simp [stOf, h]
      have h1 : baseH parameter data Qtot w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n I =
          grpAll parameter data (withPair parameter data s p u) excl Ls G d :=
        (hsame u I).trans (grpAll_congr _ excl
          (fun e => innerH_blocksOn excl (fun h hh ρ => hbl h hh ρ firstCall)
            (fun h hh ρ _ => hbl h hh ρ) f n I e) _ d)
      have h2 : baseH parameter data Qtot w s (addMsg Ms p.1) L excl f d n I = grpAll parameter data s excl Ls G d := rfl
      rw [h1, h2, grpAll_perm _ excl _ hperm d, grpAll_perm _ excl _ hperm d]
      simp only [grpAll]
      rw [grpM_withPair_self, ite_eq_left hl, ite_eq_left hx,
        grp_congr _ _ (fun e => grpAll_withPair_other s p u excl G rest hnot e) d]
      exact grp_stop_le landing_le_one Finset.univ_nonempty _ _ (grpAll_mono s excl hGmono rest) d p.2 hst
    · have hoth : ∀ m, m ∈ lightMsgs parameter data Qtot s (live L (addMsg Ms p.1)) → ∀ ρ call,
          (withPair parameter data s p u).cache (pblk parameter data (m, ρ) call) =
            s.cache (pblk parameter data (m, ρ) call) :=
        fun m hm ρ call => withPair_other_pair s p (m, ρ)
          (fun heq => by
            have h1 : m = p.1 := congrArg Prod.fst heq
            have hmm := (mem_lightMsgs.1 hm).1
            rw [h1] at hmm
            exact hnotin hmm) u call
      exact le_of_eq ((hsame u I).trans (valH_blocksOn excl hoth hbl f n I d))
  · have hX : Monotone' (grpAll parameter data s excl rest (virtualOnce Finset.univ w f n I)) :=
      grpAll_mono s excl (virtualOnce_mono hf.1 n I) rest
    rw [hsame u I, valH_heavy_withPair s p u excl hnot f n I d]
    exact le_trans (sgnM_stop s p excl hx u hl hX d) (heavy_alt_le hf.1 s excl p.1 rest n d halt I)

end NewPairTermL

section NewPairHL

variable {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- **A new pair.** Touching a new pair costs one future pair and at most the baseline. The rate is
needed only when the message of the pair is live and not heavy. -/
theorem coreH_newPairL (hw : w ≤ 1) {s : State} {P : List Pair} {Ms : List Message}
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) {budget : ℕ}
    (hb : 1 ≤ budget) {p : Pair}
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec)
    (hT : TotalInvL parameter data Qtot L s budget)
    (hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1)
    (d : Multiset View) (n k : ℕ) :
    pairE (fun u => coreH parameter data Qtot w b0 Fail (withPair parameter data s p u)
      (addPair parameter P p u) (addMsg Ms p.1) L d n k) ≤
      coreH parameter data Qtot w b0 Fail s P Ms L d n (k + 1) + b0 := by
  set Ms' := addMsg Ms p.1 with hMs'
  set φ := failMass Fail with hφ
  have hpP := not_mem_of_fresh hP hp0
  set Wp : View → ℝ≥0∞ := fun v => termH parameter data Qtot w s Ms L (· = p) (witnessFn v) d n k with hWp
  set H := hValueH parameter data Qtot w b0 s Ms L d n (k + 1) with hH
  set S := (P.map (candH parameter data Qtot w Fail s Ms L d n (k + 1))).sum with hS
  -- the candidates of the old pairs
  have h2 : ∀ q ∈ P, pairE (fun u => candH parameter data Qtot w Fail (withPair parameter data s p u) Ms' L d n k q) ≤
      candH parameter data Qtot w Fail s Ms L d n (k + 1) q := by
    intro q hq
    have hqp : q ≠ p := fun h => hpP (h ▸ hq)
    have hv : ∀ u, pview parameter data (withPair parameter data s p u) q = pview parameter data s q :=
      fun u => pview_withPair_other s p q hqp u
    unfold candH candValueH
    simp only [hv]
    split_ifs
    · simp only [pairE_const, le_refl]
    · exact termH_newPairL hw (witness_props _) hM hb p hp0 L hT _ hrate d n k
    · simp only [pairE_const, le_refl]
  -- the candidate of the new pair
  have hnew : ∀ u, Landed parameter (blockIndex (u firstCall)) →
      candH parameter data Qtot w Fail (withPair parameter data s p u) Ms' L d n k p ≤
        (if (viewOf u).1 ∈ Fail then 1 else 0) + Wp (viewOf u) := by
    intro u hl
    unfold candH candValueH
    rw [pview_withPair_self]
    by_cases hu : Unsigned L p
    · rw [ite_eq_left hu]
      by_cases hF : (viewOf u).1 ∈ Fail
      · rw [ite_eq_left hF, ite_eq_left hF]
        exact le_self_add
      · rw [ite_eq_right hF, ite_eq_right hF, zero_add]
        exact termH_stopL (witness_props _) hM hb p hp0 L hT (· = p) rfl u hl d n k
    · rw [ite_eq_right hu]
      exact bot_le
  have hpoint : ∀ u, coreH parameter data Qtot w b0 Fail (withPair parameter data s p u)
      (addPair parameter P p u) Ms' L d n k ≤
      ((if Landed parameter (blockIndex (u firstCall)) then (fun v : View => (if v.1 ∈ Fail then 1 else 0) + Wp v) (viewOf u)
          else 0) +
        (P.map fun q => candH parameter data Qtot w Fail (withPair parameter data s p u) Ms' L d n k q).sum) +
      k * (hValueH parameter data Qtot w b0 (withPair parameter data s p u) Ms' L d n k + φ) + n * φ := by
    intro u
    unfold coreH
    refine add_le_add (add_le_add ?_ le_rfl) le_rfl
    unfold addPair
    by_cases hl : Landed parameter (blockIndex (u firstCall))
    · rw [ite_eq_left hl, ite_eq_left hl, List.map_cons, List.sum_cons]
      exact add_le_add (hnew u hl) le_rfl
    · rw [ite_eq_right hl, ite_eq_right hl, zero_add]
  refine le_trans (pairE_mono hpoint) ?_
  simp only [pairE_add, pairE_const_mul, pairE_const, pairE_list_sum]
  have h1 : pairE (fun u => if Landed parameter (blockIndex (u firstCall)) then
      (fun v : View => (if v.1 ∈ Fail then 1 else 0) + Wp v) (viewOf u) else 0) =
      landing * (φ + freshAvg Finset.univ Wp) := by
    rw [pairE_landed parameter (fun v => (if v.1 ∈ Fail then 1 else 0) + Wp v) 0, mul_zero, add_zero, freshAvg_add]
    rfl
  have h3 : pairE (fun u => hValueH parameter data Qtot w b0 (withPair parameter data s p u) Ms' L d n k) ≤ H :=
    termH_newPairL hw (excess_props b0) hM hb p hp0 L hT _ hrate d n k
  have hfresh : landing * freshAvg Finset.univ Wp ≤ b0 + H := by
    refine le_trans (fresh_forecastH hw b0 s Ms L (· = p) d n k) (add_le_add le_rfl ?_)
    refine le_trans (termH_excl_mono (excess_props b0) s Ms L (fun _ h => False.elim h) d n k) ?_
    exact hValueH_mono w b0 hw s Ms L d n (Nat.le_succ k)
  have hφ1 : landing * φ ≤ φ := mul_le_of_le_one_left' landing_le_one
  have hSle : (P.map fun q => pairE fun u => candH parameter data Qtot w Fail (withPair parameter data s p u) Ms' L d n k q).sum ≤
      S := List.sum_le_sum fun q hq => h2 q hq
  rw [h1]
  unfold coreH
  calc landing * (φ + freshAvg Finset.univ Wp) +
        (P.map fun q => pairE fun u => candH parameter data Qtot w Fail (withPair parameter data s p u) Ms' L d n k q).sum +
        k * (pairE (fun u => hValueH parameter data Qtot w b0 (withPair parameter data s p u) Ms' L d n k) + φ) + n * φ
      ≤ φ + (b0 + H) + S + k * (H + φ) + n * φ := by
        rw [mul_add]
        gcongr
    _ = S + ((k : ℝ≥0∞) + 1) * (H + φ) + n * φ + b0 := by ring
    _ = _ := by push_cast; ring

end NewPairHL

/-! ### Signing a message for the first time -/

section SignExpectHWL

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  {parameter : PublicParameter} {data : PublicData} {Qtot : ℕ} {w : ℝ≥0∞} {m : Message} {s : State} {n : ℕ}
  {d : Multiset View} {f : Multiset View → ℝ≥0∞}

/-- **A dominated term, weighted**. -/
theorem term_expectHWL (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none)
    (hinv : PairInv parameter data m s) (hf : MonoFin f)
    {Ms : List Message} (hM : MInv parameter data s Ms) {L : QueryLog SigningSpec} {budgetT : ℕ}
    (hT : TotalInvL parameter data Qtot L s budgetT) (hm : MsgLive L m) (excl : Pair → Prop) (budget k : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
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
      heavyMsg_eq_none.2 fun m' hm' hh => hrestne m' hm' (heavy_uniqueL hT (mem_live.1 (List.mem_filter.1 hm').1).2 hm hh hH)
    have hlightR : lightMsgs parameter data Qtot s (restMsgs m L Ms) = restMsgs m L Ms := lightMsgs_of_none hnoneR
    have hsomeV : heavyMsg parameter data Qtot s (live L (addMsg Ms m)) = some m :=
      (heavyMsg_eq_some_iffL hT fun _ hx => (mem_live.1 hx).2).2 ⟨hperm.mem_iff.2 (List.mem_cons_self ..), hH⟩
    have hlightV : (lightMsgs parameter data Qtot s (live L (addMsg Ms m))).Perm (restMsgs m L Ms) := by
      have h1 := hperm.filter (fun m' => decide (¬Heavy parameter data Qtot s m'))
      rw [List.filter_cons, ite_eq_right (by simpa using hH)] at h1
      rw [← hlightR]
      exact h1
    refine le_trans (sign_termSW tg initial model parameter data m hparse hkind hX s hinv d excl budget)
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
          exact (heavyMsg_eq_some_iffL hT fun _ hx => (mem_live.1 hx).2).2
            ⟨hperm.mem_iff.2 (List.mem_cons_of_mem _ (heavyMsg_some hR).1), (heavyMsg_some hR).2⟩
    have hlightV : (lightMsgs parameter data Qtot s (live L (addMsg Ms m))).Perm
        (m :: lightMsgs parameter data Qtot s (restMsgs m L Ms)) := by
      have h1 := hperm.filter (fun m' => decide (¬Heavy parameter data Qtot s m'))
      rw [List.filter_cons, ite_eq_left (by simpa using hH)] at h1
      exact h1
    refine le_trans (upper_expectW tg initial model parameter data m hparse hkind hX s hinv d excl budget)
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

end SignExpectHWL

section SignPointHW2

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight))) (m : Message)

/-- `sign_pointH` with the signer's interpreter budget `bi` apart from the potential's budget `budget`; it needs
no count invariant. -/
theorem sign_pointH2 (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (bi budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) bi s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' : ℕ} (hk : k' ≤ budget) :
    (if Realized tg initial out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length then 0
      else coreH parameter data Qtot w b0 Fail out.2 (newPairs parameter data m s out.2 ++ P) (addMsg Ms m)
        (L ++ [⟨m, r⟩]) (discAfter parameter data m s d out)
        (signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length) k') ≤
      if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
      else canonH parameter data Qtot w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out := by
  obtain ⟨_, hP', _, _, _, hview⟩ := sign_paramsS tg initial model Fail (Fintype.card Randomness + bi) hparse hfail bi
    s P Ms d R hprep hP hM hD (countInv_card parameter data s bi) out hout r hr
  have hext := interp_extends tg initial model _ bi s out hout
  have hpost := source_post tg initial model parameter data m (fun ρ => hparse (m, ρ)) Fail hfail
    bi s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  by_cases hcase : Realized tg initial out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length
  · rw [ite_eq_left hcase]; exact bot_le
  rw [ite_eq_right hcase]
  have hreal : ¬Realized tg initial s := fun h => hcase (Or.inl (realized_of_extends tg initial hext h))
  have hlen : L.length < signatureLimit := by
    have := hcase
    simp only [List.length_append, List.length_singleton, not_or, not_lt] at this
    omega
  rw [ite_eq_right (by push Not; exact ⟨hreal, hlen⟩)]
  have hn : signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length = signatureLimit - (L.length + 1) := by simp
  rw [hn]
  set n := signatureLimit - (L.length + 1) with hndef
  unfold coreH canonH
  rw [List.map_append, List.sum_append]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · -- new pairs: only a failed fresh pair stays a candidate
    rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u, hnew, _, h0, hl, hs0, _, hfl, hsig⟩ | ⟨_, _, _, hnew, _⟩
    · unfold newPairs; rw [hnew]; simp
    · have hv : pview parameter data out.2 (m, ρ) = viewOf u := pview_of_pcache (q := (m, ρ)) h0
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
      rw [ite_eq_left hU', ite_eq_left hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValueH
        rw [hview q hq]
        refine post_term_leH tg initial model parameter data Qtot w Fail m hw (witness_props _) hparse hfail bi
          s Ms L d hprep out hout r hr (· = q) (fun sig hsig _ heq => ?_) n hk
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [ite_eq_right hU']
      exact bot_le
  · -- the excess forecast
    refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValueH
    exact post_term_leH tg initial model parameter data Qtot w Fail m hw (excess_props b0) hparse hfail bi
      s Ms L d hprep out hout r hr (fun _ => False) (fun _ _ _ h => h) n hk

/-- `sign_expectHW` with the signer's interpreter budget `bi` apart from the potential's budget `budget`,
under the total invariant of the live messages. -/
theorem sign_expectHW2 (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (bi budget : ℕ) (s : State) (P : List Pair) (hP : PInv parameter data s P) (Ms : List Message)
    (L : QueryLog SigningSpec) (hm : MsgLive L m) (d : Multiset View) (hM : MInv parameter data s Ms)
    {budgetT : ℕ} (hT : TotalInvL parameter data Qtot L s budgetT) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
        (weight tg initial out.2 * (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canonH parameter data Qtot w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out)) ≤
      weight tg initial s * (if Realized tg initial s ∨ signatureLimit < L.length then 0
        else coreH parameter data Qtot w b0 Fail s P Ms L d (signatureLimit - L.length) budget) := by
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
    fun ρ => hparse (m, ρ)
  have hkind' : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none :=
    fun ρ => hkind (m, ρ)
  have hinv : PairInv parameter data m s := pairInv_of_pinv hP m
  have hconst := fun c => interp_weight_constW tg initial model (s := s)
    (signCostSource parameter data m) bi c
  have hFN : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) ≤
      weight tg initial s * failMass Fail :=
    fresh_expectW tg initial model parameter data m hparse' hkind' s hinv _ bi
  have hTm : ∀ q ∈ P, ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d (witnessFn (pview parameter data s q))
          L Ms (· = q) out J) budget []) else 0)) ≤
      weight tg initial s * candH parameter data Qtot w Fail s Ms L d (n + 1) budget q := by
    intro q _
    unfold candH
    split_ifs
    · exact hconst 1
    · unfold candValueH
      exact term_expectHWL tg initial model hparse' hkind' hinv (witness_props _) hM hT hm _ bi budget
    · exact hconst 0
  have hH : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d (excess b0)
        L Ms (fun _ => False) out J) budget []) ≤
      weight tg initial s * hValueH parameter data Qtot w b0 s Ms L d (n + 1) budget := by
    unfold hValueH
    exact term_expectHWL tg initial model hparse' hkind' hinv (excess_props b0) hM hT hm _ bi budget
  have hLS : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
        else creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d
          (witnessFn (pview parameter data s q)) L Ms (· = q) out J) budget [])
        else 0).sum) ≤
      weight tg initial s * (P.map (candH parameter data Qtot w Fail s Ms L d (n + 1) budget)).sum := by
    simp only [← mul_assoc]
    rw [tsum_list_sum, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun q hq => by simpa only [mul_assoc] using hTm q hq
  have hHC : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
        (fun J => upperH parameter data Qtot w m s n d (excess b0) L Ms (fun _ => False) out J) budget [] +
          failMass Fail))) ≤
      weight tg initial s * ((budget : ℝ≥0∞) * (hValueH parameter data Qtot w b0 s Ms L d (n + 1) budget +
        failMass Fail)) := by
    have hpt : ∀ out : Run HashInput Coordinate (Option Signature) × State,
        Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperH parameter data Qtot w m s n d (excess b0) L Ms (fun _ => False) out J) budget [] +
              failMass Fail))) =
        (budget : ℝ≥0∞) * (Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * creations Finset.univ landing
            (fun J => upperH parameter data Qtot w m s n d (excess b0) L Ms (fun _ => False) out J) budget [])) +
        (budget : ℝ≥0∞) * (Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * failMass Fail)) := by
      intro out
      ring
    simp only [hpt, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    calc _ ≤ (budget : ℝ≥0∞) * (weight tg initial s * hValueH parameter data Qtot w b0 s Ms L d (n + 1) budget) +
          (budget : ℝ≥0∞) * (weight tg initial s * failMass Fail) :=
          add_le_add (mul_le_mul' le_rfl hH) (mul_le_mul' le_rfl (hconst _))
      _ = _ := by ring
  have hsplit : ∀ out : Run HashInput Coordinate (Option Signature) × State,
      Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
        (weight tg initial out.2 * canonH parameter data Qtot w b0 Fail m s P Ms L d n budget out) =
      Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) +
        Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
            else creations Finset.univ landing (fun J => upperH parameter data Qtot w m s n d
              (witnessFn (pview parameter data s q)) L Ms (· = q) out J) budget [])
            else 0).sum) +
        Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperH parameter data Qtot w m s n d (excess b0) L Ms (fun _ => False) out J) budget [] +
              failMass Fail))) +
        Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
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

end SignPointHW2

/-! ### Weighted paid programs with the honest signer -/

section GoodHW

variable (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (w b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A program whose final value, weighted by the final survival weight, is paid by the weighted
potential with one heavy message and the weighted baseline payments. -/
def GoodHW (L : QueryLog SigningSpec) (prog : OracleComp CostSpecH HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → MInv parameter data s Ms → DInv R d →
      TotalInvL parameter data Qtot L s budget →
      ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
        weight tg initial s * potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wflag tg initial model prog budget s

theorem goodHWH_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (next v)) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L
      (liftM (CostSpecH.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hT
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
        (weight tg initial s * potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wflag tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hprep hP hM hD hT) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) (le_of_eq ?_)
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- The potential part of a new pair, when the coin pays the rate of its message if it is live and
not heavy. -/
theorem new_pair_coreHL (hw : w ≤ 1) (L : QueryLog SigningSpec)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms)
    (hT : TotalInvL parameter data Qtot L s budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p firstCall) = none)
    (hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1) :
    pairE (fun u => potH parameter data Qtot w b0 Fail tg initial Lmax (withPair parameter data s p u)
        (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1)) ≤
      potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
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
  unfold potH
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
    have hcore : coreH parameter data Qtot w b0 Fail s P Ms L d n budget =
        coreH parameter data Qtot w b0 Fail s P Ms L d n (budget - 1 + 1) := by rw [Nat.sub_add_cancel hb]
    rw [hcore]
    refine le_trans ?_ (coreH_newPairL w b0 Fail hw hP hM hb hp0 L hT hrate d n (budget - 1))
    refine pairE_mono fun u => ?_
    split_ifs
    · exact bot_le
    · exact le_rfl

/-- A new pair: one of its blocks is read fresh and the others are presampled, weighted. The blocks
are untargeted, so the presample keeps both the weight (`weight_storeAllW`) and the weighted
payments (`wflag_presample_new_eq`). The coin pays the rate of a message with at most `Qtot / 2`
cached digests. -/
theorem new_pair_boundHW {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax)
    (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hT : TotalInvL parameter data Qtot L s budget) (p : Pair) (c : DigestCall)
    (hkind : ∀ call, tg.kind (pblk parameter data p call) = .none)
    (hp0 : s.cache (pblk parameter data p firstCall) = none) :
    ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
        ∑' out, Pr{let z ← (interp tg initial model (next v) (budget - 1)
          (s.store (pblk parameter data p c) v))}[z = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
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
          unfold potH
          exact le_trans (mul_le_mul' le_rfl le_add_self) le_self_add
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  have hrate : MsgLive L p.1 → ¬Heavy parameter data Qtot s p.1 → Rate parameter data w s p.1 :=
    fun hlive hnh => rate_of_fair hfair s p.1 (le_trans (cachedCount_le_of_not_heavy hnh) hQ)
      (le_trans (landedCount_le hP L hlive) hlen)
  have hone : ∀ u, ∑' out, Pr{let x ← (interp tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u))}[x = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potH parameter data Qtot w b0 Fail tg initial Lmax (withPair parameter data s p u)
          (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) +
        b0 * wflag tg initial model (next (u c)) (budget - 1) (withPair parameter data s p u) := fun u => by
    have := h (u c) (budget - 1) _ _ _ d R
      (fun x v hx => (extends_withPair hP hp0 u).1 x v (hprep x v hx)) (pinv_withPair hP hp0 u)
      (minv_withPair hM p u) hD (totalInvL_withPair hT hb p u)
    rwa [hwall u] at this
  refine le_trans (le_trans hpre (pairE_mono hone)) ?_
  rw [pairE_add, pairE_const_mul, pairE_const_mul, hcount, mul_add, ← add_assoc]
  refine add_le_add ?_ le_rfl
  calc weight tg initial s * pairE (fun u => potH parameter data Qtot w b0 Fail tg initial Lmax
          (withPair parameter data s p u) (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1))
      ≤ weight tg initial s * (potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * (if Realized tg initial s then 0 else 1)) :=
        mul_le_mul_right (new_pair_coreHL parameter data Qtot w b0 Fail Lmax tg initial hfair.le_one L budget hb
          s P Ms d hP hM hT p hp0 hrate) _
    _ ≤ _ := by
        rw [mul_add]
        refine add_le_add le_rfl ?_
        rw [mul_left_comm]
        refine mul_le_mul_right ?_ _
        split_ifs <;> simp

/-- **One ordinary query, weighted.** -/
theorem goodHWH_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (next v)) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L
      (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hT
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
    exact new_pair_boundHW parameter data Qtot w b0 Fail Lmax tg initial model hfair hQ L next h budget hb
      s P Ms d R hprep hP hM hD hT p c (hkind p) hp0
  · have hmean : ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] * weight tg initial r.2 ≤ weight tg initial s := by
      exact meanWeight_ordinary_leW tg initial model x s
    calc _ ≤ ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
          (weight tg initial r.2 * potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget +
            b0 * wflag tg initial model (next r.1) (budget - 1) r.2) := by
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
            refine le_trans (h r.1 (budget - 1) r.2 P Ms d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' (minv_blocks hblocks hM) hD
              (totalInvL_ordinary model hT hb x r hr)) (add_le_add ?_ le_rfl)
            exact mul_le_mul_right
              (potH_grow w b0 Fail tg initial hfair.le_one Lmax hext hblocks hland
                (fun q hq => (hP.mem q).1 hq) Ms L d (Nat.sub_le _ _)) _
          · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add]
          refine add_le_add ?_ ?_
          · calc _ = (∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] * weight tg initial r.2) *
                  potH parameter data Qtot w b0 Fail tg initial Lmax s P Ms L d budget := by
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun r => by ring
              _ ≤ _ := mul_le_mul_left hmean _
          · refine le_add_left (le_of_eq ?_)
            simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **Leaf, weighted.** A FORS cover with no decided hit is paid by the potential. -/
theorem goodHWH_pure (hw : w ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R hprep hP hM hD hT
  rw [wflag_pure, mul_zero, add_zero, interp_pure, OracleComp.tsum_prEvent_pure_mul]
  refine mul_le_mul_right ?_ _
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
      unfold potH
      rw [ite_eq_right (by
        rintro (h | h)
        · exact hreal h
        · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
      refine le_trans ?_ le_self_add
      unfold coreH
      refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
      unfold candH
      rw [ite_eq_left (show Unsigned L q from hunsigned)]
      split_ifs
      · exact le_rfl
      · unfold candValueH
        calc (1 : ℝ≥0∞) ≤ witnessFn (pview parameter data s q) d := by
              unfold witnessFn
              rw [hv]
              exact witness_pos_of_covered hD _ hcovered
          _ ≤ _ := base_le_termH hw (witness_props _) s Ms L _ d _ _

/-- Hash computations lifted onto the raw summand are sequences of ordinary queries. -/
theorem goodHWH_liftRaw (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) (L : QueryLog SigningSpec) {α : Type}
    (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ a, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (next a)) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L
      (simulateQ (fun q => liftM (CostSpecH.query (.inl (.inr (.inl q)))) :
        QueryImpl HashSpec (OracleComp CostSpecH)) computation >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact goodHWH_ordinary parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hdigest hfair hQ L
        query _ ih

/-- **One honest signing call, weighted**, on a message that was never signed before: the charged
bounds through the coupling of the honest signer with the charged one. -/
theorem goodHWH_signH (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (m : Message) (L : QueryLog SigningSpec) (hm : MsgLive L m)
    (next : Option Signature → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ r, GoodHW parameter data Qtot w b0 Fail Lmax tg initial model (L ++ [⟨m, r⟩]) (next r)) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (signCostSourceH parameter data m >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hT
  have hsignEq := signCostSourceH_eq parameter data m
  set ℓ := (livePairs L P).length with hℓ
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => wflag tg initial model (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canonH parameter data Qtot w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
  have hproj : ∀ o1 : Run HashInput Coordinate (Option Signature) × State,
      canonR o1 = canonR ((o1.1.1, o1.1.2.1, [], []), o1.2) := fun o1 => by
    simp only [hcanonR, canonH_congr (o := o1) (o' := ((o1.1.1, o1.1.2.1, [], []), o1.2)) rfl rfl]
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
        have hT' : TotalInvL parameter data Qtot (L ++ [⟨m, r⟩]) o1.2 budget := by
          refine totalInvL_append hT fun q hq => ?_
          have hk := other_message_keptS tg initial model B s o1' ho1' q hq firstCall
          rwa [h2] at hk
        have hIH := h r budget o1.2 _ _ _ _ hprep' hP' hM' hD' hT'
        have hpot := sign_pointH2 tg initial model parameter data Qtot w b0 Fail m hparse
          (hfail m) hw B budget s P Ms L d R hprep hP hM hD o1' ho1' r hres' (le_refl budget)
        rw [h2, hdisc, canonH_congr h11 h2] at hpot
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
        · unfold potH
          exact add_le_add hpot hlam
        · simp only [hcont, hres, Option.elim, hbud, le_refl]
  have hflag : ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
      cont o1 ≤ wflag tg initial model (signCostSourceH parameter data m >>= next) budget s := by
    rw [wflag_bind]
    exact le_add_self
  have hcanon : ∑' o1, Pr{let x ← interp tg initial model (signCostSourceH parameter data m) budget s}[x = o1] *
      (weight tg initial o1.2 * canonR o1) ≤
      weight tg initial s * (if Realized tg initial s ∨ signatureLimit < L.length then 0
        else coreH parameter data Qtot w b0 Fail s P Ms L d (signatureLimit - L.length) budget) := by
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
      _ ≤ _ := sign_expectHW2 tg initial model parameter data Qtot w b0 Fail m hparse hkind B budget s P hP Ms L hm d hM hT
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
        unfold potH
        rw [mul_add]
        exact add_le_add (add_le_add hcanon
          (interp_weight_mul_leW tg initial model (signCostSourceH parameter data m) budget s
            (fun _ => lam Lmax ℓ budget) _ fun _ _ => le_rfl)) (mul_le_mul_right hflag _)

theorem goodHWH_finish (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (finishGameH parameter data L forgery) := by
  unfold finishGameH
  exact goodHWH_liftRaw parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hdigest hfair hQ L _ _
    fun v => goodHWH_pure parameter data Qtot w b0 Fail Lmax tg initial model hfair.le_one L forgery v

/-- **The weighted one-coin potential with one heavy message, through any adversary that never
repeats a message**, the signer honest. The coin only pays the rate of a message with at most `Qtot / 2` cached
digests. -/
theorem goodHWH_advProgH (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot / 2 ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodHW parameter data Qtot w b0 Fail Lmax tg initial model L (advProgH parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProgH_pure]
      exact goodHWH_finish parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hdigest hfair hQ L
        forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProgH_draw]
        exact goodHWH_draw parameter data Qtot w b0 Fail Lmax tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProgH_hash]
        exact goodHWH_ordinary parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hdigest hfair hQ
          L bytes _ fun v => ih v L (hnr v)
      · rw [advProgH_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodHWH_signH parameter data Qtot w b0 Fail Lmax tg initial model hparse hkind hfail hfair.le_one
          message L hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end GoodHW

end FORS.Security.ForsPotential
