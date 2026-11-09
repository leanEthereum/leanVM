module

public import FORS.CoverPotential.Groups

@[expose] public section

/-! The FORS potential of the scan signer `R = R0 + i δ`, for adversaries that never request a
signature on the same message twice. A term with base function `f` is forecast by
`creations … (fun I => grpAll s excl (live messages) (virtualOnce … f n I) d) k []`: the future pairs
are independent coins on uniform views, the cached pairs of the messages not yet signed act through
the groups of their messages. A new pair is paid by one future pair (`grpAll_probe`), a signing call
by one fresh slot (`sign_term`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- A monotone and finite base function. -/
def MonoFin (f : Multiset View → ℝ≥0∞) : Prop := Monotone' f ∧ ∀ D, f D ≠ ⊤

theorem witness_props (v : View) : MonoFin (witnessFn v) := ⟨witnessFn_mono v, witnessFn_ne_top v⟩

theorem excess_props (b0 : ℝ≥0∞) : MonoFin (excess b0) := ⟨excess_monoP b0, excess_ne_top b0⟩

section Terms

variable (parameter : PublicParameter) (data : PublicData)

/-- No signing request so far was for the message. -/
def MsgLive (L : QueryLog SigningSpec) (m : Message) : Prop := ∀ entry ∈ L, entry.1 ≠ m

/-- The listed messages that were not signed: their groups are in the future. -/
noncomputable def live (L : QueryLog SigningSpec) (Ms : List Message) : List Message :=
  Ms.filter fun m => decide (MsgLive L m)

/-- Every message with a cached digest is listed. -/
structure MInv (s : State) (Ms : List Message) : Prop where
  nodup : Ms.Nodup
  mem : ∀ m ρ, s.cache (blk parameter data m ρ) ≠ none → m ∈ Ms

/-- The list after a digest query of a message. -/
noncomputable def addMsg (Ms : List Message) (m : Message) : List Message := if m ∈ Ms then Ms else m :: Ms

variable (w : ℝ≥0∞)

/-- The base of a term: the groups of the live messages on the one-coin future of the future pairs. -/
noncomputable def termBase (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (f : Multiset View → ℝ≥0∞) (d : Multiset View) (n : ℕ) (I : List View) : ℝ≥0∞ :=
  grpAll parameter data s excl (live L Ms) (virtualOnce Finset.univ w f n I) d

/-- **The forecast of a term.** -/
noncomputable def termO (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (f : Multiset View → ℝ≥0∞) (d : Multiset View) (n k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (termBase parameter data w s Ms L excl f d n) k []

end Terms

section TermBasic

variable {parameter : PublicParameter} {data : PublicData} {w : ℝ≥0∞}

theorem live_nodup (L : QueryLog SigningSpec) {Ms : List Message} (h : Ms.Nodup) : (live L Ms).Nodup := h.filter _

theorem mem_live {L : QueryLog SigningSpec} {Ms : List Message} {m : Message} :
    m ∈ live L Ms ↔ m ∈ Ms ∧ MsgLive L m := by
  unfold live; simp

theorem termBase_cons (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n : ℕ) (v : View) (I : List View) :
    termBase parameter data w s Ms L excl f d n I ≤ termBase parameter data w s Ms L excl f d n (v :: I) :=
  grpAll_le_of_le s excl (fun e => virtualOnce_le_consM hw hf.1 n I v e) _ d

theorem termBase_perm {f : Multiset View → ℝ≥0∞} (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n : ℕ) (I I' : List View) (h : I.Perm I') :
    termBase parameter data w s Ms L excl f d n I = termBase parameter data w s Ms L excl f d n I' :=
  grpAll_congr s excl (fun e => virtualOnce_perm n h e) _ d

/-- More future pairs, a larger forecast. -/
theorem termO_mono (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    termO parameter data w s Ms L excl f d n k ≤ termO parameter data w s Ms L excl f d n k' :=
  creations_mono_count Finset.univ_nonempty landing_le_one (termBase_cons hw hf s Ms L excl d n)
    (termBase_perm s Ms L excl d n) hk []

/-- The base value is below its forecast. -/
theorem base_le_termO (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n k : ℕ) :
    f d ≤ termO parameter data w s Ms L excl f d n k := by
  calc f d ≤ virtualOnce Finset.univ w f n [] d := base_le_virtualOnceM Finset.univ_nonempty hw hf.1 n [] d
    _ ≤ termBase parameter data w s Ms L excl f d n [] := le_grpAll s excl (virtualOnce_mono hf.1 n []) _ d
    _ ≤ _ := termO_mono hw hf s Ms L excl d n (Nat.zero_le k)

/-- Excluding more pairs lowers the forecast. -/
theorem grpAll_excl_mono (s : State) {excl excl' : Pair → Prop} (h : ∀ q, excl q → excl' q)
    {F : Multiset View → ℝ≥0∞} (hF : Monotone' F) :
    ∀ (Ms : List Message) (d : Multiset View),
      grpAll parameter data s excl' Ms F d ≤ grpAll parameter data s excl Ms F d
  | [], _ => le_rfl
  | m :: Ms, d => by
      simp only [grpAll, grpM]
      refine le_trans (grp_le_of_le _ _ (grpAll_excl_mono s h hF Ms) d) ?_
      refine grp_ext_mono _ (fun ρ => ?_) (grpAll_mono s excl hF Ms) d
      unfold extOf
      by_cases hx : excl (m, ρ)
      · rw [ite_eq_left hx, ite_eq_left (h _ hx)]
      · rw [ite_eq_right hx]
        split_ifs
        · exact bot_le
        · exact le_rfl

theorem termO_excl_mono {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) {excl excl' : Pair → Prop} (h : ∀ q, excl q → excl' q) (d : Multiset View) (n k : ℕ) :
    termO parameter data w s Ms L excl' f d n k ≤ termO parameter data w s Ms L excl f d n k :=
  creations_mono (fun I => grpAll_excl_mono s h (virtualOnce_mono hf.1 n I) _ d) k []

/-- A new candidate's forecast is at most the baseline plus one excess. -/
theorem fresh_forecastO (hw : w ≤ 1) (b0 : ℝ≥0∞) (s : State) (Ms : List Message) (L : QueryLog SigningSpec)
    (excl : Pair → Prop) (d : Multiset View) (n k : ℕ) :
    landing * freshAvg Finset.univ (fun v => termO parameter data w s Ms L excl (witnessFn v) d n k) ≤
      b0 + termO parameter data w s Ms L excl (excess b0) d n k := by
  have hU : (Finset.univ : Finset View).Nonempty := Finset.univ_nonempty
  unfold termO
  rw [← creations_freshAvg, ← creations_const_mul]
  have hpt : ∀ J, landing * freshAvg Finset.univ (fun v => termBase parameter data w s Ms L excl (witnessFn v) d n J) ≤
      b0 + termBase parameter data w s Ms L excl (excess b0) d n J := by
    intro J
    unfold termBase
    rw [← grpAll_freshAvg, ← grpAll_const_mul]
    calc grpAll parameter data s excl (live L Ms)
          (fun e => landing * freshAvg Finset.univ fun v => virtualOnce Finset.univ w (witnessFn v) n J e) d
        ≤ grpAll parameter data s excl (live L Ms)
          (fun e => b0 + virtualOnce Finset.univ w (excess b0) n J e) d := by
          refine grpAll_le_of_le s excl (fun e => ?_) _ d
          rw [← virtualOnce_freshAvg hU, ← virtualOnce_const_mul]
          calc virtualOnce Finset.univ w (fun D => landing * freshAvg Finset.univ fun v => witnessFn v D) n J e
              ≤ virtualOnce Finset.univ w (fun D => b0 + excess b0 D) n J e :=
                virtualOnce_mono_base (fun D => show price D ≤ b0 + (price D - b0) from le_add_tsub) n J e
            _ = b0 + virtualOnce Finset.univ w (excess b0) n J e := by
                rw [virtualOnce_add hU (fun _ => b0) (excess b0), virtualOnce_const hU hw]
      _ = _ := by
          rw [grpAll_add s excl (fun _ => b0), grpAll_const]
  calc creations Finset.univ landing (fun J => landing * freshAvg Finset.univ fun v =>
        termBase parameter data w s Ms L excl (witnessFn v) d n J) k []
      ≤ creations Finset.univ landing (fun J => b0 + termBase parameter data w s Ms L excl (excess b0) d n J) k [] :=
        creations_mono hpt k []
    _ = _ := by rw [creations_add (fun _ => b0), creations_const Finset.univ_nonempty landing_le_one]

end TermBasic

/-! ### A new pair, one term -/

section NewPairTerm

variable (parameter : PublicParameter) (data : PublicData)

/-- The coin `w` pays the creation rate of the scan signer through the mass that the group of the
message leaves on the identity. -/
def Rate (w : ℝ≥0∞) (s : State) (m : Message) : Prop :=
  (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ((1 - landing) + 1) ≤ landing * w * idMassM parameter data s m

variable {parameter data} {w : ℝ≥0∞}

theorem addMsg_nodup {Ms : List Message} (h : Ms.Nodup) (m : Message) : (addMsg Ms m).Nodup := by
  unfold addMsg
  split_ifs with hm
  · exact h
  · exact List.nodup_cons.2 ⟨hm, h⟩

theorem mem_addMsg_self (Ms : List Message) (m : Message) : m ∈ addMsg Ms m := by
  unfold addMsg
  split_ifs with hm
  · exact hm
  · exact List.mem_cons_self ..

theorem mem_addMsg_of_mem {Ms : List Message} {m m' : Message} (h : m' ∈ Ms) : m' ∈ addMsg Ms m := by
  unfold addMsg
  split_ifs
  · exact h
  · exact List.mem_cons_of_mem _ h

/-- Listing one more message does not change the groups: it has no cached digest yet. -/
theorem grpAll_addMsg {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) (L : QueryLog SigningSpec)
    (excl : Pair → Prop) (m : Message) (F : Multiset View → ℝ≥0∞) (d : Multiset View) :
    grpAll parameter data s excl (live L (addMsg Ms m)) F d = grpAll parameter data s excl (live L Ms) F d := by
  unfold addMsg
  split_ifs with hm
  · rfl
  · have hun : ∀ ρ, s.cache (blk parameter data m ρ) = none := by
      intro ρ
      by_contra h
      exact hm (hM.mem m ρ h)
    unfold live
    rw [List.filter_cons]
    split_ifs
    · exact grpM_untouched s excl m hun _ d
    · rfl

theorem termO_addMsg {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) (L : QueryLog SigningSpec)
    (excl : Pair → Prop) (m : Message) (f : Multiset View → ℝ≥0∞) (d : Multiset View) (n k : ℕ) :
    termO parameter data w s (addMsg Ms m) L excl f d n k = termO parameter data w s Ms L excl f d n k := by
  unfold termO
  congr 1
  funext I
  exact grpAll_addMsg hM L excl m _ d

/-- The listed messages after a new pair. -/
theorem minv_withPair {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) (p : Pair) (u : DigestCall → HashOutput) :
    MInv parameter data (withPair parameter data s p u) (addMsg Ms p.1) := by
  refine ⟨addMsg_nodup hM.nodup _, fun m ρ h => ?_⟩
  by_cases hq : (m, ρ) = p
  · rw [← hq]; exact mem_addMsg_self _ _
  · have h' : (withPair parameter data s p u).cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ) :=
      withPair_other_pair s p (m, ρ) hq u firstCall
    rw [h'] at h
    exact mem_addMsg_of_mem (hM.mem m ρ h)

/-- **A new pair, one term.** In the mean the forecast of a term after the block of a new pair is at
most its forecast with one more future pair. -/
theorem termO_newPair (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) (p : Pair) (hp0 : s.cache (pblk parameter data p firstCall) = none)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (hrate : MsgLive L p.1 → Rate parameter data w s p.1)
    (d : Multiset View) (n k : ℕ) :
    pairE (fun u => termO parameter data w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n k) ≤
      termO parameter data w s Ms L excl f d n (k + 1) := by
  rw [← termO_addMsg hM L excl p.1 f d n (k + 1)]
  set Ms' := addMsg Ms p.1 with hMs'
  have hnd : (live L Ms').Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  by_cases hlive : MsgLive L p.1
  · have hmem : p.1 ∈ live L Ms' := mem_live.2 ⟨mem_addMsg_self _ _, hlive⟩
    unfold termO pairE
    rw [creations_tsum, ← creations_one]
    refine creations_mono (fun I => ?_) k []
    exact grpAll_probe hw hf.1 hf.2 s p hp0 excl (live L Ms') hnd hmem (hrate hlive) n I d
  · have hnot : p.1 ∉ live L Ms' := fun h => hlive (mem_live.1 h).2
    have hsame : ∀ u, termO parameter data w (withPair parameter data s p u) Ms' L excl f d n k =
        termO parameter data w s Ms' L excl f d n k := by
      intro u
      unfold termO
      congr 1
      funext I
      exact grpAll_withPair_other s p u excl _ _ hnot d
    simp only [hsame, pairE_const]
    exact termO_mono hw hf s Ms' L excl d n (Nat.le_succ k)

/-- **The new candidate.** A new landed pair that is excluded stops the walks of its message
without disclosing anything: its forecast in the new state is at most its forecast in the old one. -/
theorem termO_stop {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) (p : Pair) (hp0 : s.cache (pblk parameter data p firstCall) = none)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (hx : excl p) (u : DigestCall → HashOutput)
    (hl : Landed parameter (blockIndex (u firstCall))) (d : Multiset View) (n k : ℕ) :
    termO parameter data w (withPair parameter data s p u) (addMsg Ms p.1) L excl f d n k ≤
      termO parameter data w s Ms L excl f d n k := by
  rw [← termO_addMsg hM L excl p.1 f d n k]
  set Ms' := addMsg Ms p.1 with hMs'
  have hnd : (live L Ms').Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  unfold termO
  refine creations_mono (fun I => ?_) k []
  unfold termBase
  by_cases hmem : p.1 ∈ live L Ms'
  · set rest := (live L Ms').erase p.1 with hrest
    have hperm : (live L Ms').Perm (p.1 :: rest) := List.perm_cons_erase hmem
    have hnot : p.1 ∉ rest := fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl
    have hst : stOf parameter data p.1 s p.2 = .fresh := by
      have h : s.cache (blk parameter data p.1 p.2) = none := hp0
      simp [stOf, h]
    rw [grpAll_perm _ excl _ hperm d, grpAll_perm _ excl _ hperm d]
    simp only [grpAll]
    rw [grpM_withPair_self, ite_eq_left hl, ite_eq_left hx,
      grp_congr _ _ (fun e => grpAll_withPair_other s p u excl (virtualOnce Finset.univ w f n I) rest hnot e) d]
    exact grp_stop_le landing_le_one Finset.univ_nonempty _ _
      (grpAll_mono s excl (virtualOnce_mono hf.1 n I) rest) d p.2 hst
  · exact le_of_eq (grpAll_withPair_other s p u excl _ _ hmem d)

end NewPairTerm

/-! ### The potential -/

section DefsO

variable (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The forecast of a candidate: its own pair discloses nothing for it. -/
noncomputable def candValueO (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  termO parameter data w s Ms L (· = p) (witnessFn (pview parameter data s p)) d n k

/-- The excess forecast of a new pair. -/
noncomputable def hValueO (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  termO parameter data w s Ms L (fun _ => False) (excess b0) d n k

/-- The value of a candidate: one at a failing index, its forecast otherwise; zero once signed. -/
noncomputable def candO (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (p : Pair) : ℝ≥0∞ :=
  if Unsigned L p then
    (if (pview parameter data s p).1 ∈ Fail then 1 else candValueO parameter data w s Ms L d n k p)
  else 0

/-- The potential without the hit and transcript tests. -/
noncomputable def coreO (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (n k : ℕ) : ℝ≥0∞ :=
  (P.map (candO parameter data w Fail s Ms L d n k)).sum +
    k * (hValueO parameter data w b0 s Ms L d n k + failMass Fail) + n * failMass Fail

/-- The cached landed pairs of the messages that were not signed. -/
noncomputable def livePairs (L : QueryLog SigningSpec) (P : List Pair) : List Pair :=
  P.filter fun q => decide (MsgLive L q.1)

/-- **The cap on the landed pairs** as an exact martingale: it is at least one as soon as `Lmax`
pairs of unsigned messages landed, and a new pair keeps its mean. -/
noncomputable def lam (Lmax ℓ k : ℕ) : ℝ≥0∞ :=
  ((65 : ℝ≥0∞) / 64) ^ ℓ * (1 + landing / 64) ^ k * ((64 : ℝ≥0∞) / 65) ^ Lmax

variable (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- **The potential.** -/
noncomputable def potO (Lmax : ℕ) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  (if Realized tg initial s ∨ signatureLimit < L.length then 0
    else coreO parameter data w b0 Fail s P Ms L d (signatureLimit - L.length) k) +
  lam Lmax (livePairs L P).length k

/-- **The fair-rate hypotheses of the scan signer.** With at most `Cmax` cached digests and `Lmax`
cached landed pairs of a message, the coin `w` pays `(2 − landing)/2^128` through the mass that the
group leaves on the identity. -/
structure FairS (Cmax Lmax : ℕ) : Prop where
  le_one : w ≤ 1
  rate : (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ((1 - landing) + 1) ≤
    w * (landing - (landing * (Cmax * (Fintype.card Randomness : ℝ≥0∞)⁻¹) +
      Lmax * (1 - landing) * (Fintype.card Randomness : ℝ≥0∞)⁻¹))

end DefsO

section Cap

variable {parameter : PublicParameter} {data : PublicData} {w : ℝ≥0∞}

theorem ratio_mul : ((65 : ℝ≥0∞) / 64) * ((64 : ℝ≥0∞) / 65) = 1 := by
  rw [← mul_div_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num),
    ENNReal.div_self (by norm_num) (by norm_num)]

theorem one_le_ratio : (1 : ℝ≥0∞) ≤ (65 : ℝ≥0∞) / 64 := by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num

/-- As many landed pairs as the cap: the cap term is at least one. -/
theorem one_le_lam {Lmax ℓ : ℕ} (h : Lmax ≤ ℓ) (k : ℕ) : 1 ≤ lam Lmax ℓ k := by
  unfold lam
  have h1 : (1 : ℝ≥0∞) ≤ (1 + landing / 64) ^ k := one_le_pow₀ le_self_add
  obtain ⟨e, he⟩ : ∃ e, ℓ = Lmax + e := ⟨ℓ - Lmax, by omega⟩
  rw [he, pow_add]
  calc (1 : ℝ≥0∞) = 1 * 1 * 1 := by simp
    _ ≤ ((65 : ℝ≥0∞) / 64) ^ e * (1 + landing / 64) ^ k * (((65 : ℝ≥0∞) / 64) ^ Lmax * ((64 : ℝ≥0∞) / 65) ^ Lmax) := by
        rw [← mul_pow, ratio_mul, one_pow]
        gcongr
        exact one_le_pow₀ one_le_ratio
    _ = _ := by ring

theorem lam_mono {Lmax ℓ ℓ' k k' : ℕ} (hℓ : ℓ ≤ ℓ') (hk : k ≤ k') :
    lam Lmax ℓ k ≤ lam Lmax ℓ' k' := by
  unfold lam
  gcongr
  · exact one_le_ratio
  · exact le_self_add

/-- **The cap term is a martingale under a new pair.** -/
theorem lam_newPair (parameter : PublicParameter) (Lmax ℓ k : ℕ) :
    pairE (fun u => if Landed parameter (blockIndex (u firstCall)) then lam Lmax (ℓ + 1) k else lam Lmax ℓ k) =
      lam Lmax ℓ (k + 1) := by
  have h := pairE_landed parameter (fun _ => lam Lmax (ℓ + 1) k) (lam Lmax ℓ k)
  rw [freshAvg_const _ Finset.univ_nonempty] at h
  rw [h]
  unfold lam
  have hstep : landing * ((65 : ℝ≥0∞) / 64) + (1 - landing) = 1 + landing / 64 := by
    have h65 : ((65 : ℝ≥0∞) / 64) = 1 + 1 / 64 := by
      rw [show (65 : ℝ≥0∞) = 64 + 1 by norm_num, ENNReal.add_div, ENNReal.div_self (by norm_num) (by norm_num)]
    rw [h65, mul_add, mul_one, add_right_comm, add_tsub_cancel_of_le landing_le_one, mul_one_div]
  calc landing * (((65 : ℝ≥0∞) / 64) ^ (ℓ + 1) * (1 + landing / 64) ^ k * ((64 : ℝ≥0∞) / 65) ^ Lmax) +
        (1 - landing) * (((65 : ℝ≥0∞) / 64) ^ ℓ * (1 + landing / 64) ^ k * ((64 : ℝ≥0∞) / 65) ^ Lmax)
      = ((65 : ℝ≥0∞) / 64) ^ ℓ * (1 + landing / 64) ^ k * ((64 : ℝ≥0∞) / 65) ^ Lmax *
          (landing * ((65 : ℝ≥0∞) / 64) + (1 - landing)) := by
        rw [pow_succ]
        ring
    _ = _ := by rw [hstep, pow_succ]; ring

/-- The cached landed pairs of an unsigned message are live items. -/
theorem landedCount_le {s : State} {P : List Pair} (hP : PInv parameter data s P) (L : QueryLog SigningSpec)
    {m : Message} (hm : MsgLive L m) :
    landedCount parameter data m s ≤ (livePairs L P).length := by
  classical
  unfold landedCount
  have hnd : (livePairs L P).Nodup := hP.nodup.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card_of_injOn (fun ρ => (m, ρ)) (fun ρ hρ => ?_) (fun a _ b _ h => (Prod.ext_iff.1 h).2)
  rw [Finset.mem_coe, Finset.mem_filter] at hρ
  refine Finset.mem_coe.2 (List.mem_toFinset.2 ?_)
  unfold livePairs
  exact List.mem_filter.2 ⟨(hP.mem (m, ρ)).2 hρ.2, by simpa using hm⟩

/-- **The rate from the counts.** -/
theorem rate_of_fair {Cmax Lmax : ℕ} (hfair : FairS w Cmax Lmax) (s : State) (m : Message)
    (hC : cachedCount parameter data m s ≤ Cmax) (hL : landedCount parameter data m s ≤ Lmax) :
    Rate parameter data w s m := by
  classical
  unfold Rate
  refine le_trans hfair.rate ?_
  rw [show landing * w * idMassM parameter data s m = w * (landing * idMassM parameter data s m) by ring]
  refine mul_le_mul' le_rfl ?_
  have hid := idMass_ge (σ := (nextRand (data.steps m))) (p := landing) (A := digestAttemptLimit) landing_le_one
    (stOf parameter data m s)
    (fun x j h0 hj => nextRand_pow_ne (data.steps m) x j h0 (lt_trans hj (by unfold digestAttemptLimit; norm_num)))
  have hcc : (Finset.univ.filter fun r => stOf parameter data m s r ≠ .fresh).card = cachedCount parameter data m s := by
    unfold cachedCount
    refine congrArg Finset.card (Finset.filter_congr fun ρ _ => ?_)
    simp only [stOf]
    cases s.cache (blk parameter data m ρ) with
    | none => simp
    | some u0 => by_cases hl : Landed parameter (blockIndex u0) <;> simp [hl]
  have hlc : (Finset.univ.filter fun r => stOf parameter data m s r = .hit).card = landedCount parameter data m s := by
    unfold landedCount
    refine congrArg Finset.card (Finset.filter_congr fun ρ _ => ?_)
    simp only [stOf]
    cases s.cache (blk parameter data m ρ) with
    | none => simp
    | some u0 => by_cases hl : Landed parameter (blockIndex u0) <;> simp [hl]
  rw [hcc, hlc] at hid
  rw [tsub_le_iff_right]
  refine le_trans hid ?_
  unfold idMassM
  rw [add_assoc]
  gcongr

end Cap

/-! ### A new pair -/

section NewPairO

variable {parameter : PublicParameter} {data : PublicData} (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem candO_mono (hw : w ≤ 1) (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (p : Pair) :
    candO parameter data w Fail s Ms L d n k p ≤ candO parameter data w Fail s Ms L d n k' p := by
  unfold candO candValueO
  split_ifs
  · exact le_rfl
  · exact termO_mono hw (witness_props _) s Ms L _ d n hk
  · exact le_rfl

theorem hValueO_mono (hw : w ≤ 1) (s : State) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    hValueO parameter data w b0 s Ms L d n k ≤ hValueO parameter data w b0 s Ms L d n k' :=
  termO_mono hw (excess_props b0) s Ms L _ d n hk

theorem coreO_mono (hw : w ≤ 1) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    coreO parameter data w b0 Fail s P Ms L d n k ≤ coreO parameter data w b0 Fail s P Ms L d n k' := by
  unfold coreO
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => candO_mono w Fail hw s Ms L d n hk q) ?_) le_rfl
  exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValueO_mono w b0 hw s Ms L d n hk) le_rfl)

/-- **A new pair.** Touching a new pair costs one future pair and at most the baseline. -/
theorem coreO_newPair (hw : w ≤ 1) {s : State} {P : List Pair} {Ms : List Message}
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) {p : Pair}
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec)
    (hrate : MsgLive L p.1 → Rate parameter data w s p.1) (d : Multiset View) (n k : ℕ) :
    pairE (fun u => coreO parameter data w b0 Fail (withPair parameter data s p u)
      (addPair parameter P p u) (addMsg Ms p.1) L d n k) ≤
      coreO parameter data w b0 Fail s P Ms L d n (k + 1) + b0 := by
  set Ms' := addMsg Ms p.1 with hMs'
  set φ := failMass Fail with hφ
  have hpP := not_mem_of_fresh hP hp0
  set Wp : View → ℝ≥0∞ := fun v => termO parameter data w s Ms L (· = p) (witnessFn v) d n k with hWp
  set H := hValueO parameter data w b0 s Ms L d n (k + 1) with hH
  set S := (P.map (candO parameter data w Fail s Ms L d n (k + 1))).sum with hS
  -- the candidates of the old pairs
  have h2 : ∀ q ∈ P, pairE (fun u => candO parameter data w Fail (withPair parameter data s p u) Ms' L d n k q) ≤
      candO parameter data w Fail s Ms L d n (k + 1) q := by
    intro q hq
    have hqp : q ≠ p := fun h => hpP (h ▸ hq)
    have hv : ∀ u, pview parameter data (withPair parameter data s p u) q = pview parameter data s q :=
      fun u => pview_withPair_other s p q hqp u
    unfold candO candValueO
    simp only [hv]
    split_ifs
    · simp only [pairE_const, le_refl]
    · exact termO_newPair hw (witness_props _) hM p hp0 L _ hrate d n k
    · simp only [pairE_const, le_refl]
  -- the candidate of the new pair
  have hnew : ∀ u, Landed parameter (blockIndex (u firstCall)) →
      candO parameter data w Fail (withPair parameter data s p u) Ms' L d n k p ≤
        (if (viewOf u).1 ∈ Fail then 1 else 0) + Wp (viewOf u) := by
    intro u hl
    unfold candO candValueO
    rw [pview_withPair_self]
    by_cases hu : Unsigned L p
    · rw [ite_eq_left hu]
      by_cases hF : (viewOf u).1 ∈ Fail
      · rw [ite_eq_left hF, ite_eq_left hF]
        exact le_self_add
      · rw [ite_eq_right hF, ite_eq_right hF, zero_add]
        exact termO_stop (witness_props _) hM p hp0 L (· = p) rfl u hl d n k
    · rw [ite_eq_right hu]
      exact bot_le
  have hpoint : ∀ u, coreO parameter data w b0 Fail (withPair parameter data s p u)
      (addPair parameter P p u) Ms' L d n k ≤
      ((if Landed parameter (blockIndex (u firstCall)) then (fun v : View => (if v.1 ∈ Fail then 1 else 0) + Wp v) (viewOf u)
          else 0) +
        (P.map fun q => candO parameter data w Fail (withPair parameter data s p u) Ms' L d n k q).sum) +
      k * (hValueO parameter data w b0 (withPair parameter data s p u) Ms' L d n k + φ) + n * φ := by
    intro u
    unfold coreO
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
  have h3 : pairE (fun u => hValueO parameter data w b0 (withPair parameter data s p u) Ms' L d n k) ≤ H :=
    termO_newPair hw (excess_props b0) hM p hp0 L _ hrate d n k
  have hfresh : landing * freshAvg Finset.univ Wp ≤ b0 + H := by
    refine le_trans (fresh_forecastO hw b0 s Ms L (· = p) d n k) (add_le_add le_rfl ?_)
    refine le_trans (termO_excl_mono (excess_props b0) s Ms L (fun _ h => False.elim h) d n k) ?_
    exact hValueO_mono w b0 hw s Ms L d n (Nat.le_succ k)
  have hφ1 : landing * φ ≤ φ := mul_le_of_le_one_left' landing_le_one
  have hSle : (P.map fun q => pairE fun u => candO parameter data w Fail (withPair parameter data s p u) Ms' L d n k q).sum ≤
      S := List.sum_le_sum fun q hq => h2 q hq
  rw [h1]
  unfold coreO
  calc landing * (φ + freshAvg Finset.univ Wp) +
        (P.map fun q => pairE fun u => candO parameter data w Fail (withPair parameter data s p u) Ms' L d n k q).sum +
        k * (pairE (fun u => hValueO parameter data w b0 (withPair parameter data s p u) Ms' L d n k) + φ) + n * φ
      ≤ φ + (b0 + H) + S + k * (H + φ) + n * φ := by
        rw [mul_add]
        gcongr
    _ = S + ((k : ℝ≥0∞) + 1) * (H + φ) + n * φ + b0 := by ring
    _ = _ := by push_cast; ring

end NewPairO

/-! ### Order and congruence -/

section OrderO

variable {parameter : PublicParameter} {data : PublicData} (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- Without a new pair, an ordinary query keeps every index block. A later call of a pair whose
index block is cached but did not land may be new, so only the index blocks are kept. -/
theorem same_blocks {x : HashInput} {s s' : State} (hext : Extends s s') (hother : ∀ y, y ≠ x → s'.cache y = s.cache y)
    (hnot : ¬∃ (p : Pair) (call : DigestCall), x = pblk parameter data p call ∧
      s.cache (pblk parameter data p firstCall) = none) (q : Pair) :
    s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall) := by
  by_cases hx : x = pblk parameter data q firstCall
  · by_cases hn : s.cache (pblk parameter data q firstCall) = none
    · exact absurd ⟨q, firstCall, hx, hn⟩ hnot
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hn
      rw [hv]; exact hext.1 _ v hv
  · exact hother _ (Ne.symm hx)

/-- A landed pair keeps every one of its blocks in a grown state. -/
theorem landed_blocks {s s' : State} (hext : Extends s s') {P : List Pair}
    (hP : PInv parameter data s P) {q : Pair} (hq : LandedIn parameter data s q) (call : DigestCall) :
    s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hP.all q hq call)
  rw [hv]; exact hext.1 _ v hv

/-- The groups see the state only through the index blocks and the views of the landed pairs: the
disclosure of a group is read at its hits alone. -/
theorem grpAll_blocks {s s' : State}
    (h : ∀ q, s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall))
    (hv : ∀ q, LandedIn parameter data s q → ∀ call,
      s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call))
    (excl : Pair → Prop) (F : Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message) (d : Multiset View), grpAll parameter data s' excl Ms F d = grpAll parameter data s excl Ms F d
  | [], _ => rfl
  | m :: Ms, d => by
      have hst : stOf parameter data m s' = stOf parameter data m s := by
        funext ρ
        have := h (m, ρ)
        simp only [stOf]
        rw [show s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ) from this]
      have hx : ∀ ρ, stOf parameter data m s ρ = .hit →
          extOf parameter data s' excl m ρ = extOf parameter data s excl m ρ := by
        intro ρ hρ
        unfold extOf
        rw [pview_congr parameter data (hv (m, ρ) (landedIn_of_stOf_hit hρ))]
      simp only [grpAll, grpM]
      rw [grp_congr _ _ (fun e => grpAll_blocks h hv excl F Ms e) d, hst]
      exact grp_congr_ext _ hx _ d

theorem termO_blocks {s s' : State}
    (h : ∀ q, s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall))
    (hv : ∀ q, LandedIn parameter data s q → ∀ call,
      s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call))
    (Ms : List Message) (L : QueryLog SigningSpec) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞) (d : Multiset View)
    (n k : ℕ) : termO parameter data w s' Ms L excl f d n k = termO parameter data w s Ms L excl f d n k := by
  unfold termO
  congr 1
  funext I
  exact grpAll_blocks h hv excl _ _ d

theorem coreO_blocks {s s' : State}
    (h : ∀ q, s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall))
    (hv : ∀ q, LandedIn parameter data s q → ∀ call,
      s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call))
    {P : List Pair} (hPl : ∀ q ∈ P, LandedIn parameter data s q)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    coreO parameter data w b0 Fail s' P Ms L d n k = coreO parameter data w b0 Fail s P Ms L d n k := by
  have hpv : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q :=
    fun q hq => pview_congr parameter data (hv q (hPl q hq))
  unfold coreO hValueO candO candValueO
  rw [termO_blocks w h hv, List.map_congr_left fun q hq => by rw [hpv q hq, termO_blocks w h hv]]

theorem minv_blocks {s s' : State}
    (h : ∀ q, s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall))
    {Ms : List Message} (hM : MInv parameter data s Ms) : MInv parameter data s' Ms :=
  ⟨hM.nodup, fun m ρ hne => hM.mem m ρ (by
    have h' : s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ) := h (m, ρ)
    rw [← h']
    exact hne)⟩

variable (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- A grown state with the same digest blocks has no larger potential. -/
theorem potO_grow (hw : w ≤ 1) (Lmax : ℕ) {s s' : State} (hext : Extends s s')
    (h : ∀ q, s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall))
    (hv : ∀ q, LandedIn parameter data s q → ∀ call,
      s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call))
    {P : List Pair} (hPl : ∀ q ∈ P, LandedIn parameter data s q)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    potO parameter data w b0 Fail tg initial Lmax s' P Ms L d k ≤ potO parameter data w b0 Fail tg initial Lmax s P Ms L d k' := by
  unfold potO
  refine add_le_add ?_ (lam_mono le_rfl hk)
  by_cases hr : Realized tg initial s' ∨ signatureLimit < L.length
  · rw [ite_eq_left hr]; exact bot_le
  · have hr' : ¬(Realized tg initial s ∨ signatureLimit < L.length) := fun h' =>
      hr (h'.imp (realized_of_extends tg initial hext) id)
    rw [ite_eq_right hr, ite_eq_right hr', coreO_blocks w b0 Fail h hv hPl]
    exact coreO_mono w b0 Fail hw s P Ms L d _ hk

end OrderO

/-! ### Paid programs -/

section GoodO

variable (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A program whose final value is paid by the potential and the baseline payments. -/
def GoodO (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → MInv parameter data s Ms → DInv R d →
      CountInv parameter data Qtot s budget →
      ∑' out, Pr{let x ← interp tg initial model prog budget s}[x = out] * finalValue parameter data tg initial R out ≤
        potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * expectedFlagged tg initial model prog budget s

/-- The cover of a forgery only needs cached blocks, so it survives a growing cache. -/
theorem forsCover_mono (parameter : PublicParameter) (root : Digest) (outcome : HiddenBridge.Outcome)
    (reveals : List Coordinate) {cc cc' : QueryCache HashSpec} (hgrow : ∀ x v, cc x = some v → cc' x = some v)
    (hc : HiddenBridge.ForsCover parameter root outcome reveals cc) :
    HiddenBridge.ForsCover parameter root outcome reveals cc' := by
  obtain ⟨hvalid, digest, hdig, hrest⟩ := hc
  refine ⟨hvalid, digest, ?_, hrest⟩
  unfold HiddenBridge.cachedDigest at hdig ⊢
  cases hall : Completeness.allSome (α := fun _ => HashOutput) (fun call : DigestCall =>
      cc (messageDigestInput parameter root outcome.1.message outcome.1.signature.randomness call)) with
  | none => rw [hall] at hdig; cases hdig
  | some u =>
      rw [allSome_of_eq _ u fun call => hgrow _ _ (HiddenBridge.allSome_some hall call)]
      rw [hall] at hdig
      exact hdig

/-- **Leaf.** A FORS cover with no decided hit is paid by the potential. -/
theorem goodO_pure (hw : w ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodO parameter data w b0 Fail Qtot Lmax tg initial model L (pure (forgery, L, verified)) := by
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

end GoodO

/-! ### Signing a message for the first time -/

section SignState

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (m : Message)

variable {parameter data m}

theorem other_message_keptS (budget : ℕ) (s : State)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) budget s))
    (q : Pair) (hq : q.1 ≠ m) (call : DigestCall) :
    out.2.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) := by
  refine interp_avoids_cache tg initial model _ _ (avoids_source parameter data m) budget s out hout _ ⟨?_, ?_⟩
  · exact msgInput_digestInput parameter data.root q.1 q.2 call
  · intro ρ call' h
    exact hq (congrArg Prod.fst
      (pblk_injective parameter data
        (show pblk parameter data q call = pblk parameter data (m, ρ) call' from h)).1)

/-- **The state after a signing call.** -/
theorem sign_paramsS (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate)
    (hprep : Prepared initial s) (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) :
    Prepared initial out.2 ∧ PInv parameter data out.2 (newPairs parameter data m s out.2 ++ P) ∧
      MInv parameter data out.2 (addMsg Ms m) ∧
      DInv (R ++ out.1.2.1) (discAfter parameter data m s d out) ∧
      CountInv parameter data Qtot out.2 (budget - traceCost out.1.2.2.1) ∧
      (∀ q ∈ P, pview parameter data out.2 q = pview parameter data s q) := by
  have hext := interp_extends tg initial model _ budget s out hout
  have hpinv : PairInv parameter data m out.2 :=
    source_pairInv tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) budget s
      (pairInv_of_pinv hP m) out hout r hr
  have hpost := source_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
    budget s hprep out hout r hr
  have hother := other_message_keptS tg initial model budget s out hout
  have hgrow : ∀ (q : Pair) (call : DigestCall) (u : HashOutput),
      s.cache (pblk parameter data q call) = some u →
      out.2.cache (pblk parameter data q call) = some u := fun q call u h => hext.1 _ u h
  refine ⟨fun x v hx => hext.1 x v (hprep x v hx),
    ⟨?_, fun q => ?_, fun q hq call => ?_, fun q hq call => ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine List.nodup_append.2 ⟨newPairs_nodup parameter data m s out.2, hP.nodup, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨_, h0, _⟩ := (mem_newPairs parameter data m s).1 ha
    obtain ⟨u, hu, _⟩ := (hP.mem a).1 hb
    rw [h0] at hu; cases hu
  · rw [List.mem_append, mem_newPairs]
    constructor
    · rintro (⟨_, _, hl⟩ | hq)
      · exact hl
      · obtain ⟨u0, h0, hl⟩ := (hP.mem q).1 hq
        exact ⟨u0, hgrow q firstCall u0 h0, hl⟩
    · rintro ⟨u0, h0, hl⟩
      cases hs0 : s.cache (pblk parameter data q firstCall) with
      | none =>
          left
          refine ⟨?_, rfl, ⟨u0, h0, hl⟩⟩
          by_contra hm
          rw [hother q hm firstCall, hs0] at h0
          cases h0
      | some u =>
          right
          have := hgrow q firstCall u hs0
          rw [h0] at this
          cases this
          exact (hP.mem q).2 ⟨u0, hs0, hl⟩
  · -- a landed pair of `out.2` has every block
    obtain ⟨u0, h0, hl⟩ := hq
    by_cases hm : q.1 = m
    · obtain ⟨q1, q2⟩ := q
      simp only at hm
      subst hm
      exact Option.ne_none_iff_isSome.2 ((hpinv q2).2 u0 h0 hl call)
    · have hland : LandedIn parameter data s q := ⟨u0, by rw [← hother q hm firstCall]; exact h0, hl⟩
      rw [hother q hm call]
      exact hP.all q hland call
  · -- a pair of `out.2` without its index block has no block
    by_cases hm : q.1 = m
    · obtain ⟨q1, q2⟩ := q
      simp only at hm
      subst hm
      exact (hpinv q2).1 hq call
    · rw [hother q hm call]
      rw [hother q hm firstCall] at hq
      exact hP.first q hq call
  · refine ⟨addMsg_nodup hM.nodup _, fun m' ρ hne => ?_⟩
    by_cases hm' : m' = m
    · rw [hm']; exact mem_addMsg_self _ _
    · have hk : out.2.cache (blk parameter data m' ρ) = s.cache (blk parameter data m' ρ) :=
        hother (m', ρ) hm' firstCall
      rw [hk] at hne
      exact mem_addMsg_of_mem (hM.mem m' ρ hne)
  · -- every revealed FORS coordinate has a disclosed view
    intro i κ l q hmem
    rcases List.mem_append.1 hmem with hR | hrev
    · obtain ⟨v, hv, h1⟩ := hD i κ l q hR
      exact ⟨v, Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl hv))), h1⟩
    · rcases hpost with ⟨_, hnil, _⟩ | ⟨ρs, u, hsel, hfors, hsig, hfl⟩
      · rw [hnil] at hrev; cases hrev
      · obtain ⟨hi, hleaf⟩ := hfors _ hrev i κ l q rfl
        refine ⟨viewOf u, ?_, by rw [hi]; rfl, by rw [hleaf]; rfl⟩
        have hv : pview parameter data out.2 (m, ρs) = viewOf u := pview_of_pcache (q := (m, ρs)) hsel.1
        rcases r with _ | sig
        · rw [(hfl rfl).1] at hrev; cases hrev
        · unfold discAfter
          rcases hsel.2.2.1 with hn | he
          · have hnew : (m, ρs) ∈ newPairs parameter data m s out.2 :=
              (mem_newPairs parameter data m s).2
                ⟨rfl, hn, ⟨u firstCall, cached_of_pcache (p := (m, ρs)) parameter data hsel.1 firstCall,
                  hsel.2.1⟩⟩
            refine Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inr ?_)))
            rw [Multiset.mem_coe, ← hv]
            exact List.mem_map_of_mem hnew
          · refine Multiset.mem_add.2 (Or.inr ?_)
            unfold poolDisc
            rw [hr]
            simp only [Option.elim]
            rw [hsig sig rfl, he, ite_eq_right (Option.some_ne_none _), hv]
            exact Multiset.mem_singleton_self _
  · intro m'
    have h1 : cachedCount parameter data m' out.2 ≤ cachedCount parameter data m' s + traceCost out.1.2.2.1 := by
      rw [cachedCount_eq, cachedCount_eq]
      exact interp_card_le tg initial model _ _ budget s out hout
    have h2 := interp_traceCost_le tg initial model _ budget s out hout
    have h3 := hC m'
    omega
  · intro q hq
    refine pview_congr parameter data fun call => ?_
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hP.all q ((hP.mem q).1 hq) call)
    rw [hv]
    exact hgrow q call v hv

end SignState

section SignUpperO

variable (parameter : PublicParameter) (data : PublicData) (w : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The live messages other than the signed one. -/
noncomputable def restMsgs (L : QueryLog SigningSpec) (Ms : List Message) : List Message :=
  (live L Ms).filter fun m' => decide (m' ≠ m)

/-- The value of a term through the groups of the other live messages. -/
noncomputable def restBase (rest : List Message) (excl : Pair → Prop) (J : List View) : Multiset View → ℝ≥0∞ :=
  grpAll parameter data s excl rest (virtualOnce Finset.univ w f n J)

/-- Upper value of one signing outcome, for the future pairs `J`. -/
noncomputable def upperO (rest : List Message) (excl : Pair → Prop)
    (out : Run HashInput Coordinate (Option Signature) × State) (J : List View) : ℝ≥0∞ :=
  restBase parameter data w s n f rest excl J d +
    (freshNewWeight parameter data m s
        (fun v => restBase parameter data w s n f rest excl J (d + {v}) - restBase parameter data w s n f rest excl J d) out +
      outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else
        restBase parameter data w s n f rest excl J (d + {v}) - restBase parameter data w s n f rest excl J d) out)

variable {parameter data w m s n d f}

theorem msgLive_append {L : QueryLog SigningSpec} {r : Option Signature} {m' : Message} :
    MsgLive (L ++ [⟨m, r⟩]) m' ↔ MsgLive L m' ∧ m' ≠ m := by
  unfold MsgLive
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left _ he),
      fun hq => h ⟨m, r⟩ (List.mem_append_right _ (List.mem_singleton_self _)) hq.symm⟩
  · rintro ⟨h, hq⟩ e he
    rcases List.mem_append.1 he with he | he
    · exact h e he
    · rw [List.mem_singleton] at he
      subst he
      exact fun h' => hq h'.symm

/-- After signing, the live messages are the other live messages. -/
theorem live_after (L : QueryLog SigningSpec) (r : Option Signature) (Ms : List Message) :
    live (L ++ [⟨m, r⟩]) (addMsg Ms m) = restMsgs m L Ms := by
  have hfil : ∀ l : List Message, l.filter (fun m' => decide (MsgLive (L ++ [⟨m, r⟩]) m')) =
      (l.filter fun m' => decide (MsgLive L m')).filter fun m' => decide (m' ≠ m) := by
    intro l
    rw [List.filter_filter]
    refine List.filter_congr fun m' _ => ?_
    rw [Bool.eq_iff_iff]
    simp [msgLive_append, and_comm]
  unfold live restMsgs addMsg
  split_ifs with hm
  · exact hfil Ms
  · rw [List.filter_cons, ite_eq_right (by simp [msgLive_append]), hfil Ms]
    rfl

/-- Before signing a live message, the live messages are it and the others. -/
theorem live_perm {L : QueryLog SigningSpec} (hm : MsgLive L m) {Ms : List Message} (hMs : Ms.Nodup) :
    (live L (addMsg Ms m)).Perm (m :: restMsgs m L Ms) := by
  have hnd : (live L (addMsg Ms m)).Nodup := live_nodup L (addMsg_nodup hMs m)
  have hmem : m ∈ live L (addMsg Ms m) := mem_live.2 ⟨mem_addMsg_self _ _, hm⟩
  refine (List.perm_cons_erase hmem).trans (List.Perm.cons m (List.Perm.of_eq ?_))
  rw [hnd.erase_eq_filter]
  unfold restMsgs live addMsg
  split_ifs with h
  · refine List.filter_congr fun m' _ => ?_
    rw [Bool.eq_iff_iff]
    simp [bne_iff_ne]
  · rw [List.filter_cons, ite_eq_left (by simpa using hm), List.filter_cons, ite_eq_right (by simp)]
    refine List.filter_congr fun m' _ => ?_
    rw [Bool.eq_iff_iff]
    simp [bne_iff_ne]

/-- A term through the group of a live message and the groups of the others. -/
theorem termO_eq_cons {L : QueryLog SigningSpec} (hm : MsgLive L m) {Ms : List Message}
    (hM : MInv parameter data s Ms) (excl : Pair → Prop) (k : ℕ) :
    termO parameter data w s Ms L excl f d n k =
      creations Finset.univ landing (fun J => grpAll parameter data s excl (m :: restMsgs m L Ms)
        (virtualOnce Finset.univ w f n J) d) k [] := by
  rw [← termO_addMsg hM L excl m f d n k]
  unfold termO termBase
  congr 1
  funext J
  exact grpAll_perm s excl _ (live_perm hm hM.nodup) d

end SignUpperO

/-- The groups see the state only through the digest blocks of their messages. -/
theorem grpAll_blocksOn {parameter : PublicParameter} {data : PublicData} {s s' : State} (excl : Pair → Prop)
    (F : Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message), (∀ m ∈ Ms, ∀ ρ call,
        s'.cache (pblk parameter data (m, ρ) call) = s.cache (pblk parameter data (m, ρ) call)) →
      ∀ d, grpAll parameter data s' excl Ms F d = grpAll parameter data s excl Ms F d
  | [], _, _ => rfl
  | m :: Ms, h, d => by
      have hm := h m (List.mem_cons_self ..)
      have hst : stOf parameter data m s' = stOf parameter data m s := by
        funext ρ
        simp only [stOf]
        rw [show s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ) from hm ρ firstCall]
      have hext : extOf parameter data s' excl m = extOf parameter data s excl m := by
        funext ρ
        unfold extOf
        rw [pview_congr parameter data (hm ρ)]
      simp only [grpAll, grpM]
      rw [hst, hext]
      exact grp_congr _ _ (fun e => grpAll_blocksOn excl F Ms (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) e) d

section SignExpectO

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  {parameter : PublicParameter} {data : PublicData} {w : ℝ≥0∞} {m : Message} {s : State} {n : ℕ}
  {d : Multiset View} {f : Multiset View → ℝ≥0∞}

theorem virtualOnce_succ_nil (J : List View) (e : Multiset View) :
    virtualOnce Finset.univ w f (n + 1) J e = freshAvg Finset.univ fun v => virtualOnce Finset.univ w f n J (e + {v}) := by
  have h := virtualOnce_succ (U := (Finset.univ : Finset View)) (w := w) (f := f) n [] J e
  simpa [itemCoins, slotValue] using h

/-- **A dominated term.** Averaged over a signing call, the upper value of a term is at most its
value with one more fresh slot and the group of the signed message. -/
theorem term_expectO (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none) (hinv : PairInv parameter data m s)
    (hf : MonoFin f) (rest : List Message) (excl : Pair → Prop) (budget k : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        creations Finset.univ landing (fun J => upperO parameter data w m s n d f rest excl out J) k [] ≤
      creations Finset.univ landing (fun J => grpAll parameter data s excl (m :: rest)
        (virtualOnce Finset.univ w f (n + 1) J) d) k [] := by
  rw [creations_tsum]
  refine creations_mono (fun J => ?_) k []
  have hX : Monotone' (restBase parameter data w s n f rest excl J) :=
    grpAll_mono s excl (virtualOnce_mono hf.1 n J) rest
  refine le_trans (sign_term tg initial model parameter data m hparse hkind hX s hinv d excl budget) (le_of_eq ?_)
  simp only [grpAll]
  refine grp_congr _ _ (fun e => ?_) d
  unfold restBase
  symm
  rw [grpAll_congr s excl (virtualOnce_succ_nil J) rest e, grpAll_freshAvg]
  congr 1
  funext v
  exact grpAll_shift s excl _ {v} rest e

/-- The fresh pair completed by a signing call weighs at most its fresh average. -/
theorem fresh_expectO (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none)
    (hinv : PairInv parameter data m s) (gf : View → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        freshNewWeight parameter data m s gf out ≤ freshAvg Finset.univ gf := by
  unfold signCostSource
  rw [interp_liftProb_bind, OracleComp.tsum_prEvent_bind_mul]
  have hstart : ∀ start : Randomness, ∑' out, Pr{let x ← (interp tg initial model
      (signCostSourceLoop parameter data m (data.step m) digestAttemptLimit start) budget s)}[x = out] *
      freshNewWeight parameter data m s gf out ≤ freshAvg Finset.univ gf := by
    intro start
    have h := scan_bound_comb tg initial model parameter data m hparse hkind s hinv gf (fun _ _ => 0)
      digestAttemptLimit (by unfold digestAttemptLimit; norm_num) budget start
    refine le_trans (ENNReal.tsum_le_tsum fun out => mul_le_mul_right le_self_add _) (le_trans h ?_)
    refine walk_le landing_le_one _ (fun ρ => ?_) le_rfl bot_le _ start
    unfold poolValue
    cases pcache parameter data m s ρ <;> simp
  calc _ ≤ ∑' start, Pr{let x ← ($ᵗ Randomness : ProbComp Randomness)}[x = start] * freshAvg Finset.univ gf :=
        ENNReal.tsum_le_tsum fun start => mul_le_mul_right (hstart start) _
    _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)

end SignExpectO

/-! ### The potential after signing a message for the first time -/

section SignPointO

variable (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)

/-- Bound for one outcome of a signing call. -/
noncomputable def canonO (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upperO parameter data w m s n d (witnessFn (pview parameter data s q))
        (restMsgs m L Ms) (· = q) out J) k []) else 0).sum +
  k * (creations Finset.univ landing (fun J => upperO parameter data w m s n d (excess b0)
      (restMsgs m L Ms) (fun _ => False) out J) k [] + failMass Fail) +
  n * failMass Fail

variable {parameter data w b0 Fail m s P Ms L d}

theorem freshNewWeight_ge {out : Run HashInput Coordinate (Option Signature) × State} {r : Option Signature}
    (hres : out.1.1 = some r) {ρ : Randomness} {u : DigestCall → HashOutput}
    (hs0 : s.cache (blk parameter data m ρ) = none) (h0 : pcache parameter data m out.2 ρ = some u)
    (hl : Landed parameter (blockIndex (u firstCall))) (g : View → ℝ≥0∞) :
    g (viewOf u) ≤ freshNewWeight parameter data m s g out := by
  unfold freshNewWeight
  rw [ite_eq_left (by rw [hres]; rfl)]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun ρ' => if s.cache (blk parameter data m ρ') = none then
    (pcache parameter data m out.2 ρ').elim 0 (fun w =>
      if Landed parameter (blockIndex (w firstCall)) then g (viewOf w) else 0) else 0)
    (fun _ _ => bot_le) (Finset.mem_univ ρ))
  simp only [hs0, h0, Option.elim, ite_true, ite_eq_left hl]

end SignPointO

section SignPointMainO

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) (m : Message)

/-- A term after one signing outcome is below its upper value. -/
theorem post_term_leO (hw : w ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : MonoFin f)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (budget : ℕ) (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (hprep : Prepared initial s)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) (excl : Pair → Prop)
    (hex : ∀ sig, r = some sig → s.cache (blk parameter data m sig.randomness) ≠ none → ¬excl (m, sig.randomness))
    (n : ℕ) {k' k : ℕ} (hk : k' ≤ k) :
    termO parameter data w out.2 (addMsg Ms m) (L ++ [⟨m, r⟩]) excl f (discAfter parameter data m s d out) n k' ≤
      creations Finset.univ landing (fun J => upperO parameter data w m s n d f (restMsgs m L Ms) excl out J) k [] := by
  have hpost := source_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
    budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  refine le_trans (termO_mono hw hf _ _ _ excl _ n hk) (creations_mono (fun J => ?_) k [])
  unfold termBase
  rw [live_after L r Ms]
  have hsame : grpAll parameter data out.2 excl (restMsgs m L Ms) (virtualOnce Finset.univ w f n J)
      (discAfter parameter data m s d out) =
      grpAll parameter data s excl (restMsgs m L Ms) (virtualOnce Finset.univ w f n J)
        (discAfter parameter data m s d out) := by
    refine grpAll_blocksOn excl _ _ (fun m' hm' ρ call => ?_) _
    have hne : m' ≠ m := by
      unfold restMsgs at hm'
      simpa using (List.mem_filter.1 hm').2
    exact other_message_keptS tg initial model budget s out hout (m', ρ) hne call
  rw [hsame]
  exact upper_pointX (grpAll_mono s excl (virtualOnce_mono hf.1 n J) _) d excl out r hr Fail hshape hex

/-- `sign_pointO` with the signer's interpreter budget `bi` apart from the potential's budget `budget`. -/
theorem sign_pointO2 (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (bi budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d) (hC : CountInv parameter data Qtot s bi)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) bi s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' : ℕ} (hk : k' ≤ budget) :
    (if Realized tg initial out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length then 0
      else coreO parameter data w b0 Fail out.2 (newPairs parameter data m s out.2 ++ P) (addMsg Ms m)
        (L ++ [⟨m, r⟩]) (discAfter parameter data m s d out)
        (signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length) k') ≤
      if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
      else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out := by
  obtain ⟨_, hP', _, _, _, hview⟩ := sign_paramsS tg initial model Fail Qtot hparse hfail bi
    s P Ms d R hprep hP hM hD hC out hout r hr
  have hext := interp_extends tg initial model _ bi s out hout
  have hpost := source_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
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
  unfold coreO canonO
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
      unfold candO
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
    unfold candO
    by_cases hU' : Unsigned (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q
    · have hU := unsigned_of_append hU'
      rw [ite_eq_left hU', ite_eq_left hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValueO
        rw [hview q hq]
        refine post_term_leO tg initial model parameter data w Fail m hw (witness_props _) hparse hfail bi s Ms L d
          hprep out hout r hr (· = q) (fun sig hsig _ heq => ?_) n hk
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [ite_eq_right hU']
      exact bot_le
  · -- the excess forecast
    refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValueO
    exact post_term_leO tg initial model parameter data w Fail m hw (excess_props b0) hparse hfail bi s Ms L d
      hprep out hout r hr (fun _ => False) (fun _ _ _ h => h) n hk

/-- `sign_expectO` with the signer's interpreter budget `bi` apart from the potential's budget `budget`. -/
theorem sign_expectO2 (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (bi budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (hm : MsgLive L m) (d : Multiset View) (hM : MInv parameter data s Ms)
    (hinv : PairInv parameter data m s) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
        (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out) ≤
      if Realized tg initial s ∨ signatureLimit < L.length then 0
      else coreO parameter data w b0 Fail s P Ms L d (signatureLimit - L.length) budget := by
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
  have hmass : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] ≤ 1 :=
    (OracleComp.tsum_prEvent_le_one _)
  have hFN : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out ≤ failMass Fail :=
    fresh_expectO tg initial model hparse' hkind' hinv _ bi
  have hT : ∀ q ∈ P, ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data w m s n d (witnessFn (pview parameter data s q))
          (restMsgs m L Ms) (· = q) out J) budget []) else 0) ≤
      candO parameter data w Fail s Ms L d (n + 1) budget q := by
    intro q _
    unfold candO
    split_ifs
    · rw [ENNReal.tsum_mul_right, mul_one]; exact hmass
    · unfold candValueO
      rw [termO_eq_cons hm hM]
      exact term_expectO tg initial model hparse' hkind' hinv (witness_props _) _ _ bi budget
    · simp
  have hH : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) bi s}[x = out] *
      creations Finset.univ landing (fun J => upperO parameter data w m s n d (excess b0)
        (restMsgs m L Ms) (fun _ => False) out J) budget [] ≤ hValueO parameter data w b0 s Ms L d (n + 1) budget := by
    unfold hValueO
    rw [termO_eq_cons hm hM]
    exact term_expectO tg initial model hparse' hkind' hinv (excess_props b0) _ _ bi budget
  unfold canonO coreO
  simp only [mul_add, ENNReal.tsum_add]
  rw [tsum_list_sum]
  calc _ ≤ failMass Fail + (P.map (candO parameter data w Fail s Ms L d (n + 1) budget)).sum +
        (budget * hValueO parameter data w b0 s Ms L d (n + 1) budget + budget * failMass Fail) +
          n * failMass Fail := by
        refine add_le_add (add_le_add (add_le_add hFN (List.sum_le_sum hT)) (add_le_add ?_ ?_)) ?_
        · simp only [mul_left_comm _ (budget : ℝ≥0∞), ENNReal.tsum_mul_left]
          exact mul_le_mul_right hH _
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
    _ = _ := by push_cast; ring

end SignPointMainO

end FORS.Security.ForsPotential
