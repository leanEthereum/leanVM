/-
  LeanVM.Guest.B1.Whir.StackedC9

  Every level of `open_stacked` at its honest values.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC8
public import LeanVM.Guest.B1.Whir.OsStraight

/-!
# The levels, honestly (TRIAGE #36)

`osLevel_complete`: one level at the values `osLvValsA ++ osLvValsB` on a memory holding what it
reads (`OsLvMem`); `osLevels_complete`: every level from the levels' data (`OsChain`) at the values
`osLvsVals`, the guest's state after the last at the specification's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- What level `lvl` reads of the memory: the stream at `cur`, its challenges stored, its next root
and out-of-domain claim stored, its squeezes' states, its query weights, its root, its scalar. -/
structure OsLvMem (rd : Reader) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ) (H : OsLvH) (rt : Digest)
    (P : OsPtrs) (sqzv cur : E) : Prop where
  reads : ∀ j < xs.length, LoadHolds rd cur j (xs.getD j 0)
  fch : ∀ j < (cfg.lv lvl).folds, LoadHolds rd P.fch ((cfg.lv lvl).foldsOff + j) (H.chs.getD j 0)
  rt2 : lvl ≠ cfg.yrLevel → LoadHolds rd P.roots (2 * lvl + 2) (osHW cfg lvl xs p 0) ∧
    LoadHolds rd P.roots (2 * lvl + 3) (osHW cfg lvl xs p 1)
  ood : lvl ≠ cfg.yrLevel → LoadHolds rd P.ood ((lvl + 1) * 4) (osHLam cfg lvl xs p H.cv1) ∧
    LoadHolds rd P.ood ((lvl + 1) * 4 + 1) (osHW cfg lvl xs p 2) ∧
    LoadHolds rd P.ood ((lvl + 1) * 4 + 2) (osHW cfg lvl xs p 3) ∧
    LoadHolds rd P.ood ((lvl + 1) * 4 + 3) (osHW cfg lvl xs p 4)
  sq0 : LoadHolds rd sqzv 0 (digestScalars (osHCv3 cfg lvl xs p H.cv1)).1
  sq1 : LoadHolds rd sqzv 1 (digestScalars (osHCv3 cfg lvl xs p H.cv1)).2
  sq2 : LoadHolds rd sqzv (2 * (cfg.lv lvl).squeezes) (digestScalars (osHCv4 cfg lvl xs p H.cv1)).1
  sq3 : LoadHolds rd sqzv (2 * (cfg.lv lvl).squeezes + 1) (digestScalars (osHCv4 cfg lvl xs p H.cv1)).2
  qw : ∀ i < (cfg.lv lvl).queries, LoadHolds rd P.qw (lvl * cfg.maxQ + i) (osHLam cfg lvl xs p H.cv1 ^ i)
  rt0 : LoadHolds rd P.roots (2 * lvl) (digestScalars rt).1
  rt1 : LoadHolds rd P.roots (2 * lvl + 1) (digestScalars rt).2
  beta : LoadHolds rd P.betas lvl (if lvl = cfg.yrLevel then osHLam cfg lvl xs p H.cv1
    else osHLam cfg lvl xs p H.cv1 * osHLam cfg lvl xs p H.cv1)

/-- What level `lvl`'s calls are taken to satisfy, at their honest words: the first part's under
`CA`, the second's under `CB`. -/
structure OsLvCallH (CA CB Csq : CallRel) (cfg : OsCfg) (lvl : ℕ) (xs : List E) (p : ℕ) (H : OsLvH) (rt : Digest)
    (P : OsPtrs) (sqzv rewv cur : E) : Prop where
  fold : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ xs.length →
    CA "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
      q'.getD 2 0] (osFoldRets xs cv' p' q' (cur * gen ^ p'))
  final : lvl = cfg.yrLevel → CA cfg.finalMsg [(digestScalars H.cv1).1, (digestScalars H.cv1).2,
    cur * gen ^ osHP1 cfg lvl p, P.fmsg]
    [(digestScalars (osHCv2 cfg lvl xs p H.cv1)).1, (digestScalars (osHCv2 cfg lvl xs p H.cv1)).2,
      cur * gen ^ osHP2 cfg lvl p]
  commit : lvl ≠ cfg.yrLevel → CA "assert_canonical" [osHW cfg lvl xs p 0] [0] ∧
    CA "assert_canonical" [osHW cfg lvl xs p 1] [0] ∧
    CA "opening_ood_point" [(digestScalars (osHCv12 cfg lvl xs p H.cv1)).1,
      (digestScalars (osHCv12 cfg lvl xs p H.cv1)).2, P.oodz * osGw ((lvl + 1 + 0) * 22), osGw (cfg.lv lvl).logCols]
      [(digestScalars (sqAll (cfg.lv lvl).logCols (osHCv12 cfg lvl xs p H.cv1)).2).1,
        (digestScalars (sqAll (cfg.lv lvl).logCols (osHCv12 cfg lvl xs p H.cv1)).2).2]
  grind : CA "grind_check" [(digestScalars (osHCv2 cfg lvl xs p H.cv1)).1,
    (digestScalars (osHCv2 cfg lvl xs p H.cv1)).2, osHNonce cfg lvl xs p, osGw (cfg.lv lvl).grindBits] []
  sq : 1 + osGw (cfg.lv lvl).squeezes ≠ 0 →
    Csq (cfg.lv lvl).sqLoop [1, osGw (cfg.lv lvl).squeezes, sqzv, P.qpos, P.qbp] []
  rw : CB (cfg.lv lvl).rowWeights [P.fch * gen ^ (cfg.lv lvl).foldsOff, rewv] []
  cap : CB (cfg.lv lvl).verifyCap [P.caps * gen ^ (4 * (cfg.lv lvl).capOff), P.flags * gen ^ (cfg.lv lvl).capOff]
    [(digestScalars rt).1, (digestScalars rt).2]
  q : CB (cfg.lv lvl).queriesFn [P.caps * gen ^ (4 * (cfg.lv lvl).capOff), P.flags * gen ^ (cfg.lv lvl).capOff,
    P.qw * gen ^ (lvl * cfg.maxQ), P.qbp * gen ^ (cfg.lv lvl).posOff, rewv, osGw (cfg.lv lvl).queries]
    [osHEnf cfg lvl xs p H]

/-- The values of a level from its first. -/
def osLvVals (cfg : OsCfg) (lvl : ℕ) (xs : List E) (cv : Digest) (p : ℕ) (w : WhirState) (H : OsLvH)
    (co : ℕ) (cur : E) (rt : Digest) (P : OsPtrs) (sqzv rewv : E) : List E :=
  osLvValsA cfg lvl xs cv p w H co cur P.oodz ++ osLvValsB cfg lvl xs p H rt P sqzv rewv

/-- **One level** at its honest values (G:1096-1213). -/
theorem osLevel_complete {cfg : OsCfg} {μ lvl : ℕ} {L : Whir.Level} {rest : List Whir.Level}
    (hspec : LvSpec cfg μ lvl L rest) {xs : List E} {cv : Digest} {p : ℕ} {w : WhirState}
    {osp : List Opening} {roots : List (Digest × ℕ × ℕ)} {H : OsLvH}
    (hok : OsLvOk cfg lvl xs p μ L cv w osp roots H) {s : OsSt} {cur : E} {rt : Digest} {P : OsPtrs}
    {sqzv rewv : E} (hP : OsPtrsAt σ P) (hat : OsAt σ s cv cur p) (hcop : s.co ≤ p) (hco8 : s.co ≤ 8)
    (hq : w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)]) (hm : OsLvMem rd cfg lvl xs p H rt P sqzv cur)
    {kret : List E → Prop} {CA CB Csq : CallRel} (hc : OsLvCallH CA CB Csq cfg lvl xs p H rt P sqzv rewv cur)
    (hv : ∀ j < (osLvVals cfg lvl xs cv p w H s.co cur rt P sqzv rewv).length,
      σ (.n (s.k + j)) = (osLvVals cfg lvl xs cv p w H s.co cur rt P sqzv rewv).getD j 0) :
    (OsCallsOk CA σ ((osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1) ∧
      OsCallsOk Csq σ (osLvSq cfg lvl (osLvG cfg lvl s).2).1 ∧
      OsCallsOk CB σ (osLvRestB cfg lvl (osLvG cfg lvl s).2) ∧
      OsLvSig σ cfg lvl (osLvG cfg lvl s).2 sqzv rewv) ∧
    Stmt.HoldsList osTC rd σ (osLevel cfg lvl (cfg.lv lvl) s).1 True kret ∧
      OsAt σ (osLevel cfg lvl (cfg.lv lvl) s).2 (osHCvEnd cfg lvl xs p H.cv1) cur (osHPEnd cfg lvl p) ∧
      (osLevel cfg lvl (cfg.lv lvl) s).2.co = (if lvl = cfg.yrLevel then 3 else 8) ∧
      (osHWEnd cfg lvl xs p H).quad = [σ (.n (osLevel cfg lvl (cfg.lv lvl) s).2.c),
        σ (.n (osLevel cfg lvl (cfg.lv lvl) s).2.b), σ (.n (osLevel cfg lvl (cfg.lv lvl) s).2.a)] ∧
      (osHWEnd cfg lvl xs p H).target = σ (.n (osLevel cfg lvl (cfg.lv lvl) s).2.t) ∧
      (osLevel cfg lvl (cfg.lv lvl) s).2.k = s.k + (osLvVals cfg lvl xs cv p w H s.co cur rt P sqzv rewv).length := by
  obtain ⟨hA, hB⟩ := os_look_app hv
  obtain ⟨hHA, hatA, hcoA, hqA, htA, hkA⟩ := osLevelA_complete (C := CA) (rd := rd) (kret := kret) hspec hok hat hcop hco8 hq
    hP.oodz hm.reads (fun j hj => by rw [hP.fch]; exact hm.fch j hj)
    (fun h => by rw [hP.roots]; exact hm.rt2 h)
    (fun h => by
      rw [hP.ood]
      obtain ⟨-, o1, o2, o3⟩ := hm.ood h
      exact ⟨by simpa using o1, by simpa using o2, by simpa using o3⟩)
    hc.fold (fun h => by rw [hP.fmsg]; exact hc.final h) hc.commit hc.grind hA
  have hlen := hok.len
  obtain ⟨⟨hHsq, hHB, hsig⟩, hatB, hcoB, hqB, htB, hkB⟩ := osLevelB_complete (C := CB) (Csq := Csq) (rd := rd) (kret := kret) (rewv := rewv) hspec hP
    hatA hqA htA (hm.reads _ (by unfold osHPEnd at hlen; omega))
    (hm.reads (osHP2 cfg lvl p + 1 + 1) (by unfold osHPEnd at hlen; omega))
    hm.sq0 hm.sq1 hm.sq2 hm.sq3 hm.qw hm.rt0 hm.rt1 (fun h => hm.ood h) hm.beta
    hc.sq hc.rw hc.cap hc.q (fun j hj => by rw [hkA]; exact hB j hj)
  have hstr := osLvStB_straight cfg lvl (osLvG cfg lvl s).2
  rw [osLvStB_eq, os_all_append, Bool.and_eq_true] at hstr
  rw [osLevel_parts]
  refine ⟨⟨os_callsOk_of_holdsList _ (osLvStA_straight _ _ _) hHA,
    os_callsOk_of_holdsList _ hstr.1 hHsq, os_callsOk_of_holdsList _ hstr.2 hHB, hsig⟩, ?_, hatB, ?_, hqB, htB, ?_⟩
  · rw [holdsList_append, osLvStB_eq, holdsList_append (osLvSq cfg lvl (osLvG cfg lvl s).2).1]
    refine (holdsList_noRet _ ?_ _ _).mpr ⟨os_holdsList_toTC hHA,
      (holdsList_noRet _ (osSqueezes_noRet _ _ _ _ _ _) _ _).mpr ⟨os_holdsList_toTC hHsq, os_holdsList_toTC hHB⟩⟩
    simp only [noRetList_append, osFolds_noRet, osLvF, osLvG, osGrind_noRet, Bool.and_true, Bool.true_and]
    unfold osLvM; split
    · exact osFinal_noRet _ _ _
    · rw [show (cfg.lv lvl).oodNext = 1 from ?_]
      · exact osCommit_noRet _ _ _ _ _ _
      · rename_i hl
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlast, -, hnext⟩ := hspec
        cases rest with
        | nil => exact absurd (hlast.mp rfl) hl
        | cons a b => exact (hnext a rfl).1
  · show (osLvGl cfg lvl (osLvG cfg lvl s).2).2.co = _
    rw [hcoB, hcoA]; split <;> rfl
  · show (osLvGl cfg lvl (osLvG cfg lvl s).2).2.k = _
    rw [hkB, hkA, osLvVals, List.length_append]; ring

/-- The values of the levels `lvl ..` from the first. -/
def osLvsVals (cfg : OsCfg) (xs : List E) (cur : E) (P : OsPtrs) (sqz rew : ℕ → E) :
    ℕ → Digest → ℕ → WhirState → List (Digest × ℕ × ℕ) → OsSt → List OsLvH → List E
  | _, _, _, _, _, _, [] => []
  | lvl, cv, p, w, roots, s, H :: Hs =>
    osLvVals cfg lvl xs cv p w H s.co cur (roots.getD lvl default).1 P (sqz lvl) (rew lvl) ++
      osLvsVals cfg xs cur P sqz rew (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
        (osHWEnd cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) (osLevel cfg lvl (cfg.lv lvl) s).2 Hs

/-- What the levels `lvl ..` read of the memory. -/
def OsLvsMem (rd : Reader) (cfg : OsCfg) (xs : List E) (cur : E) (P : OsPtrs) (sqz : ℕ → E) :
    ℕ → Digest → ℕ → WhirState → List (Digest × ℕ × ℕ) → List OsLvH → Prop
  | _, _, _, _, _, [] => True
  | lvl, _cv, p, _w, roots, H :: Hs =>
    OsLvMem rd cfg lvl xs p H (roots.getD lvl default).1 P (sqz lvl) cur ∧
      OsLvsMem rd cfg xs cur P sqz (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
        (osHWEnd cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) Hs

/-- The levels' call hypotheses, level `i`'s under `CA i` and `CB i`. -/
def OsLvsCallH (CA CB Csq : ℕ → CallRel) (cfg : OsCfg) (xs : List E) (cur : E) (P : OsPtrs) (sqz rew : ℕ → E) :
    ℕ → ℕ → WhirState → List (Digest × ℕ × ℕ) → List OsLvH → Prop
  | _, _, _, _, [] => True
  | lvl, p, _w, roots, H :: Hs =>
    OsLvCallH (CA lvl) (CB lvl) (Csq lvl) cfg lvl xs p H (roots.getD lvl default).1 P (sqz lvl) (rew lvl) cur ∧
      OsLvsCallH CA CB Csq cfg xs cur P sqz rew (lvl + 1) (osHPEnd cfg lvl p) (osHWEnd cfg lvl xs p H)
        (osHRootsEnd cfg lvl roots H) Hs

/-- The levels' calls satisfy their call relations. -/
def OsLvsCallsOk (CA CB Csq : ℕ → CallRel) (cfg : OsCfg) (σ : Val) (sqz rew : ℕ → E) : ℕ → OsSt → ℕ → Prop
  | _, _, 0 => True
  | lvl, s, n + 1 =>
    OsCallsOk (CA lvl) σ ((osLvF cfg lvl s).1 ++ (osLvM cfg lvl s).1 ++ (osLvG cfg lvl s).1) ∧
      OsCallsOk (Csq lvl) σ (osLvSq cfg lvl (osLvG cfg lvl s).2).1 ∧
      OsCallsOk (CB lvl) σ (osLvRestB cfg lvl (osLvG cfg lvl s).2) ∧
      OsLvSig σ cfg lvl (osLvG cfg lvl s).2 (sqz lvl) (rew lvl) ∧
      OsLvsCallsOk CA CB Csq cfg σ sqz rew (lvl + 1) (osLevel cfg lvl (cfg.lv lvl) s).2 n

/-- The chain state, the stream position and the state after the levels. -/
def osLvsEnd (cfg : OsCfg) (xs : List E) :
    ℕ → Digest → ℕ → WhirState → List (Digest × ℕ × ℕ) → List OsLvH → Digest × ℕ × WhirState
  | _, cv, p, w, _, [] => (cv, p, w)
  | lvl, _cv, p, _w, roots, H :: Hs =>
    osLvsEnd cfg xs (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1) (osHPEnd cfg lvl p) (osHWEnd cfg lvl xs p H)
      (osHRootsEnd cfg lvl roots H) Hs

/-- **Every level** at its honest values, from the levels' data. -/
theorem osLevels_complete {cfg : OsCfg} {μ lane : ℕ} {Lall : List Whir.Level}
    (hlen : Lall.length = cfg.levels.length)
    (hspec : ∀ i < Lall.length, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1)))
    (hyl : cfg.yrLevel = cfg.levels.length - 1) {xs : List E} {e : WhirEnd} {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} {cur : E}
    {P : OsPtrs} {sqz rew : ℕ → E} (hP : OsPtrsAt σ P) {kret : List E → Prop} {CA CB Csq : ℕ → CallRel} :
    ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (osp : List Opening)
      (roots : List (Digest × ℕ × ℕ)) (s : OsSt), lvl + Hs.length = cfg.levels.length →
      OsChain cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs → OsAt σ s cv cur p → s.co ≤ p → s.co ≤ 8 →
      w.quad = [σ (.n s.c), σ (.n s.b), σ (.n s.a)] → OsLvsMem rd cfg xs cur P sqz lvl cv p w roots Hs →
      OsLvsCallH CA CB Csq cfg xs cur P sqz rew lvl p w roots Hs →
      (∀ j < (osLvsVals cfg xs cur P sqz rew lvl cv p w roots s Hs).length,
        σ (.n (s.k + j)) = (osLvsVals cfg xs cur P sqz rew lvl cv p w roots s Hs).getD j 0) →
      OsLvsCallsOk CA CB Csq cfg σ sqz rew lvl s Hs.length ∧
      Stmt.HoldsList osTC rd σ (osLevels cfg lvl (cfg.levels.drop lvl) s).1 True kret ∧
        OsAt σ (osLevels cfg lvl (cfg.levels.drop lvl) s).2 (osLvsEnd cfg xs lvl cv p w roots Hs).1 cur
          (osLvsEnd cfg xs lvl cv p w roots Hs).2.1 ∧
        (osLevels cfg lvl (cfg.levels.drop lvl) s).2.co = 3 ∧
        (osLvsEnd cfg xs lvl cv p w roots Hs).2.2.quad = [σ (.n (osLevels cfg lvl (cfg.levels.drop lvl) s).2.c),
          σ (.n (osLevels cfg lvl (cfg.levels.drop lvl) s).2.b), σ (.n (osLevels cfg lvl (cfg.levels.drop lvl) s).2.a)] ∧
        (osLvsEnd cfg xs lvl cv p w roots Hs).2.2.target = σ (.n (osLevels cfg lvl (cfg.levels.drop lvl) s).2.t) ∧
        (osLevels cfg lvl (cfg.levels.drop lvl) s).2.k = s.k + (osLvsVals cfg xs cur P sqz rew lvl cv p w roots s Hs).length
  | [], _, _, _, _, _, _, _, _, hch, _, _, _, _, _, _, _ => hch.elim
  | H :: Hs, lvl, cv, p, w, osp, roots, s, hl, hch, hat, hcop, hco8, hq, hm, hcH, hv => by
    obtain ⟨hok, -, hlast, hnext⟩ := hch
    obtain ⟨hm1, hm2⟩ := hm
    obtain ⟨hc1, hc2⟩ := hcH
    simp only [List.length_cons] at hl
    have hlt : lvl < cfg.levels.length := by omega
    have hs := hspec lvl (by omega)
    have hdrop : cfg.levels.drop lvl = cfg.lv lvl :: cfg.levels.drop (lvl + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [OsCfg.lv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [hdrop, osLevels_cons]
    have hvs : osLvsVals cfg xs cur P sqz rew lvl cv p w roots s (H :: Hs) =
        osLvVals cfg lvl xs cv p w H s.co cur (roots.getD lvl default).1 P (sqz lvl) (rew lvl) ++
        osLvsVals cfg xs cur P sqz rew (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
          (osHWEnd cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) (osLevel cfg lvl (cfg.lv lvl) s).2 Hs := rfl
    rw [hvs] at hv ⊢
    obtain ⟨hv1, hv2⟩ := os_look_app hv
    obtain ⟨⟨hca1, hcq1, hcb1, hsq1⟩, hH1, hat1, hco1, hq1, ht1, hk1⟩ := osLevel_complete (rd := rd) (kret := kret)
      (rewv := rew lvl) hs hok hP hat hcop hco8 hq hm1 hc1 hv1
    have hend : osLvsEnd cfg xs lvl cv p w roots (H :: Hs) = osLvsEnd cfg xs (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1)
        (osHPEnd cfg lvl p) (osHWEnd cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) Hs := rfl
    rw [hend]
    by_cases hy : lvl = cfg.yrLevel
    · obtain ⟨rfl, -⟩ := hlast hy
      have hnil : cfg.levels.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hnil]
      refine ⟨⟨hca1, hcq1, hcb1, hsq1, trivial⟩, ?_, hat1, by show (osLevel cfg lvl (cfg.lv lvl) s).2.co = 3; rw [hco1, ite_pos' hy],
        hq1, ht1, ?_⟩
      · simp only [osLevels, List.append_nil]; exact hH1
      · simp only [osLevels, osLvsVals, List.append_nil]; exact hk1
    · have hch' := hnext hy
      rw [ite_neg' hy] at hco1
      have hk8 : 8 ≤ osHPEnd cfg lvl p := by
        simp only [osHPEnd, osHP2, ite_neg' hy]; omega
      obtain ⟨hcs2, hH2, hat2, hco2, hq2, ht2, hk2⟩ := osLevels_complete hlen hspec hyl hP Hs (lvl + 1) _ _ _ _ _ _
        (by omega) hch' hat1 (by omega) (by omega) hq1 hm2 hc2 (fun j hj => by rw [hk1]; exact hv2 j hj)
      refine ⟨⟨hca1, hcq1, hcb1, hsq1, hcs2⟩, ?_, hat2, hco2, hq2, ht2, ?_⟩
      · rw [holdsList_append]
        exact (holdsList_noRet _ (osLevel_noRet _ _ _ _) _ _).mpr ⟨hH1, hH2⟩
      · rw [hk2, hk1, List.length_append]; ring

end
end LeanVM.Guest.B1
