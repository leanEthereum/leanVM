/-
  LeanVM.Guest.B1.Whir.OsBody

  `open_stacked`'s whole body at its honest values.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC15
public import LeanVM.Guest.B1.Whir.OsSig

/-!
# The body, honestly (TRIAGE #36)

`osBody_complete`: from the run's data (the head's words, the levels' data, the tail's rounds,
the honest data after the tail), on every memory holding what the body reads, the body holds at
the values `osBodyVals`; each level's calls, the tail's and the finish's hold at their call
relations.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The honest data of a run of `open_stacked`: the stream, the start and level `0`'s chain, the
levels' data, the tail's rounds, the data after the tail, the buffers' pointers. -/
structure OsRun where
  xs : List E
  cv : Digest
  target : E
  root : Digest
  os : List Opening
  Hs : List OsLvH
  w1t : WhirState
  chst : List E
  cv1t : Digest
  D : OsFinD
  P : OsPtrs
  sqz : ℕ → E
  rew : ℕ → E
  tchv : E
  cur : E

/-- Level `0`'s chain state. -/
def OsRun.cv0 (R : OsRun) : Digest := obsCv (obsCv R.cv (R.xs.getD 0 0)) (R.xs.getD 1 0)

/-- Level `0`'s roots. -/
def OsRun.roots0 (cfg : OsCfg) (R : OsRun) : List (Digest × ℕ × ℕ) :=
  [(R.root, (cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)]

/-- The guest's state after the levels. -/
def OsRun.sL (cfg : OsCfg) : OsSt := (osLevels cfg 0 cfg.levels (osHead cfg).2).2

/-- The spec's chain state, stream position and state after the levels. -/
def OsRun.endL (cfg : OsCfg) (R : OsRun) : Digest × ℕ × WhirState :=
  osLvsEnd cfg R.xs 0 R.cv0 2 (osW0 R.target R.xs) (R.roots0 cfg) R.Hs

/-- The tail's start state of the specification. -/
def OsRun.wT (cfg : OsCfg) (R : OsRun) : WhirState :=
  ⟨(R.endL cfg).2.2.target, (R.endL cfg).2.2.quad, [], []⟩

/-- The values of `osBody` from `.n 0`. -/
def osBodyVals (cfg : OsCfg) (R : OsRun) : List E :=
  osHeadVals cfg (digestScalars R.cv).1 (digestScalars R.cv).2 R.target (digestScalars R.root).1
      (digestScalars R.root).2 R.cur R.cv (R.xs.getD 0 0) (R.xs.getD 1 0) R.P ++
    osLvsVals cfg R.xs R.cur R.P R.sqz R.rew 0 R.cv0 2 (osW0 R.target R.xs) (R.roots0 cfg) (osHead cfg).2 R.Hs ++
    osTailVals cfg.yrLog R.xs (R.endL cfg).1 (R.endL cfg).2.1 (R.endL cfg).2.2.quad
      (R.cur * gen ^ ((R.endL cfg).2.1 - (OsRun.sL cfg).co)) (OsRun.sL cfg).co R.tchv R.w1t R.cv1t ++
    osFinishVals cfg (osTail cfg.yrLog (OsRun.sL cfg)).2.2.1 R.D

/-- The tail's start in the guest: its chain state, its stream position, its index. -/
def OsRun.tch (cfg : OsCfg) : ℕ := (osTail cfg.yrLog (OsRun.sL cfg)).2.2.1

/-- The guest's state after the tail. -/
def OsRun.sT (cfg : OsCfg) : OsSt := (osTail cfg.yrLog (OsRun.sL cfg)).2.1

theorem os_lvsEnd_ge (cfg : OsCfg) (xs : List E) : ∀ (Hs : List OsLvH) (lvl : ℕ) (cv : Digest) (p : ℕ)
    (w : WhirState) (roots : List (Digest × ℕ × ℕ)), Hs ≠ [] → p + 3 ≤ (osLvsEnd cfg xs lvl cv p w roots Hs).2.1
  | [], _, _, _, _, _, h => absurd rfl h
  | [H], lvl, cv, p, w, roots, _ => by
    show p + 3 ≤ osHPEnd cfg lvl p
    unfold osHPEnd osHP2 osHP1; omega
  | H :: H' :: Hs, lvl, cv, p, w, roots, _ => by
    have ih := os_lvsEnd_ge cfg xs (H' :: Hs) (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
      (osHWEnd cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) (by simp)
    have hk : p ≤ osHP2 cfg lvl p := by unfold osHP2 osHP1; omega
    show p + 3 ≤ (osLvsEnd cfg xs (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1) (osHPEnd cfg lvl p)
      (osHWEnd cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) (H' :: Hs)).2.1
    have e : osHPEnd cfg lvl p = osHP2 cfg lvl p + 3 := rfl
    omega

/-- A source buffer's pointer: the fold challenges' or the tail challenges'. -/
def osSrcPtr (R : OsRun) (b : ℕ) : E := if b = osFch then R.P.fch else R.tchv

theorem os_srcPtr_eq {σ : Val} {cfg : OsCfg} {R : OsRun} (hf : σ (.n osFch) = R.P.fch)
    (ht : σ (.n (OsRun.tch cfg)) = R.tchv) {b : ℕ} (hb : b = osFch ∨ b = OsRun.tch cfg) :
    osSrcPtr R b = σ (.n b) := by
  unfold osSrcPtr
  by_cases h : b = osFch
  · rw [ite_pos' h, h, hf]
  · rw [ite_neg' h]; rcases hb with hb | hb
    · exact absurd hb h
    · rw [hb, ht]

/-- What the body reads of the memory, at the valuation `σ`. -/
structure OsBodyMem (rd : Reader) (σ : Val) (cfg : OsCfg) (R : OsRun) : Prop where
  reads : ∀ j < R.xs.length, LoadHolds rd R.cur j (R.xs.getD j 0)
  r0 : LoadHolds rd R.P.roots 0 (digestScalars R.root).1
  r1 : LoadHolds rd R.P.roots 1 (digestScalars R.root).2
  lvs : OsLvsMem rd cfg R.xs R.cur R.P R.sqz 0 R.cv0 2 (osW0 R.target R.xs) (R.roots0 cfg) R.Hs
  tch : ∀ j < cfg.yrLog - 1, LoadHolds rd R.tchv j (R.chst.getD j 0)
  last : LoadHolds rd R.tchv (cfg.yrLog - 1) (challengeOf (sqCv R.cv1t))
  zeros : ∀ j < 5 - cfg.yrLog, LoadHolds rd R.tchv (cfg.yrLog + j) 0
  src : ∀ i < 42, ∀ b o, osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog (OsRun.tch cfg) i = some (b, o) →
    LoadHolds rd (osSrcPtr R b) o (R.D.ent i)
  pt : ∀ i < 42, LoadHolds rd R.D.pt i (R.D.ent i)
  bas : ∀ i < cfg.levels.length, ∀ it ∈ osBasisCoords cfg.yrLog (OsRun.tch cfg) (0 + i) (cfg.levels.getD i default),
    LoadHolds rd (osSrcPtr R it.2.1.1) it.2.1.2 (R.D.cf it) ∧ LoadHolds rd R.D.ba it.1 (1 + R.D.cf it) ∧
      LoadHolds rd R.D.bb it.1 (R.D.cf it * eOfNat it.2.2)
  ich0 : LoadHolds rd R.D.ich 0 0
  res : ∀ lvl < cfg.levels.length, LoadHolds rd (R.D.chv lvl) 0 0 ∧ LoadHolds rd R.D.ich lvl (R.D.i0 lvl) ∧
    LoadHolds rd R.P.betas lvl (R.D.b lvl) ∧
    LoadHolds rd (R.D.chv lvl) (cfg.levels.getD lvl default).queries (R.D.r lvl) ∧
    LoadHolds rd R.D.ich (lvl + 1) (R.D.i0 lvl + R.D.b lvl * R.D.r lvl)
  ood : ∀ i < cfg.levels.tail.length,
    0 < osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog + cfg.yrLog ∧
    LoadHolds rd R.P.ood ((1 + i) * 4) (R.D.sc (1 + i)) ∧
    (∀ t < osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog + cfg.yrLog,
      LoadHolds rd R.P.oodz ((1 + i) * 22 + t) (R.D.z (1 + i) t)) ∧
    ∀ t < osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog + cfg.yrLog,
      LoadHolds rd (osSrcPtr R (osOodSrc (OsRun.tch cfg)
        (osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog)
        (cfg.levels.tail.getD i default).foldsOff t).1)
        (osOodSrc (OsRun.tch cfg) (osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog)
          (cfg.levels.tail.getD i default).foldsOff t).2 (R.D.c (1 + i) t)
  ichN : LoadHolds rd R.D.ich cfg.levels.length R.D.ichN

theorem os_ptSrc_mem {nF lane yr tch i b o : ℕ} (h : osPtSrc nF lane yr tch i = some (b, o)) :
    b = osFch ∨ b = tch := by
  unfold osPtSrc at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact Or.inl h.1.symm
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact Or.inr h.1.symm
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact Or.inl h.1.symm
      · cases h

theorem os_basisCoords_mem {yr tch lvl : ℕ} {lv : OsLvl} {it : ℕ × (ℕ × ℕ) × ℕ}
    (h : it ∈ osBasisCoords yr tch lvl lv) : it.2.1.1 = osFch ∨ it.2.1.1 = tch := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp h
  dsimp only
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem os_oodSrc_mem (tch zf ris t : ℕ) : (osOodSrc tch zf ris t).1 = osFch ∨ (osOodSrc tch zf ris t).1 = tch := by
  unfold osOodSrc; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The body** at its honest values (G:1047-1317): it holds, and its calls hold at the call
relations, each level's under `CA`, `CB`, the tail's under `CT`, the finish's under `CF`. -/
theorem osBody_complete {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {R : OsRun} {e : WhirEnd} {sp' : St} {Q : List (ℕ × List (ℕ × Opening))}
    (hx2 : 2 ≤ R.xs.length) (hHs : R.Hs.length = cfg.levels.length)
    (hch : OsChain cfg μ (cfg.lv 0).folds R.xs Lall e sp' Q 0 R.cv0 2 (osW0 R.target R.xs) R.os (R.roots0 cfg) R.Hs)
    {ospT : List Opening} {rootsT : List (Digest × ℕ × ℕ)}
    (hrunT : Runs (foldRounds (cfg.yrLog - 1) (R.wT cfg) []) ⟨(R.endL cfg).1, R.xs.drop (R.endL cfg).2.1, ospT, rootsT⟩
      (R.w1t, R.chst) ⟨R.cv1t, R.xs.drop ((R.endL cfg).2.1 + 2 * (cfg.yrLog - 1)), ospT, rootsT⟩)
    (hDt : R.D.t = polyEval R.w1t.quad (challengeOf (sqCv R.cv1t)))
    (hzD : ∀ i < 42, osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog (OsRun.tch cfg) i = none →
      R.D.ent i = 0) (hnq : ∀ lv ∈ cfg.levels, lv.queries < 2 ^ 128)
    (hσ : ∀ j < (osBodyVals cfg R).length, σ (.n j) = (osBodyVals cfg R).getD j 0)
    (hm : OsBodyMem rd σ cfg R)
    {CA CB Csq : ℕ → CallRel} (hcH : OsLvsCallH CA CB Csq cfg R.xs R.cur R.P R.sqz R.rew 0 2 (osW0 R.target R.xs)
      (R.roots0 cfg) R.Hs)
    {CT : CallRel} (hcT : ∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ R.xs.length →
      CT "opening_fold" [(digestScalars cv').1, (digestScalars cv').2, R.cur * gen ^ p', q'.getD 0 0, q'.getD 1 0,
        q'.getD 2 0] (osFoldRets R.xs cv' p' q' (R.cur * gen ^ p')))
    {CF : CallRel} (hcff : CF cfg.foldFinal [R.P.fmsg, R.tchv] [R.D.yat])
    (hcres : ∀ lvl < cfg.levels.length, 1 + osGw (cfg.levels.getD lvl default).queries ≠ 0 →
      CF (cfg.levels.getD lvl default).resLoop [1, osGw (cfg.levels.getD lvl default).queries, R.P.qpos,
        R.D.ba, R.D.bb, R.D.chv lvl, R.P.qw] []) :
    Stmt.HoldsList osTC rd σ (osBody cfg) False (fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat]) ∧
      OsLvsCallsOk CA CB Csq cfg σ R.sqz R.rew 0 (osHead cfg).2 R.Hs.length ∧
      Stmt.HoldsList CT rd σ (osTail cfg.yrLog (OsRun.sL cfg)).1 True
        (fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat]) ∧
      Stmt.HoldsList CF rd σ (osFinish cfg (OsRun.sT cfg) (OsRun.tch cfg)) False
        (fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat]) ∧
      (σ (.n (OsRun.sL cfg).k) = osGw 5 ∧ σ (.n ((OsRun.sL cfg).k + 1)) = R.tchv) ∧
      OsFinSig σ cfg (OsRun.sT cfg) (OsRun.tch cfg) R.D := by
  set HV := osHeadVals cfg (digestScalars R.cv).1 (digestScalars R.cv).2 R.target (digestScalars R.root).1
      (digestScalars R.root).2 R.cur R.cv (R.xs.getD 0 0) (R.xs.getD 1 0) R.P with hHV
  set LV := osLvsVals cfg R.xs R.cur R.P R.sqz R.rew 0 R.cv0 2 (osW0 R.target R.xs) (R.roots0 cfg) (osHead cfg).2
    R.Hs with hLV
  set TV := osTailVals cfg.yrLog R.xs (R.endL cfg).1 (R.endL cfg).2.1 (R.endL cfg).2.2.quad
      (R.cur * gen ^ ((R.endL cfg).2.1 - (OsRun.sL cfg).co)) (OsRun.sL cfg).co R.tchv R.w1t R.cv1t with hTV
  set FV := osFinishVals cfg (OsRun.tch cfg) R.D with hFV
  have hBV : osBodyVals cfg R = HV ++ LV ++ TV ++ FV := rfl
  have hv : ∀ j < (HV ++ LV ++ TV ++ FV).length, σ (.n (0 + j)) = (HV ++ LV ++ TV ++ FV).getD j 0 := fun j hj => by
    rw [Nat.zero_add, ← hBV]; exact hσ j (by rw [hBV]; exact hj)
  obtain ⟨v3, gF⟩ := os_look_app hv
  obtain ⟨v2, gT⟩ := os_look_app v3
  obtain ⟨gH, gL⟩ := os_look_app v2
  have lH : HV.length = 61 := os_length_headVals _ _ _ _ _ _ _ _ _ _ _
  simp only [Nat.zero_add, List.length_append, lH] at gH gL gT gF
  -- the head
  obtain ⟨hHh, hat0, hco0, hq0, ht0, hP, hk0⟩ := osHead_complete (C := osTC) (rd := rd) (σ := σ) (cfg := cfg)
    (kret := fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat]) rfl (hm.reads 0 (by omega)) (hm.reads 1 (by omega)) hm.r0 hm.r1
    (fun j hj => gH j hj)
  -- the levels
  have hq0' : (osW0 R.target R.xs).quad = [σ (.n (osHead cfg).2.c), σ (.n (osHead cfg).2.b),
      σ (.n (osHead cfg).2.a)] := by rw [hq0]; rfl
  obtain ⟨hcs, hLh, hatL, hcoL, hqL, htL, hkL⟩ := osLevels_complete (rd := rd) (σ := σ) (kret := fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat])
    (CA := CA) (CB := CB) (Csq := Csq) (rew := R.rew) hok.len hok.spec hok.yrLevel hP R.Hs 0 R.cv0 2 (osW0 R.target R.xs) R.os
    (R.roots0 cfg) (osHead cfg).2 (by rw [Nat.zero_add, hHs]) hch hat0 (by rw [hco0]) (by rw [hco0]; omega) hq0'
    hm.lvs hcH (fun j hj => by rw [hk0]; exact gL j hj)
  rw [List.drop_zero] at hLh hatL hcoL hqL htL hkL
  have hsLk : (OsRun.sL cfg).k = 61 + LV.length := by
    rw [show OsRun.sL cfg = (osLevels cfg 0 cfg.levels (osHead cfg).2).2 from rfl, hkL, hk0]
  -- the tail
  have hne : R.Hs ≠ [] := fun h => by have := hok.len2; rw [← hHs, h] at this; simp at this
  have hpL := os_lvsEnd_ge cfg R.xs R.Hs 0 R.cv0 2 (osW0 R.target R.xs) (R.roots0 cfg) hne
  obtain ⟨hTh, htT, htch, hkT⟩ := osTail_complete (C := CT) (rd := rd) (σ := σ) (yrLog := cfg.yrLog)
    (kret := fun rs => rs = [R.D.t, R.D.pt, osFinTot cfg R.D, R.D.yat]) (s := OsRun.sL cfg) (w := R.wT cfg) hatL
    (by show (OsRun.sL cfg).co ≤ _; rw [show (OsRun.sL cfg).co = 3 from hcoL]; exact le_trans (by omega) hpL)
    (by show (OsRun.sL cfg).co ≤ 8; rw [show (OsRun.sL cfg).co = 3 from hcoL]; omega) rfl hqL hrunT hm.tch hm.last
    hm.zeros hcT (fun j hj => by
      show σ (.n ((OsRun.sL cfg).k + j)) = _
      rw [hsLk]
      exact gT j hj)
  -- after the tail
  have htch' : σ (.n (OsRun.tch cfg)) = R.tchv := htch
  have hF := osFinish_complete (C := CF) (rd := rd) (σ := σ) (cfg := cfg) (st := OsRun.sT cfg) (tch := OsRun.tch cfg)
    (D := R.D) hP (by rw [show (OsRun.sT cfg).t = (osTail cfg.yrLog (OsRun.sL cfg)).2.1.t from rfl, htT, hDt])
    (fun i hi b o hs => by
      rw [← os_srcPtr_eq hP.fch htch' (os_ptSrc_mem hs)]; exact hm.src i hi b o hs) hzD hm.pt
    (fun i hi it hit => by
      obtain ⟨m0, m1, m2⟩ := hm.bas i hi it hit
      exact ⟨by rw [← os_srcPtr_eq hP.fch htch' (os_basisCoords_mem hit)]; exact m0, m1, m2⟩)
    hm.ich0 hnq hm.res hok.ood
    (fun i hi => by
      obtain ⟨o0, o1, o2, o3⟩ := hm.ood i hi
      exact ⟨o0, o1, o2, fun t ht => by rw [← os_srcPtr_eq hP.fch htch' (os_oodSrc_mem _ _ _ _)]; exact o3 t ht⟩)
    hm.ichN
    (by rw [hP.fmsg, show OsRun.tch cfg = (osTail cfg.yrLog (OsRun.sL cfg)).2.2.1 from rfl, htch]; exact hcff)
    (fun lvl hl h => by rw [hP.qpos, hP.qw]; exact hcres lvl hl h)
    (fun j hj => by
      show σ (.n ((osTail cfg.yrLog (OsRun.sL cfg)).2.1.k + j)) = _
      rw [hkT, hsLk]
      exact gF j hj)
  have hts : σ (.n (OsRun.sL cfg).k) = osGw 5 ∧ σ (.n ((OsRun.sL cfg).k + 1)) = R.tchv := by
    rw [hsLk]
    have t0 := gT 0 (by rw [hTV]; simp [osTailVals])
    have t1 := gT 1 (by rw [hTV]; simp [osTailVals])
    rw [hTV] at t0 t1
    simp only [osTailVals, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t0 t1
    exact ⟨t0, t1⟩
  have hfs := osFinish_sig (σ := σ) (cfg := cfg) (st := OsRun.sT cfg) (tch := OsRun.tch cfg) (D := R.D)
    (fun j hj => by
      show σ (.n ((osTail cfg.yrLog (OsRun.sL cfg)).2.1.k + j)) = _
      rw [hkT, hsLk]
      exact gF j hj)
  refine ⟨?_, by rw [hHs] at hcs ⊢; exact hcs, hTh, hF, hts, hfs⟩
  unfold osBody
  dsimp only
  simp only [holdsList_append]
  refine (holdsList_noRet _ (osHead_noRet _) _ _).mpr ⟨hHh,
    (holdsList_noRet _ (osLevels_noRet _ _ _ _) _ _).mpr ⟨hLh,
    (holdsList_noRet _ (osTail_noRet _ _) _ _).mpr ⟨os_holdsList_toTC hTh, os_holdsList_toTC hF⟩⟩⟩

end
end LeanVM.Guest.B1
