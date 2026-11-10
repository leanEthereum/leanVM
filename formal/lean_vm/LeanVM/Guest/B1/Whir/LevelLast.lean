/-
  LeanVM.Guest.B1.Whir.LevelLast

  The final level of `open_stacked` and its closing rounds run the Spec's: its fold rounds, then
  `levelLast`.
-/

module

public import LeanVM.Guest.B1.Whir.LevelMid
public import LeanVM.Guest.B1.Whir.LastRun
public import LeanVM.Guest.B1.Fs.TailRound
public import LeanVM.Guest.B1.Opening.NovelEval

/-!
# The final level and the closing rounds, soundly (G:1576-1754)

* `osTailRounds_sound`, `osTail_sound`: the closing rounds (`opening_tail_round` calls) run
  `tailRun` over their words, the challenges stored in `tail_challenges`.
* `osLevelLast_sound`: from `LvIn`, the final level's template and the closing rounds run
  `foldRounds` then `levelLast`: the lane read into `final_msg`, its normalized copy checked by
  `opening_queries` against every query (`novelSum_eq_novelEval`), the closing claim the guest's
  plus the deficit times the closing challenges (`tailRun_add`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The closing rounds -/

/-- **One `opening_tail_round` call** (G:1748-1750), its challenge stored at `tch·g^j`. -/
theorem osTailRound_sound (hT : ∀ a r, C "opening_tail_round" a r → MeaningOpeningTailRound rd a r)
    {tch j : ℕ} {s : OsSt} (hfs : s.fs.length = 5) (hco : s.co < u128Bound)
    (hok : AllOk C rd σ (osTailRound tch j s).1) :
    ∃ c0 c2 : E, ReadsAt rd (s.cur σ) [c0, c2] ∧
      (osTailRound tch j s).2.F σ =
        ⟨((⟨(s.F σ).cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2.cap, []⟩ ∧
      σ (.n (osTailRound tch j s).2.claim) =
        c0 + ((⟨(s.F σ).cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 *
          (σ (.n s.claim) + (1 + ((⟨(s.F σ).cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1) * c2) ∧
      LoadHolds rd (σ (.n tch)) j ((⟨(s.F σ).cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 ∧
      (osTailRound tch j s).2.cur σ = s.cur σ * gen ^ 2 ∧ (osTailRound tch j s).2.fs.length = 5 ∧
      (osTailRound tch j s).2.co = 0 := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five s hfs
  unfold osTailRound at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨hcu, hcall⟩ := hok
  have ecu := osCurS_val hco hcu
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, stmtOk_atom, holds_load, osLd] at hcall
  obtain ⟨hc, hl⟩ := hcall
  have hM := hT _ _ hc
  simp only [hf, List.cons_append, List.nil_append, List.map_cons, List.map_nil, osRun,
    List.range_succ, List.range_zero, Nat.add_zero, MeaningOpeningTailRound] at hM
  obtain ⟨c0, c2, hrd, hret⟩ := hM
  rw [ecu] at hrd hret
  have hcap : (s.F σ).cap = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [OsSt.F, hf]
  rw [hcap]
  simp only [Fs.squeeze, capOf, List.cons_append, List.nil_append, List.cons.injEq] at hret
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, -⟩ := hret
  refine ⟨c0, c2, hrd, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [OsSt.F, List.map_cons, List.map_nil, e0, e1, e2, e3, e4, Fs.squeeze, capOf]
  · rw [e6]; rfl
  · rw [e7] at hl; exact hl
  · simp only [OsSt.cur, pow_zero, mul_one]; exact e5

/-- **The closing rounds `j .. j + n - 1`** run `tailRun` over their words from the carried
capacity and the guest's claim, the challenges stored from `tch·g^j`. -/
theorem osTailRounds_sound (hT : ∀ a r, C "opening_tail_round" a r → MeaningOpeningTailRound rd a r)
    (tch : ℕ) : ∀ (n j : ℕ) (s : OsSt), s.fs.length = 5 → s.co < u128Bound →
      AllOk C rd σ (osTailRounds tch j n s).1 →
      ∃ pairs : List (E × E), pairs.length = n ∧ ReadsAt rd (s.cur σ) (tailWords pairs) ∧
        (osTailRounds tch j n s).2.F σ = ⟨(tailRun pairs (s.F σ).cap (σ (.n s.claim))).2.2, []⟩ ∧
        σ (.n (osTailRounds tch j n s).2.claim) = (tailRun pairs (s.F σ).cap (σ (.n s.claim))).2.1 ∧
        (∀ i < n, LoadHolds rd (σ (.n tch)) (j + i)
          ((tailRun pairs (s.F σ).cap (σ (.n s.claim))).1.getD i 0)) ∧
        (tailRun pairs (s.F σ).cap (σ (.n s.claim))).1.length = n ∧
        (osTailRounds tch j n s).2.cur σ = s.cur σ * gen ^ (2 * n) ∧
        (osTailRounds tch j n s).2.fs.length = 5 ∧ (osTailRounds tch j n s).2.co < u128Bound
  | 0, j, s, hfs, hco, _ => by
    refine ⟨[], rfl, readsAt_nil _ _, rfl, rfl, fun i h ↦ absurd h (Nat.not_lt_zero _), rfl,
      by simp [osTailRounds], hfs, hco⟩
  | n + 1, j, s, hfs, hco, hok => by
    simp only [osTailRounds] at hok ⊢
    rw [allOk_append] at hok
    obtain ⟨c0, c2, hrd0, hF0, hcl0, hl0, hcur0, hfs0, hco0⟩ := osTailRound_sound hT hfs hco hok.1
    obtain ⟨pairs, hpl, hrd, hF, hcl, hst, hTl, hcur, hfs', hco'⟩ :=
      osTailRounds_sound hT tch n (j + 1) (osTailRound tch j s).2 hfs0
        (by rw [hco0]; unfold u128Bound; positivity) hok.2
    have hcap1 : ((osTailRound tch j s).2.F σ).cap =
        ((⟨(s.F σ).cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2.cap := by rw [hF0]
    rw [hcap1, hcl0] at hF hcl hst hTl
    refine ⟨(c0, c2) :: pairs, by simp [hpl], ?_, ?_, ?_, ?_, ?_, ?_, hfs', hco'⟩
    · have e : tailWords ((c0, c2) :: pairs) = [c0, c2] ++ tailWords pairs := rfl
      rw [e]
      exact readsAt_append hrd0 (by rw [show [c0, c2].length = 2 from rfl, ← hcur0]; exact hrd)
    · rw [hF]; rfl
    · rw [hcl]; rfl
    · intro i hi
      rcases i with _ | i
      · simpa [tailRun] using hl0
      · have := hst i (by omega)
        rw [show j + 1 + i = j + (i + 1) by ring] at this
        simpa [tailRun] using this
    · simp [tailRun, hTl]
    · rw [hcur, hcur0, mul_assoc, ← pow_add]; ring_nf

/-- **The closing rounds** (G:1746-1754) into `tail_challenges` at `tch`. -/
theorem osTail_sound (hT : ∀ a r, C "opening_tail_round" a r → MeaningOpeningTailRound rd a r)
    {c : OsCfg} {s : OsSt} (hfs : s.fs.length = 5) (hco : s.co < u128Bound)
    (hok : AllOk C rd σ (osTail c s).1) :
    ∃ pairs : List (E × E), pairs.length = c.yrLog ∧ ReadsAt rd (s.cur σ) (tailWords pairs) ∧
      (osTail c s).2.1.F σ = ⟨(tailRun pairs (s.F σ).cap (σ (.n s.claim))).2.2, []⟩ ∧
      σ (.n (osTail c s).2.1.claim) = (tailRun pairs (s.F σ).cap (σ (.n s.claim))).2.1 ∧
      ReadsAt rd (σ (.n (osTail c s).2.2)) (tailRun pairs (s.F σ).cap (σ (.n s.claim))).1 ∧
      (tailRun pairs (s.F σ).cap (σ (.n s.claim))).1.length = c.yrLog := by
  unfold osTail at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨-, hR⟩, -⟩ := hok
  obtain ⟨pairs, hpl, hrd, hF, hcl, hst, hTl, -, -, -⟩ :=
    osTailRounds_sound hT (s.k + 1) c.yrLog 0 { s with k := s.k + 2 } hfs hco hR
  have eF : OsSt.F σ { s with k := s.k + 2 } = OsSt.F σ s := rfl
  rw [eF] at hF hcl hst hTl
  dsimp only at hF hcl hst hTl
  refine ⟨pairs, hpl, hrd, hF, hcl, fun i hi ↦ ?_, hTl⟩
  have := hst i (by rw [← hTl]; exact hi)
  rw [Nat.zero_add, List.getD_eq_getElem _ _ hi] at this
  exact this

/-! ## The final level -/

/-- The final level's facts: its row against the Spec's level, its `opening_queries` shape, the
normalizers of its lane. -/
structure FinFacts (c : OsCfg) (logN lvl : ℕ) (lv : OsLv) (level : Whir.Level) : Prop where
  fin : lvl = c.yrLevel
  fold : level.fold = lv.folds
  cols : logN - (lv.foldsOff + lv.folds) = c.yrLog
  ylen : 2 ^ c.yrLog = c.yrLen
  depth : lv.depth = c.yrLog + level.logInvRate
  queries : level.queries = lv.queries
  q0 : 0 < lv.queries
  qu : lv.queries < u128Bound
  P1 : 1 ≤ 128 / lv.depth
  sq : lv.squeezes = sqCount (128 / lv.depth) lv.queries
  pw : digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth
  posOff : lv.posOff < u128Bound
  sq1 : 1 ≤ lv.squeezes
  sqo : lv.squeezes < ordG
  sq5 : lv.squeezes * 5 < u128Bound
  r3 : 3 * (lv.foldsOff + lv.folds) < u128Bound
  cap4 : 4 * lv.capOff < u128Bound
  hs8 : lvl * hsStride < u128Bound
  N : lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG
  qsh : ∃ loop sh, QShapeOk c lvl lv 1 loop sh ∧ sh.nHs = c.yrLen + lv.folds ∧
    sh.hsBits = c.yrLog + 1 ∧
    ∀ i < c.yrLog, (sh.vs.map K.ofBits).getD i 0 = (subspaceRoots c.yrLog).getD i 0
  mu64 : c.yrLog < 64
  nhs : c.yrLen + lv.folds ≤ 2 ^ (c.yrLog + 1)
  hsn : ∀ i < c.yrLen + lv.folds,
    K.ofBits (hsScale lv.vanish (c.yrLog + 1) i 1) = hsNorm c.yrLog (c.yrLog + 1) i

/-- The final level's callees and the closing rounds', by their meanings. -/
structure FinCalls (rd : Reader) (C : CallRel) (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    Prop where
  round : ∀ a r, WinTabs rd (a.getD 7 0) → C "opening_round" a r → MeaningOpeningRound rd a r
  fmsg : ∀ a r, C ("opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1") a r →
    MeaningOpeningMessage (c.yrLen + lv.folds) 1 rd a r
  g17 : ∀ w, C ("grind_check__L" ++ natStr queryGrind) [w, σ (.n osTabs)] [] →
    (w.limb 0).lane.toNat % 2 ^ queryGrind = 0
  dec : ∀ a r, WinTabs rd (a.getD 3 0) → coreProgram.Rel rd (decName lv) a r →
    MeaningDecodeQueryWindows lv.depth lv.capDepth rd a r
  cap : ∀ a r, C ("verify_merkle_cap__L" ++ natStr lv.capDepth) a r →
    MeaningVerifyMerkleCap lv.capDepth rd a r
  sqLoop : FnIs (c.sqLoop lvl) (osParams 6) (sqLoopBody lv (c.sqLoop lvl))
  tail : ∀ a r, C "opening_tail_round" a r → MeaningOpeningTailRound rd a r

theorem tailWords_length : ∀ pairs : List (E × E), (tailWords pairs).length = 2 * pairs.length
  | [] => rfl
  | p :: ps => by
    rw [show tailWords (p :: ps) = [p.1, p.2] ++ tailWords ps from rfl, List.length_append,
      tailWords_length ps]
    simp; ring

/-- **The final level and the closing rounds, soundly.** -/
theorem osLevelLast_sound {V : FrameMap} (hU : UnfoldsV rd C V)
    (hle : CallRel.Le C (coreProgram.Rel rd)) (hwt : WinTabs rd (σ (.n osTabs)))
    {c : OsCfg} {logN lvl : ℕ} {lv : OsLv} {level : Whir.Level}
    (hF : FinFacts c logN lvl lv level) (hcal : FinCalls rd C σ c lvl lv)
    {st : OsSt} {ws : WhirState} {recs : List OsRec} {R : List (Digest × ℕ × ℕ)} {root : Digest}
    (hin : LvIn rd σ lvl lv st ws recs R root)
    (hok : AllOk C rd σ (osLevel c lvl lv st).1)
    (hokT : AllOk C rd σ (osTail c (osLevel c lvl lv st).2).1) (lane : ℕ) :
    ∃ (xs gs fold T : List E),
      xs.length = lvWords c lvl lv + 2 * c.yrLog ∧ ReadsAt rd (st.cur σ) xs ∧
      gs.length = lv.folds ∧ fold.length = c.yrLen + lv.folds ∧ T.length = c.yrLog ∧
      RunsWith ((foldRounds level.fold ws).bind fun p ↦ levelLast logN lane lvl level p.1 p.2)
        (st.F σ) xs
        [osLevelW rd V lvl lv (osQCallOf c lvl lv (osPreQ c lvl lv st)).1
          ((osQCallOf c lvl lv (osPreQ c lvl lv st)).2.1.map σ)
          ((osQCallOf c lvl lv (osPreQ c lvl lv st)).2.2.map σ)] R
        ⟨((ws.gammas ++ gs) ++ T).drop lane ++ ((ws.gammas ++ gs) ++ T).take lane,
          ws.glued.foldl (fun w g ↦ w + g.scalar * g.weightAt (((ws.gammas ++ gs) ++ T).drop g.foldStart)) 0,
          multilinearEval (fold.take c.yrLen) T,
          σ (.n (osTail c (osLevel c lvl lv st).2).2.1.claim) +
            T.prod * (gs.prod * recsDeficit recs ws.gammas)⟩
        ((osTail c (osLevel c lvl lv st).2).2.1.F σ) R ∧
      ReadsAt rd (σ (.n osFmsg)) fold ∧
      ReadsAt rd (σ (.n (osTail c (osLevel c lvl lv st).2).2.2)) T ∧
      (∀ j < lv.folds, LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j) gs[j]!) := by
  obtain ⟨loop, sh, ⟨hmem, hent, hodd, hbase, hsf, hsd, hscd, hfin1, hcd2, hcd8, hcdd, hQ⟩, hnhs,
    hhsb, hvs⟩ := hF.qsh
  have hfin := hF.fin
  obtain ⟨hshape, hloop⟩ := oqEntry_shape hent
  have hpre : osPreQ c lvl lv st = (osHsFinal c lv (osCap c lvl lv (osSqueezes c lvl lv
      (osFinalMsg c lv (osRounds c.plan lv.foldsOff lv.folds st).2).2).2).2).2 := by
    simp only [osPreQ, hfin, ↓reduceIte]
  have hlev : osLevel c lvl lv st =
      let f := osRounds c.plan lv.foldsOff lv.folds st
      let m := osFinalMsg c lv f.2
      let gr : List Stmt := [.call ("grind_check__L" ++ natStr queryGrind) [.n m.2.pow0, .n osTabs] []]
      let sq := osSqueezes c lvl lv m.2
      let cp := osCap c lvl lv sq.2
      let h := osHsFinal c lv cp.2
      let q := osQueries c lvl lv h.2
      (f.1 ++ m.1 ++ gr ++ sq.1 ++ cp.1 ++ h.1 ++ q.1, q.2) := by
    simp only [osLevel, hfin, ↓reduceIte, List.append_nil]
  rw [hpre]
  rw [hlev] at hok hokT ⊢
  simp only at hok hokT ⊢
  set f := osRounds c.plan lv.foldsOff lv.folds st with hf
  set m := osFinalMsg c lv f.2 with hm
  set sq := osSqueezes c lvl lv m.2 with hsq
  set cp := osCap c lvl lv sq.2 with hcp
  set h := osHsFinal c lv cp.2 with hh
  set q := osQueries c lvl lv h.2 with hq
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨hoF, hoM⟩, hoG⟩, hoS⟩, hoC⟩, hoH⟩, hoQ⟩ := hok
  set D := recsDeficit recs ws.gammas with hD
  -- the folds
  obtain ⟨xs0, gs, rounds, hx0, hgl, hrl, hrd0, hrun0, hcur0, hfs0, hm0, hco0, hpad0, lg, lc⟩ :=
    osRounds_sound hcal.round hwt c.plan lv.folds lv.foldsOff st ws D hin.fs hin.mats hin.co hF.r3
      hin.claim hoF
  -- the final lane
  obtain ⟨fold, nn, hM⟩ := osFinalMsg_sound hcal.fmsg hfs0 hm0 hco0 hoM
  set S := (f.2.F σ).absorbAll fold dsObserve with hS
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, List.map_cons, List.map_nil] at hoG
  obtain ⟨gok, -, -⟩ := grindSqueeze_cells (s := S) (bits := queryGrind) (by decide) nn _ _
    hM.word0 hM.pow0 (hcal.g17 _ hoG)
  have hpow1 : powOk queryGrind (Keccak.lane (S.nonceState nn) 2) = true :=
    gok.resolve_left (by decide)
  -- the squeezes, the cap, the normalized lane
  have hSq := osSqueezes_sound (c := c) (lvl := lvl) hle hcal.dec hcal.sqLoop hF.pw hF.posOff hF.sq1
    hF.sqo hF.sq5 hwt hM.mats hM.fs hM.F rfl hoS
  obtain ⟨r0, r1, hcapM, lr0, lr1, hmc, hcpe⟩ := osCap_sound hcal.cap hSq.mats hF.cap4 hoC
  obtain ⟨hhs, hhse⟩ := osHsFinal_sound hoH
  have hmh : MatsOk σ h.2.mats := by rw [hhse]; exact hmc
  have hf3 : 3 * lv.foldsOff < u128Bound := lt_of_le_of_lt (by omega) hF.r3
  obtain ⟨hqC, -, hqe⟩ := osQueries_sound hmh hF.cap4 hf3 hF.hs8 hF.posOff hF.qu hoQ
  obtain ⟨hn1, hargs, hrets⟩ := osQCallOf_val hmh hF.cap4 hf3 hF.hs8 hF.posOff hF.qu hoQ
  have eq_q : q.2.fs = sq.2.fs ∧ q.2.cb = sq.2.cb ∧ q.2.co = sq.2.co ∧ q.2.claim = f.2.claim := by
    rw [hqe, hhse, hcpe]
    exact ⟨rfl, rfl, rfl, by rw [hSq.claim]; rfl⟩
  obtain ⟨eqfs, eqcb, eqco, eqcl⟩ := eq_q
  have hqF : q.2.F σ = sq.2.F σ := by simp only [OsSt.F, eqfs]
  have hqcur : q.2.cur σ = sq.2.cur σ := by simp only [OsSt.cur, eqcb, eqco]
  -- the root
  have hroot : (r0, r1) = digestHalves root := by
    rw [loadHolds_unique lr0 hin.r0, loadHolds_unique lr1 hin.r1]
  -- the positions
  set P := 128 / lv.depth with hP
  set S' := S.nonceState nn with hS'
  have hw0 : σ (.n m.2.word0) = challengeOf S' := by rw [hM.word0, Keccak.challengeOf_cells]
  set qs := sqPositions lv.depth (sqSample (challengeOf S') (capOf S')) lv.queries with hqs
  have hqsl : qs.length = lv.queries := by simp [qs, sqPositions]
  have hpos := sq_positions (rd := rd) (d := lv.depth) (cd := lv.capDepth) (po := lv.posOff)
    (S := lv.squeezes) (Q := lv.queries) (w := sqSample (challengeOf S') (capOf S'))
    (qpos := σ (.n osQpos)) (qbp := σ (.n osQbp)) (tabs := σ (.n osTabs)) hF.P1 hF.sq
    (by rw [← hw0]; exact hSq.dec)
  -- the queries
  set N := lv.queries / (1 + if lvl = 0 then 1 else 0) with hN
  have hpairs : (if lvl = 0 then lv.queries / 2 else lv.queries) = N := by
    rw [hN]; split_ifs <;> simp
  set args := osQArgs σ c lvl lv h.2 with hargsd
  obtain ⟨fm, hfind, hpar, hhold⟩ := hU _ _ _ hqC
  have hQN : oqCount sh.odd sh.base N = lv.queries := hQ
  have hsw := opening_queries_all_sound_w _ hmem rd C V hU hle fm _ args _ N hfind hpar hhold
    (by simp [args, osQArgs, hpairs]) hF.N (by
      rw [hQN, hsd, hscd]
      intro k hk x bp hx hbp
      obtain ⟨hl1, hlt, bp', hbp', hfr⟩ := hpos k hk
      refine ⟨_, hlt, loadHolds_unique hx hl1, ?_⟩
      rw [loadHolds_unique hbp hbp']
      exact hfr)
  simp only at hsw
  set wsq := oqsOf sh.oq sh.odd loop N rd (V (osQueriesName c lvl lv) args
    [σ (.n q.2.batched)]) V with hwsq
  have hcap' : MeaningVerifyMerkleCap sh.cd rd [args.getD 0 0, args.getD 1 0] [r0, r1] := by
    rw [hscd]; exact hcapM
  have hm' : MeaningOpeningQueriesW sh rd wsq [args.getD 0 0, args.getD 1 0, args.getD 2 0,
      args.getD 3 0, args.getD 4 0, args.getD 5 0, args.getD 6 0, args.getD 7 0]
      [σ (.n q.2.batched)] := hsw
  obtain ⟨rounds', hsv, hrl', hsvl, hRA, hWA, hosl, hopen, hidx, hwq, -, hfinal, -, -⟩ :=
    queries_open hm' hcap' hroot hcd2 hcd8 hcdd (N0 := N) (by simp [args, osQArgs, hpairs]) hF.N
      hQN (by have := hF.q0; omega) qs (by rw [hqsl])
      (fun k hk ↦ by rw [hsd]; exact (hpos k hk).2.1)
      (fun k hk ↦ by
        obtain ⟨-, -, bp, hbp, hfr⟩ := hpos k hk
        exact ⟨bp, by simpa [args, osQArgs] using hbp, by rw [hsd, hscd]; exact hfr⟩)
  have hrr : rounds' = rounds := rounds_eq (n := lv.folds) hrl (by rw [hrl', hsf])
    (by simpa [args, osQArgs] using hRA) (fun j hj ↦ by
      obtain ⟨a, b, t⟩ := lc j hj
      refine ⟨?_, ?_, ?_⟩
      · rw [loadHolds_mul_gen_pow, show 3 * lv.foldsOff + 3 * j = 3 * (lv.foldsOff + j) by ring]
        exact a
      · rw [loadHolds_mul_gen_pow, show 3 * lv.foldsOff + (3 * j + 1) = 3 * (lv.foldsOff + j) + 1 by ring]
        exact b
      · rw [loadHolds_mul_gen_pow, show 3 * lv.foldsOff + (3 * j + 2) = 3 * (lv.foldsOff + j) + 2 by ring]
        exact t)
  subst hrr
  -- the normalized lane
  have hfl : fold.length = c.yrLen + lv.folds := hM.len
  have hhsv : ∀ i < fold.length, hsv.getD i 0 =
      fold.getD i 0 * ofK (hsNorm c.yrLog (c.yrLog + 1) i) := by
    intro i hi
    have hw := hWA hfin1 i (by rw [hsvl, hnhs, ← hfl]; exact hi)
    obtain ⟨v, hv1, hv2⟩ := hhs i (by rw [← hfl]; exact hi)
    have hargs4 : args.getD 4 0 = σ (.n h.2.hs) := by simp [args, osQArgs, hfin]
    rw [hargs4] at hw
    have ev : v = fold.getD i 0 := by
      rw [List.getD_eq_getElem _ _ hi]; exact loadHolds_unique hv1 (hM.fmsg i hi)
    rw [loadHolds_unique hw hv2, ev, word_eOfNat, eOfNat, hF.hsn i (by rw [← hfl]; exact hi)]
  have hreq : ∀ k (hk : k < qs.length), foldRow (specLanes lvl (wsq.getD k default).2.1)
      (K.ofBits qs[k]) rounds' = novelEval fold (subspaceAt c.yrLog (K.ofBits qs[k])) := by
    intro k hk
    have e1 := hfinal hfin1 k (by rw [← hqsl]; exact hk)
    rw [qwFold, hbase, lanesOf_base, hwq k (by rw [← hqsl]; exact hk),
      List.getD_eq_getElem _ _ hk, hnhs, hhsb, ← hfl] at e1
    rw [e1]
    exact novelSum_eq_novelEval hF.mu64 _ _ hvs fold hsv (by rw [hfl]; exact hF.nhs)
      (by rw [hsvl, hnhs, hfl]) hhsv
  -- the closing rounds
  have hfsq : q.2.fs.length = 5 := by rw [eqfs]; exact hSq.fs
  have hcoq : q.2.co < u128Bound := by rw [eqco, hSq.co, hM.co]; unfold u128Bound; positivity
  obtain ⟨pairs, hpl, hrdT, hFT, hclT, hT, hTl⟩ := osTail_sound (c := c) hcal.tail hfsq hcoq hokT
  -- the Spec's level
  set os := wsq.map (toOpening rd (args.getD 0 0) sh.cd sh.depth) with hos
  set ws1 : WhirState :=
    { ws with claim := σ (.n f.2.claim) + gs.prod * D, gammas := ws.gammas ++ gs } with hws1
  have hg1 : ws1.gammas.length = lv.foldsOff + lv.folds := by simp [ws1, hin.glen, hgl]
  have hmu : logN - ws1.gammas.length = c.yrLog := by rw [hg1]; exact hF.cols
  set F3 : Fs := ((⟨capOf S', []⟩ : Fs).squeezeN (sqCount P lv.queries - 1)).2 with hF3
  have hsqF : sq.2.F σ = F3 := by rw [hSq.F, hF.sq]
  have hqF3 : (q.2.F σ).cap = F3.cap := by rw [hqF, hsqF]
  have hqcl : σ (.n q.2.claim) = σ (.n f.2.claim) := by rw [eqcl]
  rw [hqF3, hqcl] at hFT hclT hT hTl
  obtain ⟨tadd1, tadd2, tadd3⟩ := tailRun_add pairs F3.cap (σ (.n f.2.claim)) (gs.prod * D)
  set T := (tailRun pairs F3.cap (σ (.n f.2.claim))).1 with hTd
  have hrun1 := levelLast_run logN lane lvl level ws1 rounds' (f.2.F σ) R hin.R fold
    (by rw [hmu, hF.ylen, hfl, hF.fold]) nn (by decide)
    (by rw [hmu, ← hF.depth]; exact hF.P1) (by rw [hF.queries]; exact hF.q0)
    hpow1 qs (by rw [hmu, ← hF.depth, hF.queries]) F3 (by rw [hmu, ← hF.depth, hF.queries])
    os (by rw [hosl, hqsl])
    (fun k hk ho ↦ by
      have := hopen k hk ho
      rw [hsd, hbase, hsf] at this
      exact this) hidx
    (fun k hk ho ↦ by
      have hkw : k < wsq.length := by
        have h' := ho; rw [hos, List.length_map] at h'; exact h'
      have e : os[k].leaf = (wsq.getD k default).2.1 := by
        rw [List.getD_eq_getElem _ _ hkw]
        simp only [hos, List.getElem_map]
        rfl
      rw [e, hmu]; exact hreq k hk) pairs (by rw [hmu, hpl])
  rw [hmu] at hrun1
  have hws1c : ws1.claim = σ (.n f.2.claim) + gs.prod * D := rfl
  rw [hws1c, tadd1, tadd2, tadd3] at hrun1
  refine ⟨xs0 ++ (fold ++ [nn] ++ tailWords pairs), gs, fold, T, ?_, ?_, hgl, hfl, ?_, ?_, hM.fmsg,
    ?_, ?_⟩
  · simp [lvWords, hfin, hx0, hfl, tailWords_length, hpl]; ring
  · refine readsAt_append hrd0 (readsAt_append ?_ ?_)
    · rw [hx0, ← hcur0]; exact hM.reads
    · rw [hx0, ← hcur0, show (fold ++ [nn]).length = c.yrLen + lv.folds + 1 by simp [hfl],
        ← hM.cur, ← hSq.cur, ← hqcur]
      exact hrdT
  · rw [hTd, hTl]
  · have h0 := RunsTo.withRoots hrun0 R
    rw [hF.fold]
    have hW : osLevelW rd V lvl lv (osQCallOf c lvl lv h.2).1 ((osQCallOf c lvl lv h.2).2.1.map σ)
        ((osQCallOf c lvl lv h.2).2.2.map σ) = os := by
      simp only [osLevelW, hn1, hargs, hrets, hshape, hloop]
      rw [← hscd, ← hsd]
      rfl
    refine RunsWith.of_eq (RunsWith.bind' h0 hrun1) rfl (by simp) (by rw [hW]; rfl) rfl ?_ ?_ rfl
    · simp only [ws1, hF.ylen, hclT]
    · rw [hFT]
  · exact hT
  · intro j hj; exact lg j hj

end
end LeanVM.Guest.B1.Whir
