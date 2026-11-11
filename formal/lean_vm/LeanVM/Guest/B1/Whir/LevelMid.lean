/-
  LeanVM.Guest.B1.Whir.LevelMid

  A non-final level of `open_stacked` runs the Spec's: its fold rounds, then `levelNext`.
-/

module

public import LeanVM.Guest.B1.Whir.Level

/-!
# A non-final level, soundly (G:1556-1694)

`osLevelMid_sound`: from `LvIn`, a non-final level's template runs `foldRounds` then
`levelNext`, reading `lvWords` words at the cursor and one phase of openings (the witness's,
`osLevelW` at the level's `opening_queries` call), and leaves the next level's `LvIn`, the
level's record appended (`RecStored`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The rounds `queries_open` reads at `coefs` are the stored ones. -/
theorem rounds_eq {coefs : E} {n : ℕ} {rs rs' : List FoldRound} (hl : rs.length = n)
    (hl' : rs'.length = n) (h1 : RoundsAt rd coefs rs')
    (h2 : ∀ j < n, LoadHolds rd coefs (2 * j) rs[j]!.alpha ∧
      LoadHolds rd coefs (2 * j + 1) rs[j]!.beta) :
    rs' = rs := by
  refine List.ext_getElem (by rw [hl, hl']) fun j hj' hj ↦ ?_
  obtain ⟨a1, b1⟩ := h1 j hj'
  obtain ⟨a2, b2⟩ := h2 j (by omega)
  rw [List.getD_eq_getElem _ _ hj'] at a1 b1
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at a2 b2
  have ea := loadHolds_unique a1 a2
  have eb := loadHolds_unique b1 b2
  have ext : ∀ x y : FoldRound, x.alpha = y.alpha → x.beta = y.beta → x = y := by
    rintro ⟨⟩ ⟨⟩ h1 h2; simp_all
  exact ext _ _ ea eb

/-- Words read from the cursor, then past them. -/
theorem readsAt_snoc {p : E} {xs : List E} {x : E} (h1 : ReadsAt rd p xs)
    (h2 : LoadHolds rd (p * gen ^ xs.length) 0 x) : ReadsAt rd p (xs ++ [x]) :=
  readsAt_append h1 fun k hk ↦ by
    obtain rfl : k = 0 := by simpa using hk
    exact h2

/-- **A non-final level, soundly.** -/
theorem osLevelMid_sound {V : FrameMap} (hU : UnfoldsV rd C V)
    (hle : CallRel.Le C (coreProgram.Rel rd)) (hwt : WinTabs rd (σ (.n osTabs)))
    {c : OsCfg} {logN lvl : ℕ} {lv lv' : OsLv} {level next : Whir.Level}
    (hF : MidFacts c logN lvl lv level next lv') (hcal : MidCalls rd C σ c lvl lv)
    {st : OsSt} {ws : WhirState} {recs : List OsRec} {R : List (Digest × ℕ × ℕ)} {root : Digest}
    (hin : LvIn rd σ lvl lv st ws recs R root)
    (hok : AllOk C rd σ (osLevel c lvl lv st).1) :
    ∃ (xs : List E) (ws' : WhirState) (r : OsRec) (root' : Digest),
      xs.length = lvWords c lvl lv ∧ ReadsAt rd (st.cur σ) xs ∧
      RunsWith ((foldRounds level.fold ws).bind fun p ↦ levelNext logN lvl level next p.1 p.2)
        (st.F σ) xs
        [osLevelW rd V lvl lv (osQCallOf c lvl lv (osPreQ c lvl lv st)).1
          ((osQCallOf c lvl lv (osPreQ c lvl lv st)).2.1.map σ)
          ((osQCallOf c lvl lv (osPreQ c lvl lv st)).2.2.map σ)]
        R ws' ((osLevel c lvl lv st).2.F σ) (R ++ [(root', lv'.depth, lvWidth (lvl + 1) lv')]) ∧
      LvIn rd σ (lvl + 1) lv' (osLevel c lvl lv st).2 ws' (recs ++ [r])
        (R ++ [(root', lv'.depth, lvWidth (lvl + 1) lv')]) root' ∧
      RecStored rd σ lvl lv r ∧
      (osLevel c lvl lv st).2.cur σ = st.cur σ * gen ^ xs.length ∧
      ∃ gs, ws'.alphas = ws.alphas ++ gs ∧ gs.length = lv.folds := by
  obtain ⟨loop, sh, hmem, hent, hodd, hbase, hsf, hsd, hscd, hfin0, hcd2, hcd8, hcdd, hQ⟩ := hF.qsh
  have hnf := hF.nf
  obtain ⟨hshape, hloop⟩ := oqEntry_shape hent
  -- the blocks
  have hpre : osPreQ c lvl lv st = (osHsMid lvl lv (osCap c lvl lv (osLam (osSqueezes c lvl lv
      (osCommit c lvl lv (osRounds c.plan lv.foldsOff lv.folds st).2).2).2).2).2).2 := by
    simp only [osPreQ, hnf, ↓reduceIte]
  have hlev : osLevel c lvl lv st =
      let f := osRounds c.plan lv.foldsOff lv.folds st
      let m := osCommit c lvl lv f.2
      let gr : List Stmt := [.call ("grind_check__L" ++ natStr queryGrind) [.n m.2.pow0, .n osTabs] []]
      let sq := osSqueezes c lvl lv m.2
      let la := osLam sq.2
      let cp := osCap c lvl lv la.2
      let h := osHsMid lvl lv cp.2
      let q := osQueries c lvl lv h.2
      let g := osGlue lvl lv q.2
      (f.1 ++ m.1 ++ gr ++ sq.1 ++ la.1 ++ cp.1 ++ h.1 ++ q.1 ++ g.1, g.2) := by
    simp only [osLevel, hnf, ↓reduceIte]
  rw [hpre]
  rw [hlev] at hok ⊢
  simp only at hok ⊢
  set f := osRounds c.plan lv.foldsOff lv.folds st with hf
  set m := osCommit c lvl lv f.2 with hm
  set sq := osSqueezes c lvl lv m.2 with hsq
  set la := osLam sq.2 with hla
  set cp := osCap c lvl lv la.2 with hcp
  set h := osHsMid lvl lv cp.2 with hh
  set q := osQueries c lvl lv h.2 with hq
  set g := osGlue lvl lv q.2 with hg
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hoF, hoM⟩, hoG⟩, hoS⟩, hoL⟩, hoC⟩, hoH⟩, hoQ⟩, hoGl⟩ := hok
  set D := recsDeficit recs ws.alphas with hD
  -- the folds
  obtain ⟨xs0, gs, rounds, hx0, hgl, hrl, hrd0, hrun0, hcur0, hfs0, hm0, hco0, hpad0, lg, lc⟩ :=
    osRounds_sound hcal.round hwt c.plan lv.folds lv.foldsOff st ws D hin.fs hin.mats hin.co hF.r3
      hin.claim hoF
  -- the message
  obtain ⟨x0, x1, high, n1, y0, nn, hC⟩ :=
    osCommit_sound hcal.msg hcal.g15 hcal.spf hfs0 hm0 (by rw [hpad0]; exact hin.pad) hco0
      hF.ood hoM
  set S := (oodPt (f.2.F σ) (x0 :: x1 :: high) n1 lv.logCols).2.absorbAll [y0] dsObserve with hS
  -- the query grind
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, List.map_cons, List.map_nil] at hoG
  obtain ⟨gok, hch, -⟩ := grindSqueeze_cells (s := S) (bits := queryGrind) (by decide) nn _ _
    hC.word0 hC.pow0 (hcal.g17 _ hoG)
  have hpow1 : powOk queryGrind (Keccak.lane (S.nonceState nn) 2) = true :=
    gok.resolve_left (by decide)
  -- the squeezes
  have hSq := osSqueezes_sound (c := c) (lvl := lvl) hle hcal.dec hcal.sqLoop hF.pw hF.posOff hF.sq1
    hF.sqo hF.sq5 hwt hC.mats hC.fs hC.F rfl hoS
  -- λ
  have hpadS : PadOk σ sq.2.pad := by rw [hSq.pad]; exact hC.pad
  have hL := osLam_sound hSq.fs hpadS hoL
  -- the cap
  have hmL : MatsOk σ la.2.mats := by rw [hL.mats]; exact hSq.mats
  obtain ⟨r0, r1, hcapM, lr0, lr1, hmc, hcpe⟩ := osCap_sound hcal.cap hmL hF.cap4 hoC
  -- the high part
  obtain ⟨hhs, hhse⟩ := osHsMid_sound hoH
  -- the queries
  have hmh : MatsOk σ h.2.mats := by rw [hhse]; exact hmc
  have hf3 : 2 * lv.foldsOff < u128Bound := lt_of_le_of_lt (by omega) hF.r3
  obtain ⟨hqC, hmq, hqe⟩ := osQueries_sound hmh hF.cap4 hf3 hF.hs8 hF.posOff hF.qu hoQ
  obtain ⟨hn1, hargs, hrets⟩ := osQCallOf_val hmh hF.cap4 hf3 hF.hs8 hF.posOff hF.qu hoQ
  -- the glue
  obtain ⟨hcl, lsc0, lbeta, lmu, hge⟩ := osGlue_sound hF.pwQ hoGl
  -- the states' fields
  have eq_q : q.2.lam = la.2.lam ∧ q.2.lamInv = la.2.lamInv ∧ q.2.ys = m.2.ys ∧
      q.2.claim = f.2.claim ∧ q.2.fs = la.2.fs ∧ q.2.pad = la.2.pad ∧ q.2.cb = la.2.cb ∧
      q.2.co = la.2.co := by
    rw [hqe, hhse, hcpe]
    exact ⟨rfl, rfl, rfl, by rw [hL.claim, hSq.claim]; rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨eql, eqli, eqys, eqcl, eqfs, eqpad, eqcb, eqco⟩ := eq_q
  have eq_g : g.2.fs = la.2.fs ∧ g.2.pad = la.2.pad ∧ g.2.mats = q.2.mats ∧ g.2.cb = la.2.cb ∧
      g.2.co = la.2.co := by
    rw [hge]; exact ⟨eqfs, eqpad, rfl, eqcb, eqco⟩
  obtain ⟨egfs, egpad, egmats, egcb, egco⟩ := eq_g
  have hgF : g.2.F σ = la.2.F σ := by simp only [OsSt.F, egfs]
  have hgcur : g.2.cur σ = la.2.cur σ := by simp only [OsSt.cur, egcb, egco]
  -- the root
  have er0 : r0 = (digestHalves root).1 := loadHolds_unique lr0 hin.r0
  have er1 : r1 = (digestHalves root).2 := loadHolds_unique lr1 hin.r1
  have hroot : (r0, r1) = digestHalves root := by rw [er0, er1]
  -- the positions
  set P := 128 / lv.depth with hP
  set S' := S.nonceState nn with hS'
  have hw0 : σ (.n m.2.word0) = challengeOf S' := by rw [hC.word0, Keccak.challengeOf_cells]; rfl
  set qs := sqPositions lv.depth (sqSample (challengeOf S') (capOf S')) lv.queries with hqs
  have hqsl : qs.length = lv.queries := by simp [qs, sqPositions]
  have hpos := sq_positions (rd := rd) (d := lv.depth) (cd := lv.capDepth) (po := lv.posOff)
    (S := lv.squeezes) (Q := lv.queries) (w := sqSample (challengeOf S') (capOf S'))
    (qpos := σ (.n osQpos)) (qbp := σ (.n osQbp)) (tabs := σ (.n osTabs)) hF.P1 hF.sq
    (by rw [← hw0]; exact hSq.dec)
  -- the queries' meaning
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
  obtain ⟨rounds', hsv, hrl', -, hRA, -, hosl, hopen, hidx, hwq, -, -, hret⟩ :=
    queries_open hm' hcap' hroot hcd2 hcd8 hcdd (N0 := N) (by simp [args, osQArgs, hpairs]) hF.N
      hQN (by have := hF.q0; omega) qs (by rw [hqsl])
      (fun k hk ↦ by rw [hsd]; exact (hpos k hk).2.1)
      (fun k hk ↦ by
        obtain ⟨-, -, bp, hbp, hfr⟩ := hpos k hk
        exact ⟨bp, by simpa [args, osQArgs] using hbp, by rw [hsd, hscd]; exact hfr⟩)
  -- the rounds are the stored ones
  have hrr : rounds' = rounds := rounds_eq (n := lv.folds) hrl (by rw [hrl', hsf])
    (by simpa [args, osQArgs] using hRA) (fun j hj ↦ by
      obtain ⟨a, b⟩ := lc j hj
      refine ⟨?_, ?_⟩
      · rw [loadHolds_mul_gen_pow, show 2 * lv.foldsOff + 2 * j = 2 * (lv.foldsOff + j) by ring]
        exact a
      · rw [loadHolds_mul_gen_pow, show 2 * lv.foldsOff + (2 * j + 1) = 2 * (lv.foldsOff + j) + 1 by ring]
        exact b)
  subst hrr
  have hbat : σ (.n q.2.batched) = oqChain sh.odd sh.base (args.getD 2 0)
      (fun k ↦ qwFold sh.base rounds' (wsq.getD k default)) N := by
    have := hret (by rw [hfin0]; decide)
    simpa using this
  -- the Spec's level
  set os := wsq.map (toOpening rd (args.getD 0 0) sh.cd sh.depth) with hos
  set ws1 : WhirState := { ws with claim := σ (.n f.2.claim) + gs.prod * D, alphas := ws.alphas ++ gs }
    with hws1
  have hg1 : ws1.alphas.length = lv.foldsOff + lv.folds := by simp [ws1, hin.glen, hgl]
  have hmu : logN - ws1.alphas.length = lv.logCols := by rw [hg1]; exact hF.cols
  set F3 : Fs := ((⟨capOf S', []⟩ : Fs).squeezeN (sqCount P lv.queries - 1)).2 with hF3
  have hsqF : sq.2.F σ = F3 := by rw [hSq.F, hF.sq]; rfl
  have hlam : σ (.n la.2.lam) = F3.squeeze.1 := by rw [hL.lam, hsqF]
  have hlaF : la.2.F σ = F3.squeeze.2 := by rw [hL.F, hsqF]
  set lam := F3.squeeze.1 with hlamd
  have hwlen : (os.map (·.leaf)).length = qs.length := by rw [List.length_map, hosl, hqsl]
  have hrun1 := levelNext_run logN lvl level next ws1 rounds' (f.2.F σ) R hin.R x0 x1 high
    (by rw [hC.high_len, hF.fold]) n1 y0 nn (by rw [hmu]; exact hF.cols1)
    (by rw [hmu, ← hF.depth]; exact hF.P1) (by rw [hF.queries]; exact hF.q0) hC.oodOk
    (by rw [hmu]; exact hpow1) qs (by rw [hmu, ← hF.depth, hF.queries]; rfl)
    F3 (by rw [hmu, ← hF.depth, hF.queries]; rfl) os (by rw [hosl, hqsl])
    (fun k hk ho ↦ by
      have := hopen k hk ho
      rw [hsd, hbase, hsf] at this
      exact this) hidx
  rw [hmu] at hrun1
  -- the record
  set Z0 := (oodPt (f.2.F σ) (x0 :: x1 :: high) n1 lv.logCols).1 with hZ0
  set r : OsRec := ⟨lam, lv.foldsOff + lv.folds, lv.logCols, Z0, qs, high⟩ with hr
  set ws' := glueLevel ws1 lam lv.logCols Z0 y0 qs (powers lam qs.length)
    (levelBatched lv.logCols lvl rounds' high qs (os.map (·.leaf)) lam) with hws'
  set root' := digestFromHalves (x0, x1) with hroot'
  -- the batch
  have hlinv : lam * args.getD 2 0 = 1 := by
    have := hL.inv
    simp only [args, osQArgs, hnf, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero]
    have ehli : h.2.lamInv = la.2.lamInv := by rw [hhse, hcpe]
    rw [ehli, ← hlam]; exact this
  have hchain := oqChain_mul_pow hlinv (odd := sh.odd) (base := sh.base)
    (by rw [hodd]; split_ifs <;> omega) (by rw [hbase, hodd]; split_ifs <;> simp)
    (fun k ↦ qwFold sh.base rounds' (wsq.getD k default)) N
  rw [hQN] at hchain
  have hwords : ∀ k < qs.length, (os.map (·.leaf)).getD k [] = (wsq.getD k default).2.1 := by
    intro k hk
    have hk' : k < wsq.length := by rw [← List.length_map (f := toOpening rd (args.getD 0 0) sh.cd sh.depth)]; rw [hosl]; omega
    rw [List.getD_eq_getElem _ _ (by simpa [os] using hk'), List.getD_eq_getElem _ _ hk']
    simp [os, toOpening]
  have hfoldsum : ∑ k ∈ Finset.range qs.length, lam ^ k *
      foldRow (specLanes lvl ((os.map (·.leaf)).getD k [])) (K.ofBits (qs.getD k 0)) rounds' =
        lam ^ lv.queries * σ (.n q.2.batched) := by
    rw [hbat, hchain, powSum, hqsl]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    rw [hwords k (by omega), ← hwq k hk', qwFold, hbase, lanesOf_base]
  have hB := levelBatched_eq lv.logCols lvl rounds' high qs (os.map (·.leaf)) hwlen lam
  rw [hfoldsum] at hB
  -- the claim
  have hclaim : ws'.claim = σ (.n g.2.claim) + recsDeficit (recs ++ [r]) (ws.alphas ++ gs) := by
    show ws1.claim + lam * y0 + lam * lam *
      levelBatched lv.logCols lvl rounds' high qs (os.map (·.leaf)) lam = _
    rw [hB, recsDeficit_snoc _ _ _ (by simp [r, hin.glen, hgl]),
      recsDeficit_append_alphas _ _ _ hin.recF, hcl]
    have e1 : σ (.n q.2.lam) = lam := by rw [eql, hlam]
    have e2 : σ (.n (q.2.ys.getD 0 0)) = y0 := by rw [eqys]; exact hC.ys.2
    rw [e1, e2, eqcl]
    simp only [ws1, recH, r, hqsl]
    ring
  -- the reads
  have hxs1 : ReadsAt rd (st.cur σ) (xs0 ++ (x0 :: x1 :: high ++ [n1, y0, nn])) :=
    readsAt_append hrd0 (by rw [hx0, ← hcur0]; exact hC.reads)
  refine ⟨xs0 ++ (x0 :: x1 :: high ++ [n1, y0, nn]), ws', r, root', ?_, hxs1, ?_, ?_, ?_, ?_,
    gs, by simp [ws', glueLevel, ws1], hgl⟩
  · simp [lvWords, hnf, hx0, hC.high_len]
  · -- the run
    have h0 := RunsTo.withRoots hrun0 R
    rw [hF.fold]
    have hW : osLevelW rd V lvl lv (osQCallOf c lvl lv h.2).1 ((osQCallOf c lvl lv h.2).2.1.map σ)
        ((osQCallOf c lvl lv h.2).2.2.map σ) = os := by
      simp only [osLevelW, hn1, hargs, hrets, hshape, hloop]
      rw [← hscd, ← hsd]
      rfl
    refine RunsWith.of_eq (RunsWith.bind' h0 hrun1) rfl rfl (by rw [hW]; rfl) rfl rfl ?_ ?_
    · rw [hgF, hlaF]
    · rw [hF.shape]
  · -- the next level's start
    refine ⟨?_, ?_, ?_, ?_, hclaim, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [egfs]; exact hL.fs
    · rw [egco, hL.co, hSq.co, hC.co]; unfold u128Bound; norm_num
    · rw [egpad]; exact hL.pad
    · rw [egmats]; exact hmq
    · simp [ws', glueLevel, ws1, hin.glen, hgl, hF.off']
    · intro j hj
      simp only [ws', glueLevel, ws1] at hj ⊢
      by_cases hj0 : j < ws.alphas.length
      · rw [List.getElem_append_left hj0]; exact hin.fch j hj0
      · rw [List.getElem_append_right (by omega)]
        have := lg (j - ws.alphas.length) (by simp at hj; omega)
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hj; omega),
          Option.getD_some, ← hin.glen, Nat.add_sub_cancel' (by omega)] at this
        exact this
    · simp [hin.rlen]
    · rw [List.getElem?_append_right (by rw [hin.rlen]), hin.rlen, Nat.sub_self]; rfl
    · rw [show 2 * (lvl + 1) = 2 * lvl + 2 by ring, digestScalars_digestOfScalars]; exact hC.root0
    · rw [show 2 * (lvl + 1) + 1 = 2 * lvl + 3 by ring, digestScalars_digestOfScalars]
      exact hC.root1
    · simp only [ws', glueLevel, ws1, hin.glued, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, recGlued, r, List.length_append, hin.glen, hgl]
    · intro r' hr'
      simp only [ws', glueLevel, ws1, List.length_append, hgl]
      rcases List.mem_append.mp hr' with h1 | h1
      · have := hin.recF r' h1; omega
      · simp only [List.mem_singleton] at h1; subst h1; simp [r, hin.glen]
  · -- the record
    have e1 : σ (.n q.2.lam) = r.lam := by rw [eql, hlam]
    refine ⟨rfl, rfl, hqsl, ?_, ?_, ?_, hC.ood, ?_, ?_, ?_, ?_⟩
    · exact hC.high_len
    · rw [← e1]; exact lsc0
    · show Z0.length = lv.logCols
      rw [hZ0, oodPt_eq]
      simp only [List.length_cons, squeezeN_length]
      have := hF.cols1; omega
    · rw [← e1]; exact lbeta
    · refine ⟨σ (.n q.2.lamInv), lmu, ?_⟩
      rw [← e1, eql, eqli]; exact hL.inv
    · intro cc hcc
      obtain ⟨v, hv1, hv2⟩ := hhs cc hcc
      have hs' : (osCap c lvl lv la.2).2.sent = m.2.sent := by rw [hcpe]; rfl
      rw [hs'] at hv1
      have hlt : 2 + cc < (x0 :: x1 :: high).length := by simp [hC.high_len]; omega
      have := hC.sent (2 + cc) hlt
      rw [loadHolds_unique hv1 this] at hv2
      convert hv2 using 2
      rw [List.getD_eq_getElem _ _ (by rw [hC.high_len]; exact hcc)]
      simp [show 2 + cc = cc + 1 + 1 by ring, r]
    · intro k hk
      have := (hpos k hk).1
      rwa [loadHolds_mul_gen_pow] at this
  · rw [hgcur, hL.cur, hSq.cur, hC.cur, hcur0]
    simp only [List.length_append, List.length_cons, hx0, hC.high_len, List.length_nil]
    ring

end
end LeanVM.Guest.B1.Whir
