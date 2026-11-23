/-
  LeanVM.Guest.B1.Whir.LevelMid

  A non-final level of `open_stacked` runs the Spec's: its fold rounds, then `levelNext`.
-/

module

public import LeanVM.Guest.B1.Whir.Level

/-!
# A non-final level, soundly

`osLevelMid_sound`: from `LvIn`, a non-final level's template runs `foldRounds` then
`levelNext`, reading `lvWords` words at the cursor and one phase of openings (the witness's,
`osLevelW` at the level's `level_queries` call), and leaves the next level's `LvIn`, the
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

/-- The rates' values the level appends to `rts`. -/
theorem osRates_rts (c : OsCfg) (lvl : ℕ) (st : OsSt) :
    (osRates c lvl st).2.rts = st.rts ++ [[st.k + 1 + 2 * 0 + 1, st.k + 1 + 2 * 1 + 1,
      st.k + 1 + 2 * 2 + 1, st.k + 1 + 2 * 3 + 1]] := rfl

theorem rtOk_of {σ : Val} {k : ℕ} {lv : OsLv}
    (h : ∀ i < 4, σ (.n (k + 1 + 2 * i + 1)) = gw ((osRateVals lv).getD i 0)) :
    RtOk σ [k + 1 + 2 * 0 + 1, k + 1 + 2 * 1 + 1, k + 1 + 2 * 2 + 1, k + 1 + 2 * 3 + 1] lv := by
  intro j hj
  interval_cases j
  exacts [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

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
        [osLevelW rd V c lvl lv ((osQCallOf c lvl lv (osPreQ c lvl lv st)).1.map σ)
          ((osQCallOf c lvl lv (osPreQ c lvl lv st)).2.map σ)]
        R ws' ((osLevel c lvl lv st).2.F σ) (R ++ [(root', lv'.depth, lvWidth (lvl + 1) lv')]) ∧
      LvIn rd σ (lvl + 1) lv' (osLevel c lvl lv st).2 ws' (recs ++ [r])
        (R ++ [(root', lv'.depth, lvWidth (lvl + 1) lv')]) root' ∧
      RecStored rd σ lvl lv r ∧
      (osLevel c lvl lv st).2.cur σ = st.cur σ * gen ^ xs.length ∧
      (∃ gs, ws'.alphas = ws.alphas ++ gs ∧ gs.length = lv.folds) ∧
      ∃ e, (osLevel c lvl lv st).2.rts = st.rts ++ [e] ∧ RtOk σ e lv := by
  obtain ⟨loop, sh, hmem, hent, hbase, hsf, hspd, hfin0, hcd2, hcd8, hcdd⟩ := hF.qsh
  have hpdd : sh.pd + lv.capDepth = lv.depth := by rw [hspd]; omega
  have hnf := hF.nf
  obtain ⟨hshape, hloop⟩ := oqEntry_shape hent
  -- the blocks
  have hpre : osPreQ c lvl lv st = (osHsMid lvl lv (osLam (osPositions c lvl (osQGrind
      (osCommit c lvl lv (osRounds true lv.foldsOff lv.folds (osRates c lvl st).2).2).2).2).2).2).2 := by
    simp only [osPreQ, hnf, ↓reduceIte]
  have hlev : osLevel c lvl lv st =
      let rt := osRates c lvl st
      let f := osRounds true lv.foldsOff lv.folds rt.2
      let m := osCommit c lvl lv f.2
      let gr := osQGrind m.2
      let sq := osPositions c lvl gr.2
      let la := osLam sq.2
      let h := osHsMid lvl lv la.2
      let q := osQueries c lvl lv h.2
      let g := osGlue lvl q.2
      (rt.1 ++ f.1 ++ m.1 ++ gr.1 ++ sq.1 ++ la.1 ++ h.1 ++ q.1 ++ g.1, g.2) := by
    simp only [osLevel, hnf, ↓reduceIte]
  rw [hpre]
  rw [hlev] at hok ⊢
  simp only at hok ⊢
  set rt := osRates c lvl st with hrt
  set f := osRounds true lv.foldsOff lv.folds rt.2 with hf
  set m := osCommit c lvl lv f.2 with hm
  set gr := osQGrind m.2 with hgr
  set sq := osPositions c lvl gr.2 with hsq
  set la := osLam sq.2 with hla
  set h := osHsMid lvl lv la.2 with hh
  set q := osQueries c lvl lv h.2 with hq
  set g := osGlue lvl q.2 with hg
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hoR, hoF⟩, hoM⟩, hoG⟩, hoS⟩, hoL⟩, hoH⟩, hoQ⟩, hoGl⟩ := hok
  set D := recsDeficit recs ws.alphas with hD
  -- the rates
  obtain ⟨hrv, hlpv, hlwv⟩ := osRates_sound hcal.rate hoR
  have hpo : lv.posOff < u128Bound := hF.posOff
  have hfe : ∃ k fs co claim, f.2 = { rt.2 with k := k, fs := fs, co := co, claim := claim } :=
    osRounds_snd true lv.foldsOff lv.folds rt.2
  obtain ⟨_, _, _, _, hfe⟩ := hfe
  have hflp : f.2.lp = rt.2.lp := by rw [hfe]
  have hflw : f.2.lw = rt.2.lw := by rw [hfe]
  have hfrts : f.2.rts = rt.2.rts := by rw [hfe]
  -- the folds
  have hpz : PadZ σ (rt.2.pad.getD osPadV) := by
    obtain ⟨p, hp⟩ := hin.pads
    have := hin.pad p hp
    show PadZ σ (st.pad.getD osPadV)
    rw [hp]; exact this
  obtain ⟨xs0, gs, rounds, hx0, hgl, hrl, hrd0, hrun0, hcur0, hfs0, hm0, hco0, -, hpad0, lg, lc⟩ :=
    osRounds_sound hcal.gc hwt true lv.folds lv.foldsOff rt.2 ws D hin.fs hpz hin.claim hoF
  replace hcur0 : f.2.cur σ = st.cur σ * gen ^ (5 * lv.folds) := hcur0
  replace hrd0 : ReadsAt rd (st.cur σ) xs0 := hrd0
  have hmF : MatsOk σ f.2.mats := by rw [hm0]; exact hin.mats
  have hcoF : f.2.co < u128Bound := by
    rw [hco0]
    have := hin.co; have := hF.f5
    show st.co + 5 * lv.folds < u128Bound
    omega
  -- the message
  obtain ⟨x0, x1, high, n1, y0, nn, hC⟩ :=
    osCommit_sound hcal.msg hcal.gc hwt hcal.spf hfs0 hmF (by rw [hpad0]; exact hin.pad) hcoF
      hF.ood hoM
  set S := (oodPt (f.2.F σ) (x0 :: x1 :: high) n1 lv.logCols).2.absorbAll [y0] dsObserve with hS
  -- the query grind
  have hgq := hcal.gc queryGrind m.2.k (.n m.2.pow0) (.n osTabs) (by decide) hwt hoG
  obtain ⟨gok, hch, -⟩ := grindSqueeze_cells (s := S) (bits := queryGrind) (by decide) nn _ _
    hC.word0 hC.pow0 hgq
  have hpow1 : powOk queryGrind (Keccak.lane (S.nonceState nn) 2) = true :=
    gok.resolve_left (by decide)
  -- the positions
  have hsq5 := hF.sq5
  have hsqv : σ (.n ((gr.2.rts.getLast?.getD []).getD 1 0)) = gen ^ lv.squeezes := by
    have e : gr.2.rts = st.rts ++ [[st.k + 1 + 2 * 0 + 1, st.k + 1 + 2 * 1 + 1,
        st.k + 1 + 2 * 2 + 1, st.k + 1 + 2 * 3 + 1]] := hfrts.trans (osRates_rts c lvl st)
    rw [e, List.getLast?_append, List.getLast?_singleton, Option.some_or]
    have := hrv 1 (by decide)
    simp only [Option.getD_some, List.getD_cons_succ, List.getD_cons_zero]
    rw [this]
    exact gw_eq (by simp [osRateVals]; unfold u128Bound at *; omega)
  have hSq := osPositions_sound hcal.lp hcal.rate hwt
    (st := gr.2) (by rw [show gr.2.lp = rt.2.lp from hflp, hlpv, gw_eq hpo])
    (by rw [show gr.2.lw = rt.2.lw from hflw, hlwv, gw_eq hpo]) hsqv hC.mats hC.fs hC.F rfl hoS
  -- λ
  have hpadS : PadOk σ sq.2.pad := by rw [hSq.pad]; exact hC.pad
  have hL := osLam_sound hSq.fs hcal.iz hpadS hoL
  -- the high part
  obtain ⟨hhs, hhse⟩ := osHsMid_sound hoH
  -- the queries
  have hmh : MatsOk σ h.2.mats := by rw [hhse, hL.mats]; exact hSq.mats
  have hf3 : 2 * lv.foldsOff < u128Bound := lt_of_le_of_lt (by omega) hF.r3
  obtain ⟨hargs, hcapC, h13, h15, hqC, ebat, epow, lr0, lr1, hmq, hqe⟩ :=
    osLq_sound hU hcal.rate hcal.lq hF.it hcd8 hF.pwQ hmh hf3 hF.hs8
      (by rw [show h.2.lp = rt.2.lp from hflp, hlpv, gw_eq hpo])
      (by rw [show h.2.lw = rt.2.lw from hflw, hlwv, gw_eq hpo]) hoQ
  set A := osQArgs σ c lvl lv h.2 with hA
  set Vq := V (osQueriesName c lvl lv) A ((osQCallOf c lvl lv h.2).2.map σ) with hVq
  have hcapM := hcal.cap _ _ hcapC
  -- the glue
  obtain ⟨hcl, lsc0, lbeta, lmu, hge⟩ := osGlue_sound hoGl
  -- the states' fields
  have eq_q : q.2.lam = la.2.lam ∧ q.2.lamInv = la.2.lamInv ∧ q.2.ys = m.2.ys ∧
      q.2.claim = f.2.claim ∧ q.2.fs = la.2.fs ∧ q.2.pad = la.2.pad ∧ q.2.cb = la.2.cb ∧
      q.2.co = la.2.co := by
    rw [hqe, hhse]
    exact ⟨rfl, rfl, rfl, by rw [hL.claim, hSq.claim]; rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨eql, eqli, eqys, eqcl, eqfs, eqpad, eqcb, eqco⟩ := eq_q
  have eq_g : g.2.fs = la.2.fs ∧ g.2.pad = la.2.pad ∧ g.2.mats = q.2.mats ∧ g.2.cb = la.2.cb ∧
      g.2.co = la.2.co := by
    rw [hge]; exact ⟨eqfs, eqpad, rfl, eqcb, eqco⟩
  obtain ⟨egfs, egpad, egmats, egcb, egco⟩ := eq_g
  have hgF : g.2.F σ = la.2.F σ := by simp only [OsSt.F, egfs]
  have hgcur : g.2.cur σ = la.2.cur σ := by simp only [OsSt.cur, egcb, egco]
  have hgrts : g.2.rts = f.2.rts := by rw [hge, hqe, hhse]; rfl
  -- the root
  have hroot : (Vq (.n 10), Vq (.n 11)) = digestHalves root := by
    rw [loadHolds_unique lr0 hin.r0, loadHolds_unique lr1 hin.r1]
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
  set N := lv.queries / (1 + lvBase lvl) with hN
  set odd := lv.queries % (1 + lvBase lvl) with hodd
  set args := osOqArgs Vq A N odd with hargsd
  obtain ⟨fm, hfind, hpar, hhold⟩ := hU _ _ _ hqC
  have hQN : oqCount odd sh.base N = lv.queries := by rw [hbase]; exact lvCount _ _
  have hob : sh.base = 1 ∨ odd = 0 := by
    rw [hbase]; by_cases h0 : lvl = 0 <;> simp [odd, lvBase, h0, Nat.mod_one]
  have hodd1 : odd ≤ 1 := le_trans (lvOdd_le _ _) (by unfold lvBase; split_ifs <;> omega)
  have hsw := opening_queries_all_sound_w _ hmem lv.capDepth (by omega) hcd8 rd C V hU hle fm _ args _
    N odd hfind hpar hhold (by simp [args, osOqArgs]) hF.N (by simp [args, osOqArgs])
    (by rw [hbase]; exact lvOdd_le _ _) (by
      rw [hQN, hpdd]
      intro k hk x bp hx hbp
      obtain ⟨hl1, hlt, bp', hbp', hfr⟩ := hpos k hk
      refine ⟨_, hlt, loadHolds_unique hx hl1, ?_⟩
      rw [loadHolds_unique hbp hbp']
      exact hfr)
  simp only at hsw
  set wsq := oqsOf sh.oq lv.capDepth odd loop N rd (V (osOqName c lvl lv) args [Vq (.n 18)]) V
    with hwsq
  have hm' : MeaningOpeningQueriesW sh lv.capDepth rd wsq [args.getD 0 0, args.getD 1 0, args.getD 2 0,
      args.getD 3 0, args.getD 4 0, args.getD 5 0, args.getD 6 0, args.getD 7 0, args.getD 8 0]
      [Vq (.n 18)] := by
    have e : args = [args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0,
        args.getD 5 0, args.getD 6 0, args.getD 7 0, args.getD 8 0] := by
      simp only [hargsd, osOqArgs, List.getD_cons_zero, List.getD_cons_succ]
    rw [← e]; exact hsw
  obtain ⟨rounds', hsv, hrl', -, hRA, -, hosl, hopen, hidx, hwq, -, -, hret⟩ :=
    queries_open hm' (by simp [args, osOqArgs, h13]) (by simp [args, osOqArgs, h15]) hcapM hroot
      hcd2 hcd8 (by rw [hbase]; unfold lvBase; split_ifs <;> omega) (N0 := N)
      (by simp [args, osOqArgs]) hF.N (odd0 := odd) (by simp [args, osOqArgs]) hodd1
      hQN (by have := hF.q0; omega) qs (by rw [hqsl])
      (fun k hk ↦ by rw [hpdd]; exact (hpos k hk).2.1)
      (fun k hk ↦ by
        obtain ⟨-, -, bp, hbp, hfr⟩ := hpos k hk
        exact ⟨bp, by simpa [args, osOqArgs, A, osQArgs] using hbp, by rw [hpdd]; exact hfr⟩)
  rw [hpdd] at hosl hopen hidx
  -- the rounds are the stored ones
  have hrr : rounds' = rounds := rounds_eq (n := lv.folds) hrl (by rw [hrl', hsf])
    (by simpa [args, osOqArgs, A, osQArgs] using hRA) (fun j hj ↦ by
      obtain ⟨a, b⟩ := lc j hj
      refine ⟨?_, ?_⟩
      · rw [loadHolds_mul_gen_pow, show 2 * lv.foldsOff + 2 * j = 2 * (lv.foldsOff + j) by ring]
        exact a
      · rw [loadHolds_mul_gen_pow, show 2 * lv.foldsOff + (2 * j + 1) = 2 * (lv.foldsOff + j) + 1 by ring]
        exact b)
  subst hrr
  have hbat : σ (.n q.2.batched) = oqChain odd sh.base (args.getD 2 0)
      (fun k ↦ qwFold sh.base rounds' (wsq.getD k default)) N := by
    have := hret (by rw [hfin0]; decide)
    rw [ebat]
    simpa using this
  -- the Spec's level
  set os := wsq.map (toOpening rd (Vq (.n 7)) lv.capDepth lv.depth) with hos
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
      rw [hbase, hsf] at this
      exact this) hidx
  rw [hmu] at hrun1
  -- the record
  set Z0 := (oodPt (f.2.F σ) (x0 :: x1 :: high) n1 lv.logCols).1 with hZ0
  set r : OsRec := ⟨lam, lv.foldsOff + lv.folds, lv.logCols, Z0, qs, high⟩ with hr
  set ws' := glueLevel ws1 lam lv.logCols Z0 y0 qs (powers lam qs.length)
    (levelBatched lv.logCols lvl rounds' high qs (os.map (·.leaf)) lam) with hws'
  set root' := digestFromHalves (x0, x1) with hroot'
  -- the batch
  have hlinv : lam ≠ 0 → lam * args.getD 2 0 = 1 := by
    have := hL.inv
    simp only [args, osOqArgs, A, osQArgs, hnf, ↓reduceIte, List.getD_cons_succ, List.getD_cons_zero]
    have ehli : h.2.lamInv = la.2.lamInv := by rw [hhse]
    rw [ehli, ← hlam]; exact this
  have hwords : ∀ k < qs.length, (os.map (·.leaf)).getD k [] = (wsq.getD k default).2.1 := by
    intro k hk
    have hk' : k < wsq.length := by
      rw [← List.length_map (f := toOpening rd (Vq (.n 7)) lv.capDepth lv.depth)]; rw [hosl]; omega
    rw [List.getD_eq_getElem _ _ (by simpa [os] using hk'), List.getD_eq_getElem _ _ hk']
    simp [os, toOpening]
  have hfoldsum : lam * lam * ∑ k ∈ Finset.range qs.length, lam ^ k *
      foldRow (specLanes lvl ((os.map (·.leaf)).getD k [])) (K.ofBits (qs.getD k 0)) rounds' =
        lam * lam * (lam ^ lv.queries * σ (.n q.2.batched)) := by
    by_cases hl0 : lam = 0
    · simp [hl0]
    have hchain := oqChain_mul_pow (hlinv hl0) (odd := odd) (base := sh.base) hodd1 hob
      (fun k ↦ qwFold sh.base rounds' (wsq.getD k default)) N
    rw [hQN] at hchain
    rw [hbat, hchain, powSum, hqsl]
    refine congrArg (lam * lam * ·) (Finset.sum_congr rfl fun k hk ↦ ?_)
    have hk' := Finset.mem_range.mp hk
    rw [hwords k (by omega), ← hwq k hk', qwFold, hbase, lanesOf_base]
  have hB : lam * lam * levelBatched lv.logCols lvl rounds' high qs (os.map (·.leaf)) lam =
      lam * lam * (lam ^ lv.queries * σ (.n q.2.batched) +
        ∑ k ∈ Finset.range qs.length, lam ^ k * highTerm lv.logCols high (qs.getD k 0)) := by
    rw [levelBatched_eq lv.logCols lvl rounds' high qs (os.map (·.leaf)) hwlen lam, mul_add,
      hfoldsum, mul_add]
  -- `λ^n`
  have epow' : σ (.n q.2.lamPow) = σ (.n q.2.lam) ^ lv.queries := by
    rw [epow, eql, hA]
    simp only [osQArgs, hnf, ↓reduceIte, List.getD_cons_zero]
    rfl
  -- the claim
  have hclaim : ws'.claim = σ (.n g.2.claim) + recsDeficit (recs ++ [r]) (ws.alphas ++ gs) := by
    show ws1.claim + lam * y0 + lam * lam *
      levelBatched lv.logCols lvl rounds' high qs (os.map (·.leaf)) lam = _
    rw [hB, recsDeficit_snoc _ _ _ (by simp [r, hin.glen, hgl]),
      recsDeficit_append_alphas _ _ _ hin.recF, hcl]
    have e1 : σ (.n q.2.lam) = lam := by rw [eql, hlam]
    have e2 : σ (.n (q.2.ys.getD 0 0)) = y0 := by rw [eqys]; exact hC.ys.2
    rw [epow', e1, e2, eqcl]
    simp only [ws1, recH, r, hqsl]
    ring
  -- the reads
  have hxs1 : ReadsAt rd (st.cur σ) (xs0 ++ (x0 :: x1 :: high ++ [n1, y0, nn])) :=
    readsAt_append hrd0 (by rw [hx0, ← hcur0]; exact hC.reads)
  have hrts' : g.2.rts = st.rts ++ [[st.k + 1 + 2 * 0 + 1, st.k + 1 + 2 * 1 + 1,
      st.k + 1 + 2 * 2 + 1, st.k + 1 + 2 * 3 + 1]] := (hgrts.trans hfrts).trans (osRates_rts c lvl st)
  refine ⟨xs0 ++ (x0 :: x1 :: high ++ [n1, y0, nn]), ws', r, root', ?_, hxs1, ?_, ?_, ?_, ?_,
    ⟨gs, by simp [ws', glueLevel, ws1], hgl⟩, _, hrts', rtOk_of hrv⟩
  · simp [lvWords, hnf, hx0, hC.high_len]
  · -- the run
    have h0 := RunsTo.withRoots hrun0 R
    rw [hF.fold]
    have hW : osLevelW rd V c lvl lv ((osQCallOf c lvl lv h.2).1.map σ)
        ((osQCallOf c lvl lv h.2).2.map σ) = os := by
      simp only [osLevelW, hargs, hshape, hloop]
      rfl
    refine RunsWith.of_eq (RunsWith.bind' h0 hrun1) rfl rfl (by rw [hW]; rfl) rfl rfl ?_ ?_
    · rw [hgF, hlaF]
    · rw [hF.shape]
  · -- the next level's start
    refine ⟨?_, ?_, ?_, ?_, ?_, hclaim, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [egfs]; exact hL.fs
    · rw [egco, hL.co, hSq.co, show gr.2.co = m.2.co from rfl, hC.co]
    · rw [egpad]; exact hL.pad
    · rw [egpad]; exact ⟨_, rfl⟩
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
    · rw [hrts', List.length_append, hin.rtl]; rfl
  · -- the record
    have e1 : σ (.n q.2.lam) = r.lam := by rw [eql, hlam]
    refine ⟨rfl, rfl, hqsl, ?_, ?_, ?_, hC.ood, ?_, ?_, ?_, ?_⟩
    · exact hC.high_len
    · rw [← e1]; exact lsc0
    · show Z0.length = lv.logCols
      rw [hZ0, oodPt_eq]
      simp only [List.length_cons, squeezeN_length]
      have := hF.cols1; omega
    · rw [← e1, ← epow']; exact lbeta
    · refine ⟨σ (.n q.2.lamInv), lmu, ?_⟩
      rw [← e1, eql, eqli]; exact hL.inv
    · intro cc hcc
      obtain ⟨v, hv1, hv2⟩ := hhs cc hcc
      have hs' : la.2.sent = m.2.sent := rfl
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
  · rw [hgcur, hL.cur, hSq.cur, show gr.2.cur σ = m.2.cur σ from rfl, hC.cur, hcur0]
    simp only [List.length_append, List.length_cons, hx0, hC.high_len, List.length_nil]
    ring

end
end LeanVM.Guest.B1.Whir
