/-
  LeanVM.Guest.B1.Whir.StackedSound

  `open_stacked` is sound at a configuration: its relation gives `OpenOut`.
-/

module

public import LeanVM.Guest.B1.Whir.StackedInner

/-!
# `open_stacked`, soundness at a configuration (TRIAGE #36)

`open_stacked_sound`: at a configuration whose facts (`OsCfgOk`, decided per candidate) match the
specification's ladder and whose callees have their meanings (`OsCallees`), the relation of a
function whose body is `osBody cfg` gives group 6's `OpenOut`: the stream words and the openings
the guest reads, over which `whirOpen` runs to the end the guest returns.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The head -/

theorem osHead_noRet (cfg : OsCfg) : Stmt.noRetList (osHead cfg).1 = true := by
  simp [osHead, osHeap, osFsNext, fsNextT, fsCompressT, Stmt.noRetList, Stmt.noRet]

/-- **The head** (G:1062-1094): the first quadratic read from the chain state of `fs0, fs1`
(`sumcheckRoundPoly 3 target none`), the stack's root at the first root slot: the invariant at
level `0`. -/
theorem osHead_sound {cfg : OsCfg} {logN : ℕ} (hoff : (cfg.lv 0).foldsOff = 0) {fs0 fs1 target root0 root1 cur : E}
    {root : Digest} (hroot : (root0, root1) = digestScalars root)
    (hσ : σ (.n 0) = fs0 ∧ σ (.n 1) = fs1 ∧ σ (.n 2) = target ∧ σ (.n 3) = root0 ∧ σ (.n 4) = root1 ∧
      σ (.n 5) = cur) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osHead cfg).1 True kret) :
    ∃ (cv : Digest) (x0 x1 : E), (fs0, fs1) = digestScalars cv ∧
      OsLvInv rd σ cfg logN cur 0 (osHead cfg).2 (obsCv (obsCv cv x0) x1) [x0, x1]
        ⟨target, [x0, target + x1, x1], [], []⟩
        [(root, (cfg.lv 0).depth, oqR 1 (2 ^ (cfg.lv 0).folds))] := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hσ
  unfold osHead at h ⊢
  simp only at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨hc, h⟩ := holdsList_true_of (by rfl) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hc
  obtain ⟨hx, h⟩ := holdsList_true_of (by rfl) h
  have hx' := hx
  rw [osFsNext, holds_fsNextT] at hx'
  obtain ⟨⟨-, cv, hcv, -⟩, -⟩ := hx'
  have hat0 : OsCur rd σ cur ⟨8, 6, 7, 5, 0, 0, 0, 0, 2⟩ cv [] :=
    ⟨hcv, readsAt_nil _ _, by show σ (.n 5) * gen ^ 0 = cur * gen ^ 0; rw [e5]⟩
  have hat1 := osFsNext_sound hat0 hx
  obtain ⟨hy, h⟩ := holdsList_true_of (by rfl) h
  have hat2 := osFsNext_sound hat1 hy
  obtain ⟨hadd, h⟩ := holdsList_true_of (by rfl) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hadd
  simp only [osHeap, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, and_true] at h
  obtain ⟨-, -, -, -, l3, l4, -⟩ := h
  refine ⟨cv, σ (.n 8), σ (.n 23), by rw [← e0, ← e1, ← hc.1, ← hc.2]; exact hcv,
    ⟨hat2.fs, hat2.reads, hat2.cursor⟩, by decide, ?_, e2.symm, by rw [hoff]; rfl,
    fun j hj => absurd hj (by simp), rfl, ⟨root, by simp, ?_, ?_⟩, ⟨[], rfl, rfl, fun i hi => absurd hi (by simp)⟩⟩
  · show [σ (.n 8), target + σ (.n 23), σ (.n 23)] = [σ (.n 8), σ (.n 38), σ (.n 23)]
    rw [hadd, e2]
  · rw [← (congrArg Prod.fst hroot : root0 = _), ← e3]; exact l3
  · rw [← (congrArg Prod.snd hroot : root1 = _), ← e4]; exact l4

/-! ## The residual chains, every level -/

private theorem zipIdx_map_range' {α β : Type} [Inhabited α] (f : α × ℕ → β) (l : List α) :
    l.zipIdx.map f = (List.range l.length).map fun i => f (l.getD i default, i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

theorem osResiduals_sound {cfg : OsCfg} {ich ba bb k : ℕ}
    (hres : ∀ i < cfg.levels.length, ∃ fn, coreProgram.find? (cfg.lv i).resLoop = some fn ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧ fn.body = resLoopOf cfg i (cfg.lv i))
    (hcols : ∀ i < cfg.levels.length, 1 ≤ (cfg.lv i).logCols ∧ (cfg.lv i).queries < 2 ^ 62)
    {kret : List E → Prop} {C : CallRel}
    (hC : ∀ i < cfg.levels.length, ∀ a, a.length = 7 → C (cfg.lv i).resLoop a [] → coreProgram.Rel rd (cfg.lv i).resLoop a [])
    (h : Stmt.HoldsList C rd σ (osResiduals cfg.maxQ ich ba bb k cfg.levels) True kret) :
    ∀ i < cfg.levels.length, ∃ rc : E, (∀ x < (cfg.lv i).queries, ResBody rd (cfg.lv i).posOff (i * 22)
        (cfg.lv i).logCols (i * cfg.maxQ) (cfg.lv i).vals (σ (.n osQpos)) (σ (.n ba)) (σ (.n bb)) rc
        (σ (.n osQw)) (gen ^ x)) ∧ LoadHolds rd rc 0 0 ∧
      ∃ i0 b r, LoadHolds rd (σ (.n ich)) i i0 ∧ LoadHolds rd (σ (.n osBetas)) i b ∧
        LoadHolds rd rc (cfg.lv i).queries r ∧ LoadHolds rd (σ (.n ich)) (i + 1) (i0 + b * r) := by
  unfold osResiduals at h
  rw [zipIdx_map_range', holdsList_range_flatten _ _ (fun _ => rfl)] at h
  intro i hi
  obtain ⟨fn, hf, hp, hb⟩ := hres i hi
  exact osResidual_sound hf hp hb (hcols i hi).1 (hcols i hi).2 (hC i hi) (h.1 i hi)

/-! ## The configuration and the callees -/

/-- A configuration's facts against the specification's ladder `Lall` for the candidate
`(μ, r)`, decided per candidate. -/
structure OsCfgOk (cfg : OsCfg) (μ r : ℕ) (Lall : List Whir.Level) : Prop where
  config : deriveConfig μ r = some Lall
  len : Lall.length = cfg.levels.length
  len2 : 2 ≤ cfg.levels.length
  spec : ∀ i < Lall.length, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1))
  lane : (Lall.head?.map (·.fold)).getD 0 = (cfg.lv 0).folds
  off0 : (cfg.lv 0).foldsOff = 0
  shape : stackShape μ r = ((cfg.lv 0).depth, 2 ^ (cfg.lv 0).folds)
  yr2 : 2 ≤ cfg.yrLog
  yr5 : cfg.yrLog ≤ 5
  yrLevel : cfg.yrLevel = cfg.levels.length - 1
  nFolds : osLevelF cfg (cfg.levels.length - 1) = cfg.nFolds
  total : cfg.nFolds + cfg.yrLog = μ
  laneLe : (cfg.lv 0).folds ≤ cfg.nFolds
  pt42 : cfg.nFolds + cfg.yrLog ≤ 42
  ood : ∀ lv ∈ cfg.levels.tail, lv.oodHere = 1
  lvs : ∀ i < cfg.levels.length, (cfg.lv i).prefixLen = cfg.nFolds - osLevelF cfg i ∧
    (cfg.lv i).resFoldOff = osLevelF cfg i ∧ (cfg.lv i).prefixLen + cfg.yrLog = (cfg.lv i).logCols ∧
    osLevelF cfg i ≤ cfg.nFolds ∧ OsTablesOkK (cfg.lv i)

/-- The callees of a configuration, as their meanings, and its residual loops. -/
structure OsCallees (rd : Reader) (cfg : OsCfg) : Prop where
  lv : ∀ i < cfg.levels.length, LvCallees rd cfg i
  fin : ∀ a r, coreProgram.Rel rd cfg.finalMsg a r → MeaningOpeningFinalMessage cfg.yrLen rd a r
  ff : ∀ a r, coreProgram.Rel rd cfg.foldFinal a r → MeaningFoldFinalMsg cfg.yrLog rd a r
  res : ∀ i < cfg.levels.length, ∃ fn, coreProgram.find? (cfg.lv i).resLoop = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧ fn.body = resLoopOf cfg i (cfg.lv i)

private theorem readsAt_getD {p : E} {l : List E} (h : ReadsAt rd p l) :
    ∀ j < l.length, LoadHolds rd p j (l.getD j 0) := fun j hj => by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]; exact h j hj

theorem osTail_noRet (yrLog : ℕ) (s : OsSt) : Stmt.noRetList (osTail yrLog s).1 = true := by
  unfold osTail
  simp only [noRetList_append, osFolds_noRet]
  rw [noRetList_flatten_range _ _ (fun _ => rfl)]
  rfl

theorem osBases_noRet (yrLog tch ba bb : ℕ) : ∀ (lvl : ℕ) (lvs : List OsLvl) (k : ℕ),
    Stmt.noRetList (osBases yrLog tch ba bb lvl lvs k).1 = true
  | _, [], _ => rfl
  | lvl, lv :: rest, k => by
    have hnr : ∀ items k', Stmt.noRetList (osBasisRow ba bb items k').1 = true := by
      intro items
      induction items with
      | nil => intro; rfl
      | cons it rest ih =>
        intro k'
        obtain ⟨slot, src, inv⟩ := it
        simp only [osBasisRow, noRetList_append, ih, Bool.and_true]
        unfold osBasisBlk; split <;> rfl
    simp only [osBases, noRetList_append, hnr, osBases_noRet yrLog tch ba bb (lvl + 1) rest, Bool.and_self]

theorem osOodWeights_noRet (yrLog tch : ℕ) : ∀ (prev ol : ℕ) (lvs : List OsLvl) (acc : Option ℕ) (k : ℕ),
    (∀ lv ∈ lvs, lv.oodHere = 1) → Stmt.noRetList (osOodWeights yrLog tch prev ol lvs acc k).1 = true
  | _, _, [], _, _, _ => rfl
  | prev, ol, lv :: rest, acc, k, hood => by
    have h1 : lv.oodHere = 1 := hood lv (by simp)
    have hnr : ∀ k', Stmt.noRetList (osOodWeight yrLog tch (prev - yrLog) lv.foldsOff ol 0 k') = true := by
      intro k'
      unfold osOodWeight osOodFacs
      rw [os_zipIdx_map_range, List.map_map]
      show Stmt.noRetList (List.flatten _) = true
      rw [noRetList_flatten_range _ _ (fun _ => rfl)]
    simp only [osOodWeights, h1, List.range_one, List.foldl_cons, List.foldl_nil]
    rw [noRetList_append, osOodWeights_noRet yrLog tch _ _ rest _ _ (fun lv' h' => hood lv' (by simp [h']))]
    cases acc <;> simp [hnr, noRetList_append, Stmt.noRetList, Stmt.noRet]

/-! ## After the tail -/

/-- **After the tail** (G:1229-1317): the guest returns the final claim, the rotated point's
buffer, the glued claims' weight at the terminal point and the residual's value there. -/
theorem osFinish_sound {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    (hcal : OsCallees rd cfg) {st : OsSt} {tch : ℕ} {wL : WhirState} {residual tf : List E}
    (hfl : wL.folds.length = cfg.nFolds)
    (hfch : ∀ j < wL.folds.length, LoadHolds rd (σ (.n osFch)) j (wL.folds.getD j 0))
    (hgl : ∃ recs : List OsRec, recs.length = cfg.levels.length ∧ wL.glued = osGluedOf μ cfg recs ∧
      ∀ i < cfg.levels.length, OsRecOk rd σ cfg i (recs.getD i default))
    (hresl : residual.length = cfg.yrLen) (hres : ReadsAt rd (σ (.n osFmsg)) residual)
    (htfl : tf.length = cfg.yrLog) (htch : ReadsAt rd (σ (.n tch)) (tf ++ List.replicate (5 - cfg.yrLog) 0))
    {rets : List E} {C : CallRel}
    (hC7 : ∀ i < cfg.levels.length, ∀ a, a.length = 7 → C (cfg.lv i).resLoop a [] →
      coreProgram.Rel rd (cfg.lv i).resLoop a [])
    (hC2 : ∀ a r, a.length = 2 → C cfg.foldFinal a r → MeaningFoldFinalMsg cfg.yrLog rd a r)
    (h : Stmt.HoldsList C rd σ (osFinish cfg st tch) False (fun rs => rs = rets)) :
    ∃ pt, rets = [σ (.n st.t), pt,
        wL.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (wL.folds.drop c.foldStart ++ tf)) 0,
        multilinearEval residual tf] ∧
      ReadsAt rd pt (((wL.folds ++ tf).drop (cfg.lv 0).folds ++ (wL.folds ++ tf).take (cfg.lv 0).folds) ++
        List.replicate (42 - (cfg.nFolds + cfg.yrLog)) 0) := by
  obtain ⟨recs, hrecl, hglr, hrecs⟩ := hgl
  have hn := hok.len2
  have hhd : cfg.levels.headD default = cfg.lv 0 := by
    cases h' : cfg.levels with
    | nil => simp [h'] at hn
    | cons a b => simp [OsCfg.lv, h']
  unfold osFinish at h
  simp only [hhd] at h
  generalize hbs : osBases cfg.yrLog tch (st.k + 1 + 44) (st.k + 1 + 46) 0 cfg.levels (st.k + 1 + 47) = bs at h
  generalize hod : osOodWeights cfg.yrLog tch (cfg.lv 0).logCols 1 cfg.levels.tail none
    (bs.2 + 3 + 13 * cfg.levels.length) = od at h
  simp only [holdsList_append] at h
  obtain ⟨hF, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hP, h⟩ := holdsList_true_of (by
    simp only [osPoint, Stmt.noRetList, Stmt.noRet, Bool.true_and]
    rw [noRetList_flatten_range _ _ (fun i => by unfold osPtBlk; split <;> rfl)]) h
  obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hB, h⟩ := holdsList_true_of (by rw [← hbs]; exact osBases_noRet _ _ _ _ _ _ _) h
  obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hI0, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hR, h⟩ := holdsList_true_of (by
    unfold osResiduals; rw [zipIdx_map_range', noRetList_flatten_range _ _ (fun _ => rfl)]) h
  obtain ⟨hO, h⟩ := holdsList_true_of (by rw [← hod]; exact osOodWeights_noRet _ _ _ _ _ _ _ hok.ood) h
  obtain ⟨hC, h⟩ := holdsList_true_of (by rfl) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, and_true] at hF hI0 hC
  have hlast := hok.spec (cfg.levels.length - 1) (by rw [hok.len]; omega)
  rw [show cfg.levels.length - 1 + 1 = Lall.length by rw [hok.len]; omega, List.drop_length] at hlast
  have hyr : cfg.yrLen = 2 ^ cfg.yrLog := by
    rw [hlast.yrLen, hok.nFolds, ← hok.total, Nat.add_sub_cancel_left]
  -- the residual's value
  obtain ⟨mm, ps, hmml, hpsl, hmm, hps, hyat⟩ := hC2 _ _ rfl hF
  have hps' : ps = tf := os_readsAt_unique hps (os_readsAt_prefix htch) (by rw [hpsl, htfl])
  have hmm' : mm = residual := os_readsAt_unique hmm hres (by rw [hmml, hresl, hyr])
  simp only [List.cons.injEq, and_true] at hyat
  rw [hps', hmm'] at hyat
  -- the point
  have htch' : ∀ j < cfg.yrLog, LoadHolds rd (σ (.n tch)) j (tf.getD j 0) := fun j hj => by
    have := readsAt_getD htch j (by simp; omega)
    rwa [os_getD_append_lt (by omega)] at this
  have hpt := osPoint_sound hok.laneLe hok.pt42 hfl htfl (fun j hj => hfch j (by rw [hfl]; exact hj))
    htch' hP
  set n := cfg.levels.length with hnn
  set P := wL.folds
  -- the levels' facts
  have hspec : ∀ i < n, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1)) := fun i hi =>
    hok.spec i (by rw [hok.len]; exact hi)
  -- the basis rows
  rw [← hbs] at hB
  have hbasis : ∀ i < n, ∀ it ∈ osBasisCoords cfg.yrLog tch i (cfg.lv i),
      OsBasisOk rd σ (st.k + 1 + 44) (st.k + 1 + 46) it := fun i hi it hit =>
    osBases_sound 0 cfg.levels _ hB i hi it (by simpa using hit)
  -- the residual chains
  have hres' := osResiduals_sound (ich := bs.2 + 1) (ba := st.k + 1 + 44) (bb := st.k + 1 + 46)
    (k := bs.2 + 3) hcal.res (fun i hi => ⟨((hspec i hi).logCols).2.1, ((hspec i hi).logCols).2.2⟩) hC7 hR
  choose! rc hrcB hrc0 i0 bv rr hi0 hbv hrr hi1 using hres'
  have hich : ∀ i ≤ n, LoadHolds rd (σ (.n (bs.2 + 1))) i (∑ i' ∈ Finset.range i, bv i' * rr i') := by
    intro i hi
    induction i with
    | zero => rw [Finset.sum_range_zero, ← word_zero, ← hI0.1]; exact hI0.2
    | succ i ih =>
      have := hi1 i (by omega)
      rw [loadHolds_unique (hi0 i (by omega)) (ih (by omega))] at this
      rwa [Finset.sum_range_succ]
  -- the levels' terminal points
  set pt : ℕ → List E := fun i => P.drop (osLevelF cfg i) ++ tf
  have hIW : ∀ i < n, rr i = inducedWeight (μ - osLevelF cfg i) (recs.getD i default).queries
      (powers (recs.getD i default).lam (recs.getD i default).queries.length) (pt i) := by
    intro i hi
    obtain ⟨hpre, hrfo, hml, hFP, htab⟩ := hok.lvs i hi
    rw [← ((hspec i hi).logCols).1]
    exact os_rc_eq_inducedWeight htfl (by rw [hfl]; exact hFP) (by rw [hfl]; exact hpre) hrfo hml htab.ok
      hfch htch' (hbasis i hi) (hrecs i hi) (hrcB i hi) (hrc0 i hi) (hrr i hi)
  -- the out-of-domain weights
  set W : ℕ → E := fun j => match (recs.getD j default).ood with
    | some z => (recs.getD j default).lam * eqEval z (pt j)
    | none => 0
  have htail : ∀ i, cfg.levels.tail.getD i default = cfg.lv (i + 1) := by
    intro i; simp [OsCfg.lv, List.getD_eq_getElem?_getD]
  have hsome : ∀ i < n - 1, ∃ z, (recs.getD i default).ood = some z := by
    intro i hi
    have := (hrecs i (by omega)).2.2.2.1
    rw [hok.yrLevel] at this
    cases h' : (recs.getD i default).ood with
    | none => exact absurd (this.mp h') (by omega)
    | some z => exact ⟨z, rfl⟩
  rw [← hod] at hO
  have hOOD := osOodWeights_sound cfg.levels.tail 1 (cfg.lv 0).logCols none _ W hok.ood (fun i hi k' hk => by
    have hi' : i + 1 < n := by simp at hi; omega
    have hpc : osPrevColsAt cfg.levels.tail (cfg.lv 0).logCols i = (cfg.lv i).logCols := by
      cases i with
      | zero => rfl
      | succ i => simp only [osPrevColsAt, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, htail]
    have hfo : (cfg.levels.tail.getD i default).foldsOff = osLevelF cfg i := by
      rw [htail]
      have hs := hspec i (by omega)
      rw [List.drop_eq_getElem_cons (by rw [hok.len]; omega)] at hs
      exact hs.nextFolds
    rw [hpc, hfo] at hk
    rw [hpc]
    obtain ⟨hpre, hrfo, hml, hFP, -⟩ := hok.lvs i (by omega)
    obtain ⟨z, hz⟩ := hsome i (by omega)
    obtain ⟨-, -, -, -, -, hzs⟩ := hrecs i (by omega)
    obtain ⟨-, hzl, hzr, hsc⟩ := hzs z hz
    have hzl' : z.length = (cfg.lv i).logCols := hzl
    have hlv : (cfg.lv i).logCols = (cfg.levels[i]?.getD default).logCols := by
      simp [OsCfg.lv, List.getD_eq_getElem?_getD]
    have hzf : (cfg.lv i).logCols - cfg.yrLog + cfg.yrLog = (cfg.lv i).logCols := by omega
    have hptl : (pt i).length = (cfg.lv i).logCols := by simp [pt, P, hfl, htfl]; omega
    rw [osOodWeight_sound (by have := (hspec i (by omega)).logCols.2.1; omega) hk
      (sc := (recs.getD i default).lam) (z := fun t => z.getD t 0) (c := fun t => (pt i).getD t 0)
      (by convert hsc using 2; ring)
      (fun t ht => by
        have := readsAt_getD hzr t (by omega)
        rw [loadHolds_mul_gen_pow] at this
        convert this using 2; ring)
      (fun t ht => by
        unfold osOodSrc
        split
        · rw [os_getD_append_lt (by simp [P, hfl]; omega), os_getD_drop']
          exact hfch _ (by rw [hfl]; omega)
        · rw [os_getD_append_ge (by simp [P, hfl]; omega)]
          simp only [List.length_drop, P, hfl]
          rw [show t - (cfg.nFolds - osLevelF cfg i) = t - ((cfg.lv i).logCols - cfg.yrLog) by omega]
          exact htch' _ (by omega))]
    simp only [W, hz]
    rw [os_eqEval_eq z (pt i) (by rw [hzl, hptl]), hzl, hzf]) hO
  simp only [osAccVal, zero_add] at hOOD
  rw [hod] at hOOD
  -- the glued weight, level by level
  have hlvl : ∀ i < n, osRecInner μ (osLevelF cfg i) (recs.getD i default) (pt i) = bv i * rr i + W i := by
    intro i hi
    obtain ⟨-, -, -, hnone, hb1, hb2⟩ := hrecs i hi
    rw [hIW i hi]
    unfold osRecInner
    simp only [W]
    cases h' : (recs.getD i default).ood with
    | none =>
      rw [loadHolds_unique (hbv i hi) (hb1 h')]
      simp
    | some z =>
      rw [loadHolds_unique (hbv i hi) (hb2 z h').1]
      simp only [one_mul]
      ring
  have hW0 : W (n - 1) = 0 := by
    have := (hrecs (n - 1) (by omega)).2.2.2.1
    rw [hok.yrLevel] at this
    simp only [W, this.mpr rfl]
  have hinner : wL.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (wL.folds.drop c.foldStart ++ tf)) 0 =
      (∑ i ∈ Finset.range n, bv i * rr i) + ∑ i ∈ Finset.range (n - 1), W i := by
    rw [hglr, os_gluedOf_inner, hrecl, Finset.sum_congr rfl fun i hi => hlvl i (Finset.mem_range.mp hi),
      Finset.sum_add_distrib]
    congr 1
    rw [show n = n - 1 + 1 by omega, Finset.sum_range_succ, Nat.add_sub_cancel, hW0, add_zero]
  have hichN := loadHolds_unique hC.2.2 (hich n le_rfl)
  rw [show cfg.levels.tail.length = n - 1 by simp [n]] at hOOD
  -- the returns
  rcases hacc : od.2.1 with _ | a
  · rw [hacc] at h hOOD
    simp only at hOOD
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    obtain ⟨-, -, -, e3, hret⟩ := h
    refine ⟨σ (.n (st.k + 1)), ?_, hpt⟩
    rw [← hret, hC.1, hC.2.1, e3, hichN, hinner, ← hOOD, add_zero, hyat]
  · rw [hacc] at h hOOD
    simp only at hOOD
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    obtain ⟨-, -, -, e3, e4, hret⟩ := h
    refine ⟨σ (.n (st.k + 1)), ?_, hpt⟩
    rw [← hret, hC.1, hC.2.1, e4, e3, hichN, hinner, ← hOOD, hyat]

/-! ## The theorem -/

/-- **`open_stacked` at a configuration is sound** (G:1047-1317; TRIAGE #36): the relation of a
function whose body is `osBody cfg`, at a configuration whose facts match the ladder of
`(μ, r)`, gives `OpenOut` (`whirOpen μ r`, V:1763, up to its terminal). -/
theorem open_stacked_sound {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall)
    {name : String} {fn : Fn} (hfind : coreProgram.find? name = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) (hb : fn.body = osBody cfg)
    (hcal : OsCallees rd cfg) {root : Digest} {fs0 fs1 target root0 root1 cur : E} {rets : List E}
    (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.Rel rd name [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOut rd μ r root fs0 fs1 target cur rets := by
  rw [rel_iff_sem hfind, hb, hp] at h
  obtain ⟨σ, hpar, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := hpar
  have hn := hok.len2
  unfold osBody at h
  simp only [holdsList_append] at h
  -- the head
  obtain ⟨hH, h⟩ := holdsList_true_of (osHead_noRet _) h
  obtain ⟨cv, x0, x1, hcv, hinv0⟩ := osHead_sound (logN := μ) hok.off0 hroot ⟨e0, e1, e2, e3, e4, e5⟩ hH
  -- the levels
  obtain ⟨hL, h⟩ := holdsList_true_of (osLevels_noRet _ _ _ _) h
  have hcl : ∀ i < Lall.length, LvCallees rd cfg i := fun i hi => hcal.lv i (by rw [← hok.len]; exact hi)
  obtain ⟨ys, os, cvL, wL, rootsL, residual, hend, hresl, hres, hcont⟩ :=
    osLevels_sound (lane := (cfg.lv 0).folds) hok.len hok.spec hcl hcal.fin (cfg.levels.length - 1) 0 _ _
      _ _ _ (by rw [hok.len]; omega) hinv0 (by simpa using hL)
  rw [hok.len] at hend hcont
  simp only [List.drop_zero] at hend hcont
  generalize (osLevels cfg 0 cfg.levels (osHead cfg).2).2 = sL at *
  -- the tail
  obtain ⟨hT, h⟩ := holdsList_true_of (osTail_noRet _ _) h
  obtain ⟨ysT, tf, cvT, htfl, hreads, hrunT, htch⟩ := osTail_sound hok.yr2 hok.yr5 hend.cur hend.co hT
  generalize osTail cfg.yrLog sL = tl at *
  -- after the tail
  have hnf : wL.folds.length = cfg.nFolds := by rw [hend.nfolds, hok.nFolds]
  obtain ⟨pt, hrets, hpt⟩ := osFinish_sound hok hcal hnf hend.folds hend.glued hresl hres htfl htch (fun _ _ _ _ h => h)
    (fun a r _ h => hcal.ff a r h) h
  have hptl : ((wL.folds ++ tf).drop (cfg.lv 0).folds ++ (wL.folds ++ tf).take (cfg.lv 0).folds).length =
      cfg.nFolds + cfg.yrLog := by
    simp [hnf, htfl]; have := hok.laneLe; omega
  refine ⟨cv, [x0, x1] ++ ys ++ ysT, os,
    ⟨(wL.folds ++ tf).drop (cfg.lv 0).folds ++ (wL.folds ++ tf).take (cfg.lv 0).folds,
      wL.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (wL.folds.drop c.foldStart ++ tf)) 0,
      multilinearEval residual tf, σ (.n tl.2.1.t)⟩, cvT, rootsL, hcv, hreads, fun rest orest => ?_,
    pt, by rw [hrets], by rw [hptl]; exact hpt, by rw [hptl, hok.total]⟩
  have htail : Runs (osTailOpen (μ - osLevelF cfg (cfg.levels.length - 1)) (cfg.lv 0).folds wL residual)
      ⟨cvL, ysT ++ rest, orest, rootsL⟩
      ⟨(wL.folds ++ tf).drop (cfg.lv 0).folds ++ (wL.folds ++ tf).take (cfg.lv 0).folds,
        wL.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt (wL.folds.drop c.foldStart ++ tf)) 0,
        multilinearEval residual tf, σ (.n tl.2.1.t)⟩ ⟨cvT, rest, orest, rootsL⟩ := by
    rw [hok.nFolds, ← hok.total, Nat.add_sub_cancel_left]
    unfold osTailOpen
    rw [hend.quad]
    exact Runs.bind (RunsTo.runs (hrunT wL.target) _ _ _) (Runs.ret _ _)
  have hrun := hcont (ysT ++ rest) orest _ _ htail
  show Runs (whirOpen μ r target) _ _ _
  unfold whirOpen
  rw [show oqR 1 (2 ^ (cfg.lv 0).folds) = 2 ^ (cfg.lv 0).folds by simp [oqR]] at hrun
  rw [hok.config, hok.shape]
  refine Runs.bind (Runs.ret _ _) ?_
  rw [hok.lane]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine Runs.bind (os_runs_roundPoly3 cv target x0 x1 _ _ _) ?_
  exact hrun

end
end LeanVM.Guest.B1
