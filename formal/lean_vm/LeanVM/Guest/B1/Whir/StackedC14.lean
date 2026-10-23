/-
  LeanVM.Guest.B1.Whir.StackedC14

  `open_stacked` after its tail rounds at its honest values.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC13
public import LeanVM.Guest.B1.Whir.StackedSound

/-!
# After the tail, honestly (TRIAGE #36)

`osFinish_complete`: the residual's value returned by `fold_final_msg`, the point, the basis
rows, the residual chains, the out-of-domain weights and the returns at their honest values
`osFinishVals`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The honest data after the tail: the residual's value, the buffers' pointers, the point's
entries, the basis rows' challenges, each level's chain, inner sum, scalar and chain end, the
out-of-domain weights' scalars, points and coordinates, the final claim, the last inner sum. -/
structure OsFinD where
  yat : E
  pt : E
  ent : ℕ → E
  ba : E
  bb : E
  cf : ℕ × (ℕ × ℕ) × ℕ → E
  ich : E
  chv : ℕ → E
  i0 : ℕ → E
  b : ℕ → E
  r : ℕ → E
  sc : ℕ → E
  z : ℕ → ℕ → E
  c : ℕ → ℕ → E
  t : E
  ichN : E

/-- The out-of-domain weights' sum (none without one). -/
def osFinAcc (cfg : OsCfg) (D : OsFinD) : Option E :=
  osOodWsAcc cfg.yrLog D.sc D.z D.c (cfg.levels.headD default).logCols 1 cfg.levels.tail none

/-- The total's value. -/
def osFinTot (cfg : OsCfg) (D : OsFinD) : E :=
  match osFinAcc cfg D with
  | none => D.ichN
  | some a => D.ichN + a

/-- The values of `osFinish` from its first. -/
def osFinishVals (cfg : OsCfg) (tch : ℕ) (D : OsFinD) : List E :=
  let n := cfg.levels.length
  [D.yat] ++ osPtVals D.pt D.ent ++ [osGw (n * 22), D.ba, osGw (n * 22), D.bb] ++
    osBasesVals cfg.yrLog tch D.cf 0 cfg.levels ++ [osGw (n + 1), D.ich, 0] ++
    osResidualsVals cfg.maxQ cfg.levels D.chv D.i0 D.b D.r ++
    osOodWsVals cfg.yrLog D.sc D.z D.c (cfg.levels.headD default).logCols 1 cfg.levels.tail none ++
    [D.t, D.pt, D.ichN] ++ (match osFinAcc cfg D with | none => [] | some a => [D.ichN + a]) ++ [D.yat]

/-- **After the tail** at its honest values (G:1229-1317). -/
theorem osFinish_complete {cfg : OsCfg} {st : OsSt} {tch : ℕ} {D : OsFinD} {P : OsPtrs} (hP : OsPtrsAt σ P)
    (hst : σ (.n st.t) = D.t)
    (hsrc : ∀ i < 42, ∀ b o, osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog tch i = some (b, o) →
      LoadHolds rd (σ (.n b)) o (D.ent i))
    (hz : ∀ i < 42, osPtSrc cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog tch i = none → D.ent i = 0)
    (hpt : ∀ i < 42, LoadHolds rd D.pt i (D.ent i))
    (hbas : ∀ i < cfg.levels.length, ∀ it ∈ osBasisCoords cfg.yrLog tch (0 + i) (cfg.levels.getD i default),
      OsBasisMem rd σ D.ba D.bb (D.cf it) it)
    (hich0 : LoadHolds rd D.ich 0 0) (hnq : ∀ lv ∈ cfg.levels, lv.queries < 2 ^ 128)
    (hres : ∀ lvl < cfg.levels.length, LoadHolds rd (D.chv lvl) 0 0 ∧ LoadHolds rd D.ich lvl (D.i0 lvl) ∧
      LoadHolds rd P.betas lvl (D.b lvl) ∧ LoadHolds rd (D.chv lvl) (cfg.levels.getD lvl default).queries (D.r lvl) ∧
      LoadHolds rd D.ich (lvl + 1) (D.i0 lvl + D.b lvl * D.r lvl))
    (hood1 : ∀ lv ∈ cfg.levels.tail, lv.oodHere = 1)
    (hood : ∀ i < cfg.levels.tail.length,
      0 < osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog + cfg.yrLog ∧
      LoadHolds rd P.ood ((1 + i) * 4) (D.sc (1 + i)) ∧
      (∀ t < osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog + cfg.yrLog,
        LoadHolds rd P.oodz ((1 + i) * 22 + t) (D.z (1 + i) t)) ∧
      ∀ t < osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog + cfg.yrLog,
        LoadHolds rd (σ (.n (osOodSrc tch (osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog)
          (cfg.levels.tail.getD i default).foldsOff t).1))
          (osOodSrc tch (osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols i - cfg.yrLog)
            (cfg.levels.tail.getD i default).foldsOff t).2 (D.c (1 + i) t))
    (hichN : LoadHolds rd D.ich cfg.levels.length D.ichN)
    (hcff : C cfg.foldFinal [σ (.n osFmsg), σ (.n tch)] [D.yat])
    (hcres : ∀ lvl < cfg.levels.length, 1 + osGw (cfg.levels.getD lvl default).queries ≠ 0 →
      C (cfg.levels.getD lvl default).resLoop [1, osGw (cfg.levels.getD lvl default).queries, σ (.n osQpos),
        D.ba, D.bb, D.chv lvl, σ (.n osQw)] [])
    (hv : ∀ j < (osFinishVals cfg tch D).length, σ (.n (st.k + j)) = (osFinishVals cfg tch D).getD j 0) :
    Stmt.HoldsList C rd σ (osFinish cfg st tch) False (fun rs => rs = [D.t, D.pt, osFinTot cfg D, D.yat]) := by
  set n := cfg.levels.length
  set PT := osPtVals D.pt D.ent
  set H4 : List E := [osGw (n * 22), D.ba, osGw (n * 22), D.bb]
  set B := osBasesVals cfg.yrLog tch D.cf 0 cfg.levels
  set I3 : List E := [osGw (n + 1), D.ich, 0]
  set R := osResidualsVals cfg.maxQ cfg.levels D.chv D.i0 D.b D.r
  set O := osOodWsVals cfg.yrLog D.sc D.z D.c (cfg.levels.headD default).logCols 1 cfg.levels.tail none
  set T3 : List E := [D.t, D.pt, D.ichN]
  set TT : List E := (match osFinAcc cfg D with | none => [] | some a => [D.ichN + a]) with hTT
  have hV : osFinishVals cfg tch D = [D.yat] ++ PT ++ H4 ++ B ++ I3 ++ R ++ O ++ T3 ++ TT ++ [D.yat] := rfl
  rw [hV] at hv
  obtain ⟨v9, gY⟩ := os_look_app hv
  obtain ⟨v8, gTT⟩ := os_look_app v9
  obtain ⟨v7, gT3⟩ := os_look_app v8
  obtain ⟨v6, gO⟩ := os_look_app v7
  obtain ⟨v5, gR⟩ := os_look_app v6
  obtain ⟨v4, gI⟩ := os_look_app v5
  obtain ⟨v3, gB⟩ := os_look_app v4
  obtain ⟨v2, gH⟩ := os_look_app v3
  obtain ⟨gy, gPT⟩ := os_look_app v2
  have lPT : PT.length = 43 := os_length_ptVals _ _
  have lR : R.length = 13 * n := os_length_residualsVals _ _ _ _ _ _
  simp only [List.length_append, List.length_cons, List.length_nil, lPT, lR, Nat.zero_add] at gPT gH gB gI gR gO gT3 gTT gY
  have hy : σ (.n st.k) = D.yat := by simpa using gy 0 (by simp)
  have hH : ∀ j < 4, σ (.n (st.k + (1 + 43) + j)) = H4.getD j 0 := fun j hj => gH j (by simp [H4]; omega)
  have h0 := hH 0 (by omega); have h1 := hH 1 (by omega); have h2 := hH 2 (by omega); have h3 := hH 3 (by omega)
  simp only [H4, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at h0 h1 h2 h3
  -- the bases
  have hba : σ (.n (st.k + 1 + 44)) = D.ba := by rw [← h1]
  have hbb : σ (.n (st.k + 1 + 46)) = D.bb := by rw [← h3]
  set Kr : List E → Prop := fun rs => rs = [D.t, D.pt, osFinTot cfg D, D.yat] with hKr
  obtain ⟨hBh, hBk⟩ := osBases_complete (C := C) (rd := rd) (kret := Kr) hba hbb 0 cfg.levels
    (st.k + 1 + 47) hbas (fun j hj => by rw [show st.k + 1 + 47 + j = st.k + (1 + 43 + 4) + j by ring]; exact gB j hj)
  set bs := osBases cfg.yrLog tch (st.k + 1 + 44) (st.k + 1 + 46) 0 cfg.levels (st.k + 1 + 47) with hbs
  have hbsk : bs.2 = st.k + (1 + 43 + 4 + B.length) := by rw [hBk]; ring
  have hI : ∀ j < 3, σ (.n (bs.2 + j)) = I3.getD j 0 := fun j hj => by rw [hbsk]; exact gI j (by simp [I3]; omega)
  have i0 := hI 0 (by omega); have i1 := hI 1 (by omega); have i2 := hI 2 (by omega)
  simp only [I3, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at i0 i1 i2
  -- the residual chains
  have hR := osResiduals_complete (C := C) (rd := rd) (σ := σ) (kret := Kr) (maxQ := cfg.maxQ) (ich := bs.2 + 1)
    (ba := st.k + 1 + 44) (bb := st.k + 1 + 46) (k := bs.2 + 3) hnq i1 hP.betas hres
    (fun lvl hl h => by rw [hba, hbb]; exact hcres lvl hl h) (fun j hj => by
      have e : bs.2 + 3 + j = st.k + (1 + 43 + 4 + B.length + 3) + j := by rw [hbsk]; ring
      rw [e]; exact gR j hj)
  -- the out-of-domain weights
  set rk := bs.2 + 3 + 13 * n
  obtain ⟨hOh, hOk, hO1, hO2⟩ := osOodWeights_complete (C := C) (rd := rd) (σ := σ) (kret := Kr) (yrLog := cfg.yrLog) (tch := tch)
    (sc := D.sc) (z := D.z) (c := D.c) hP.ood hP.oodz cfg.levels.tail 1 (cfg.levels.headD default).logCols none none
    rk hood1 ⟨fun _ => rfl, fun _ => rfl⟩ (fun _ _ h => absurd h (by simp)) hood
    (fun j hj => by
      show σ (.n (bs.2 + 3 + 13 * n + j)) = _
      rw [hbsk, show st.k + (1 + 43 + 4 + B.length) + 3 + 13 * n + j =
        st.k + (1 + 43 + 4 + B.length + 3 + 13 * n) + j by ring]
      exact gO j hj)
  set od := osOodWeights cfg.yrLog tch (cfg.levels.headD default).logCols 1 cfg.levels.tail none rk with hod
  have hk : od.2.2 = st.k + (1 + 43 + 4 + B.length + 3 + 13 * n + O.length) := by
    rw [hOk]; show bs.2 + 3 + 13 * n + O.length = _; rw [hbsk]; ring
  have hT : ∀ j < 3, σ (.n (od.2.2 + j)) = T3.getD j 0 := fun j hj => by rw [hk]; exact gT3 j (by simp [T3]; omega)
  have t0 := hT 0 (by omega); have t1 := hT 1 (by omega); have t2 := hT 2 (by omega)
  simp only [T3, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t0 t1 t2
  have hpt0 : σ (.n (st.k + 1)) = D.pt := by
    have := gPT 0 (by omega); simpa [PT, osPtVals] using this
  -- the whole
  unfold osFinish
  simp only [osHeap, List.singleton_append]
  rw [← hbs, ← hod]
  have hnrB : Stmt.noRetList bs.1 = true := osBases_noRet _ _ _ _ _ _ _
  have hnrR : Stmt.noRetList (osResiduals cfg.maxQ (bs.2 + 1) (st.k + 1 + 44) (st.k + 1 + 46) (bs.2 + 3)
      cfg.levels) = true := by
    unfold osResiduals; rw [os_zipIdx_map_rangeD, noRetList_flatten_range _ _ (fun _ => rfl)]
  have hnrO : Stmt.noRetList od.1 = true := osOodWeights_noRet _ _ _ _ _ _ _ hood1
  have hnrP : Stmt.noRetList (osPoint cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog tch (st.k + 1)) = true := by
    simp only [osPoint, Stmt.noRetList, Stmt.noRet, Bool.true_and]
    rw [noRetList_flatten_range _ _ (fun i => by unfold osPtBlk; split <;> rfl)]
  have hpre : Stmt.HoldsList C rd σ (Stmt.call cfg.foldFinal [V.n osFmsg, V.n tch] [V.n st.k] ::
      osPoint cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog tch (st.k + 1) ++
      [Stmt.atom (Atom.const (V.n (st.k + 1 + 43)) (osGw (cfg.levels.length * 22))),
        Stmt.atom (Atom.hint (Hint.allocDyn (V.n (st.k + 1 + 43 + 1)) (V.n (st.k + 1 + 43))))] ++
      [Stmt.atom (Atom.const (V.n (st.k + 1 + 45)) (osGw (cfg.levels.length * 22))),
        Stmt.atom (Atom.hint (Hint.allocDyn (V.n (st.k + 1 + 45 + 1)) (V.n (st.k + 1 + 45))))] ++ bs.1 ++
      [Stmt.atom (Atom.const (V.n bs.2) (osGw (cfg.levels.length + 1))),
        Stmt.atom (Atom.hint (Hint.allocDyn (V.n (bs.2 + 1)) (V.n bs.2)))] ++
      [Stmt.atom (Atom.const (V.n (bs.2 + 2)) (word 0 0 0)), Stmt.atom (Atom.load (V.n (bs.2 + 2)) (V.n (bs.2 + 1)) 0)] ++
      osResiduals cfg.maxQ (bs.2 + 1) (st.k + 1 + 44) (st.k + 1 + 46) (bs.2 + 3) cfg.levels ++ od.1 ++
      [Stmt.atom (Atom.copy (V.n od.2.2) (V.n st.t)), Stmt.atom (Atom.copy (V.n (od.2.2 + 1)) (V.n (st.k + 1))),
        Stmt.atom (Atom.load (V.n (od.2.2 + 2)) (V.n (bs.2 + 1)) cfg.levels.length)]) True Kr := by
    have hP' := osPoint_complete (C := C) (rd := rd) (σ := σ) (kret := Kr) (k := st.k + 1) (ptv := D.pt) (ent := D.ent) hsrc hz hpt
      (fun j hj => gPT j hj)
    simp only [List.cons_append]
    refine ⟨by simp only [List.map_cons, List.map_nil]; rw [hy]; exact hcff, ?_⟩
    simp only [holdsList_append]
    refine (holdsList_noRet _ hnrP _ _).mpr ⟨hP', (holdsList_noRet _ rfl _ _).mpr ⟨?_,
      (holdsList_noRet _ rfl _ _).mpr ⟨?_, (holdsList_noRet _ hnrB _ _).mpr ⟨hBh,
      (holdsList_noRet _ rfl _ _).mpr ⟨?_, (holdsList_noRet _ rfl _ _).mpr ⟨?_,
      (holdsList_noRet _ hnrR _ _).mpr ⟨hR, (holdsList_noRet _ hnrO _ _).mpr ⟨hOh, ?_⟩⟩⟩⟩⟩⟩⟩⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      rw [← h0]
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      rw [← h2]
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact i0
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨by rw [i2, word_zero], by rw [i2, i1]; exact hich0⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact ⟨by rw [t0, hst], by rw [t1, hpt0], by rw [t2, i1]; exact hichN⟩
  have hnrPre : Stmt.noRetList (Stmt.call cfg.foldFinal [V.n osFmsg, V.n tch] [V.n st.k] ::
      osPoint cfg.nFolds (cfg.levels.headD default).folds cfg.yrLog tch (st.k + 1) ++
      [Stmt.atom (Atom.const (V.n (st.k + 1 + 43)) (osGw (cfg.levels.length * 22))),
        Stmt.atom (Atom.hint (Hint.allocDyn (V.n (st.k + 1 + 43 + 1)) (V.n (st.k + 1 + 43))))] ++
      [Stmt.atom (Atom.const (V.n (st.k + 1 + 45)) (osGw (cfg.levels.length * 22))),
        Stmt.atom (Atom.hint (Hint.allocDyn (V.n (st.k + 1 + 45 + 1)) (V.n (st.k + 1 + 45))))] ++ bs.1 ++
      [Stmt.atom (Atom.const (V.n bs.2) (osGw (cfg.levels.length + 1))),
        Stmt.atom (Atom.hint (Hint.allocDyn (V.n (bs.2 + 1)) (V.n bs.2)))] ++
      [Stmt.atom (Atom.const (V.n (bs.2 + 2)) (word 0 0 0)), Stmt.atom (Atom.load (V.n (bs.2 + 2)) (V.n (bs.2 + 1)) 0)] ++
      osResiduals cfg.maxQ (bs.2 + 1) (st.k + 1 + 44) (st.k + 1 + 46) (bs.2 + 3) cfg.levels ++ od.1 ++
      [Stmt.atom (Atom.copy (V.n od.2.2) (V.n st.t)), Stmt.atom (Atom.copy (V.n (od.2.2 + 1)) (V.n (st.k + 1))),
        Stmt.atom (Atom.load (V.n (od.2.2 + 2)) (V.n (bs.2 + 1)) cfg.levels.length)]) = true := by
    simp only [List.cons_append, Stmt.noRetList, noRetList_append, hnrP, hnrB, hnrR, hnrO, Stmt.noRet, Bool.and_true,
]
  have lH4 : H4.length = 4 := rfl
  have lI3 : I3.length = 3 := rfl
  have lT3 : T3.length = 3 := rfl
  have hY : σ (.n (od.2.2 + 3 + TT.length)) = D.yat := by
    have := gY 0 (by simp)
    rw [hk]; convert this using 3; · omega
    · rfl
  rcases hacc : od.2.1 with _ | a
  · have hfa : osFinAcc cfg D = none := hO1.mp hacc
    have hTT0 : TT = [] := by rw [hTT, hfa]
    rw [hTT0] at hY
    simp only [List.length_nil, Nat.add_zero] at hY
    simp only [List.append_nil]
    rw [holdsList_append]
    refine (holdsList_noRet _ hnrPre _ _).mpr ⟨hpre, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨by rw [hY, hy], ?_⟩
    simp only [hKr, osFinTot, hfa]
    rw [t0, t1, t2, show od.2.2 + 2 + 1 = od.2.2 + 3 from rfl, hY]
  · obtain ⟨v, hfv⟩ : ∃ v, osFinAcc cfg D = some v := by
      cases h' : osFinAcc cfg D with
      | none => exact absurd (hO1.mpr h') (by simp [hacc])
      | some v => exact ⟨v, rfl⟩
    have hav : σ (.n a) = v := hO2 a v hacc hfv
    have hTT1 : TT = [D.ichN + v] := by rw [hTT, hfv]
    have hk3 : σ (.n (od.2.2 + 3)) = D.ichN + v := by
      have := gTT 0 (by rw [hTT1]; simp)
      rw [hTT1] at this
      convert this using 3; · have := hk; omega
      · rfl
    rw [hTT1] at hY
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at hY
    rw [holdsList_append, holdsList_append]
    refine (holdsList_noRet _ hnrPre _ _).mpr ⟨hpre, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨by rw [hk3, t2, hav], by rw [show od.2.2 + 3 + 1 = od.2.2 + 3 + 1 from rfl, hY, hy], ?_⟩
    simp only [hKr, osFinTot, hfv]
    rw [t0, t1, hk3, hY]

end
end LeanVM.Guest.B1
