/-
  LeanVM.Guest.B1.Place.ArmKids

  `open_stacked`'s callees at the merged template placed, from the helpers' placed statements:
  per level `level_positions` and `level_queries`, after the levels `level_residual`, the named
  callees everywhere.
-/

module

public import LeanVM.Guest.B1.Place.ArmLay
public import LeanVM.Guest.B1.Place.ArmData
public import LeanVM.Guest.B1.Place.OsKidsO
public import LeanVM.Guest.B1.Place.Lq
public import LeanVM.Guest.B1.Place.Lr

/-!
# The callees, placed

* `LpAtO`, `LqAtO`, `LrAtO`: the helpers' placed statements (`LpAtD`, `LqAtD`, `LrAtD`) at an
  optional words bound; `lpAtO_of_D`, `lqAtO_of_D`, `lrAtO_of_D` at none.
* `winW … l p`: level `l`'s slice of `query_win_ptrs`, its `level_positions` at `p` (the window
  pointers into its decoders' runs, `winPtrsA`); `runsS … l p`: those runs.
* `arm_lv_ok`: on a body holding at the dispatch relation on every memory holding the callees'
  words `Lk` (`osLkA`, one such memory existing), with the helpers' dispatches at their honest
  values (`OsHelperVals`), level `l`'s frames satisfy `OsLvKOkO`: the calls before its positions
  named, `level_positions` by `LpAtO` on `Lk` and its window pointers, `level_queries` by `LqAtO`
  on those and the decoders' runs.
* `arm_rest_ok`: the frames after the levels: the closing rounds' and `fold_final_msg` named, the
  residuals' by `LrAtO` on `Lk`.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-! ## The helpers' statements at an optional bound -/

/-- `LpAtD` at an optional words bound. -/
def LpAtO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name loop : String) (S d cd : ℕ)
    (Bd : Option ℕ) : Prop :=
  ∀ (w0 : E) (cap : List E) (ep ew : ℕ) (tabs : E) (Lin : ℕ → Layout), cap.length = 5 →
    (∀ fp, ∀ k < S * (128 / d), RegionL (Lin fp) (ep + k) ∧ RegionL (Lin fp) (ew + k)) →
    (∀ fp, ∀ t < 128, ∃ i, tabs.limb 0 * addressOfIndex t = addressOfIndex i ∧
      RegionL (Lin fp) i) →
    (∀ fp rd, LowDef κ rd → MemL rd (Lin fp) →
      LpMem cert S d cd (lpDecPos fs name loop S d cd fp) w0 cap (ofK (addressOfIndex ep))
        (ofK (addressOfIndex ew)) tabs rd) →
    CompleteAtPO fs cert κ name Lin
      (w0 :: cap ++ [ofK (addressOfIndex ep), ofK (addressOfIndex ew), tabs])
      ((⟨cap, []⟩ : Fs).squeezeN (S - 1)).2.cap (lpRuns fs cert name loop S d cd w0 cap) Bd

theorem lpAtO_of_D {name loop : String} {S d cd : ℕ} (h : LpAtD fs cert κ name loop S d cd) :
    LpAtO fs cert κ name loop S d cd none := h

/-- `LqAtD` at an optional words bound. -/
def LqAtO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String)
    (q base folds leaf d cd mu nhs hbits fin : ℕ) (Bd : Option ℕ) : Prop :=
  let s := lqOqS q base folds leaf d cd mu nhs hbits fin
  ∀ (Lin : Layout) (lam lamInv : E) (ecoefs ehs epos eqp : ℕ) (rounds : List FoldRound)
    (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest)
    (capW flW : List E) (r0 r1 : E),
    rounds.length = s.folds → (s.final = 1 → hsv.length = s.nHs) →
    OqStatic s rounds hsv qs rows sibs q →
    LqCaps s q capW flW r0 r1 qs rows sibs →
    LqReg (RegionL Lin) s q ecoefs ehs epos eqp eb →
    (∀ rd, LowDef κ rd → MemL rd Lin → LqMem rd s q ecoefs ehs epos eqp rounds hsv eb qs) →
    CompleteAtO fs cert κ name Lin
      [lam, lamInv, ofK (addressOfIndex ecoefs), ofK (addressOfIndex ehs),
        ofK (addressOfIndex epos), ofK (addressOfIndex eqp)]
      (Returns [r0, r1, lqSum s (lqOdd q base folds leaf d cd mu nhs hbits fin) (lqIters q base)
        lamInv rounds qs rows, lam ^ q]) Bd

theorem lqAtO_of_D {name : String} {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (h : LqAtD fs cert κ name q base folds leaf d cd mu nhs hbits fin) :
    LqAtO fs cert κ name q base folds leaf d cd mu nhs hbits fin none :=
  fun Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 h1 h2 h3 h4 h5 h6 ↦
    (h Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 h1 h2 h3 h4 h5
      h6).toO

/-- `LrAtD` at an optional words bound. -/
def LrAtO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String)
    (q cols nhs hbits : ℕ) (Bd : Option ℕ) : Prop :=
  ∀ (Lin : Layout) (P BD HS M : E) (D p : ℕ → E) (hsv : List E), hsv.length = nhs →
    RegPtrs [(0, q), (1, cols), (2, nhs)] [P, BD, HS, M] (RegionL Lin) →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ i < q, LoadHolds rd P i (p i)) ∧ (∀ s < cols, LoadHolds rd BD s (D s)) ∧
        ∀ c < nhs, LoadHolds rd HS c (hsv.getD c 0)) →
    CompleteAtO fs cert κ name Lin [P, BD, HS, M]
      (Returns [(lrRet q cols nhs hbits D hsv p M).1, (lrRet q cols nhs hbits D hsv p M).2]) Bd

theorem lrAtO_of_D {name : String} {q cols nhs hbits : ℕ} (h : LrAtD fs cert κ name q cols nhs hbits) :
    LrAtO fs cert κ name q cols nhs hbits none :=
  fun Lin P BD HS M D p hsv h1 h2 h3 ↦ (h Lin P BD HS M D p hsv h1 h2 h3).toO

/-! ## Small facts -/

theorem regionL_append_left {L L' : Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  exact ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_append_right {L L' : Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  exact ⟨q, List.mem_append_right _ hq, h1, h2⟩

theorem mkCall_f' (σ : Val) (x : Option V × String × List V × List V) :
    (Main.mkCall σ x).f = x.2.1 := by
  obtain ⟨cv, f, a, r⟩ := x
  cases cv <;> rfl

theorem osSizesL_length {c : OsCfg} (h : c.yrLevel ≤ c.levels.length) :
    (osSizesL c).length = 19 + c.yrLevel := by
  simp [osSizesL, Nat.min_eq_left h]
  omega

theorem osSizesL_hi {c : OsCfg} (h : c.yrLevel ≤ c.levels.length) (j : ℕ) :
    (osSizesL c).getD (11 + c.yrLevel + j) 0 =
      [c.yrLen + (c.levels.getD c.yrLevel default).folds, yrLogCap, pointCap, pointCap,
        c.levels.length * ligColsCap, c.levels.length, c.levels.length, 2 * c.levels.length].getD j 0 := by
  unfold osSizesL
  dsimp only
  rw [List.getD_append_right _ _ _ _ (by simp [Nat.min_eq_left h]; omega)]
  congr 1
  simp [Nat.min_eq_left h]
  omega

theorem levels_getElem_eq {c : OsCfg} {l : ℕ} (hl : l < c.levels.length) :
    c.levels[l] = osLvA c l := (List.getD_eq_getElem _ _ hl).symm

/-- A level's statements are the body's. -/
theorem mem_osLevels (c : OsCfg) : ∀ (lvl : ℕ) (lvs : List OsLv) (s0 : OsSt) (i : ℕ)
    (hi : i < lvs.length) (s : Stmt),
    s ∈ (osLevel c (lvl + i) lvs[i] (osLevels c lvl (lvs.take i) s0).2).1 →
      s ∈ (osLevels c lvl lvs s0).1
  | _, [], _, _, hi, _, _ => absurd hi (by simp)
  | lvl, lv :: rest, s0, 0, _, s, h => by
    have e : (osLevels c lvl (lv :: rest) s0).1 = (osLevel c lvl lv s0).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv s0).2).1 := rfl
    rw [e]
    exact List.mem_append_left _ h
  | lvl, lv :: rest, s0, i + 1, hi, s, h => by
    have e : (osLevels c lvl (lv :: rest) s0).1 = (osLevel c lvl lv s0).1 ++
        (osLevels c (lvl + 1) rest (osLevel c lvl lv s0).2).1 := rfl
    rw [e]
    refine List.mem_append_right _ (mem_osLevels c (lvl + 1) rest _ i (by simpa using hi) s ?_)
    rw [show lvl + 1 + i = lvl + (i + 1) by omega]
    exact h

theorem lvPre_sub_body {c : OsCfg} {l : ℕ} (hl : l < c.levels.length) {s : Stmt}
    (h : s ∈ lvPre c l (osLvA c l) (osLvSt c l)) : s ∈ osBodyA c := by
  have h1 : s ∈ (osLevel c (0 + l) c.levels[l] (osLevels c 0 (c.levels.take l) (osHead c).2).2).1 := by
    rw [Nat.zero_add, levels_getElem_eq hl, osLevel_split]
    exact List.mem_append_left _ h
  have h2 := mem_osLevels c 0 c.levels (osHead c).2 l hl s h1
  unfold osBodyA
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h2))

/-- A named statement's frame names a callee of `osKindOf`. -/
theorem named_of_plain {c : OsCfg} (hB : (osBodyA c).all bodyOkS = true) {σ : Val}
    {pre : List Stmt} (hsub : ∀ s ∈ pre, s ∈ osBodyA c) {c' : Call}
    (hc : c' ∈ (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) :
    ∃ K, osKindOf c'.f = some K := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  have hok := bodyOkS_call (List.all_eq_true.mp hB s (hsub s hs)) hsx
  rw [mkCall_f']
  exact Option.isSome_iff_exists.mp hok

/-! ## The window pointers -/

/-- Level `l`'s window pointers, its `level_positions` at `p`. -/
def winPtrsA (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (l p : ℕ) : List E :=
  sqWinPtrs fs cert (lpLvP (osLvA c l).depth (osLvA c l).capDepth) (lpLoopA c l)
    (osLvA c l).squeezes (lpKidsAt fs (osPositionsName (osLvA c l)) (osLvA c l).squeezes p)

/-- Level `l`'s slice of `query_win_ptrs` (`g^(base + l·ligPosCap)`), its `level_positions` at
`p`. -/
def winW (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (b0 l p : ℕ) : Layout :=
  [(baseA c b0 osIxQbpA + l * ligPosCap, winPtrsA fs cert c l p)]

/-- Level `l`'s decoders' runs, its `level_positions` at `p`. -/
def runsS (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (D : ℕ → OsLvData) (l p : ℕ) :
    Layout :=
  lpRuns fs cert (osPositionsName (osLvA c l)) (lpLoopA c l) (osLvA c l).squeezes
    (osLvA c l).depth (osLvA c l).capDepth (D l).w0 (D l).capL p

theorem winPtrsA_length (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (l p : ℕ) :
    (winPtrsA fs cert c l p).length = (osLvA c l).squeezes * (128 / (osLvA c l).depth) := by
  simp only [winPtrsA, sqWinPtrs, List.length_map, List.length_range]
  rfl

theorem winW_eq (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (b0 l p : ℕ) :
    winW fs cert c b0 l p = [(baseA c b0 osIxQbpA + l * ligPosCap, winPtrsA fs cert c l p)] := rfl

theorem regionL_winW {c : OsCfg} {b0 l p k : ℕ}
    (hk : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth)) :
    RegionL (winW fs cert c b0 l p) (baseA c b0 osIxQbpA + l * ligPosCap + k) := by
  rw [winW_eq]
  exact ⟨_, List.mem_singleton_self _, by simp, by simp only [winPtrsA_length]; omega⟩

/-! ## A level -/

set_option maxHeartbeats 1600000 in
/-- **Level `l`'s frames are placed**, its `level_positions` at any `p`. -/
theorem arm_lv_ok {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) {Lin : Layout}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) {b0 : ℕ}
    {σ : Val}
    (hall : ∀ rd, LowDef κ rd → MemL rd (osLkA c b0 H.own Lin) →
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ (osLkA c b0 H.own Lin))) rd σ (osBodyA c))
    (hdo : ∀ s ∈ osBodyA c, DispOk σ s)
    (hfl : ∀ s ∈ osBodyA c, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1)
    (hB : (osBodyA c).all bodyOkS = true)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLkA c b0 H.own Lin))
    (hHV : OsHelperVals c b0 tabs H.own H.D σ)
    (hsel : ∀ l (f : OsLv → String), selName σ c l f = f (osLvA c l))
    (hyr : c.yrLevel < c.levels.length)
    (hnamed : ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hlp : ∀ e ∈ lpTable, e.1 ∈ osCalleeNames c →
      LpAtO fs cert κ e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2 (Bd.map (· e.1)))
    (hlq : ∀ e ∈ lqTable, e.1 ∈ osCalleeNames c →
      LqAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1
      e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.2.2 (Bd.map (· e.1)))
    {l : ℕ} (hl : l < c.levels.length) (hF : LvFacts c l)
    (hin : ∀ c' ∈ (lvK σ c l (osLvA c l) (osLvSt c l)).calls,
      c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) :
    OsLvKOkO fs cert κ σ (osLkA c b0 H.own Lin) (winW fs cert c b0 l) (runsS fs cert c H.D l) Bd
      (lvK σ c l (osLvA c l) (osLvSt c l)) := by
  set Lk := osLkA c b0 H.own Lin with hLk
  have hlen : H.own.length = (osSizesL c).length := H.own_len.length_eq
  have hSL := osSizesL_length (c := c) hyr.le
  obtain ⟨rd0, hl0, hm0⟩ := hex
  obtain ⟨hlpE, hlqE, -, hpo, hSper, hqS, hper, hS1, hpdcd, hcdE, hfinE, hfo, hnhs, -, -, hQ⟩ := hF
  have h3 : 3 < (osSizesL c).length := by omega
  have h9 : 9 < (osSizesL c).length := by omega
  have hlen3 : (osOwnA H.own 3).length = 2 * c.nFolds := by
    rw [osOwnA, forall₂_getD_len H.own_len h3]; rfl
  have hlen9 : (osOwnA H.own 9).length = c.levels.length * ligPosCap := by
    rw [osOwnA, forall₂_getD_len H.own_len h9]; rfl
  have hposIn : ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      (osLvA c l).posOff + k < c.levels.length * ligPosCap := fun k hk ↦ by
    have : (l + 1) * ligPosCap ≤ c.levels.length * ligPosCap := Nat.mul_le_mul_right _ hl
    rw [Nat.add_mul, one_mul] at this
    omega
  have hposR : ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      RegionL Lk (baseA c b0 9 + ((osLvA c l).posOff + k)) := fun k hk ↦
    regionL_lkA_buf hlen h9 (by decide) (by rw [← osOwnA, hlen9]; exact hposIn k hk)
  have hposL : ∀ rd, MemL rd Lk → ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      LoadHolds rd (ofK (addressOfIndex (baseA c b0 9 + (osLvA c l).posOff))) k
        ((osOwnA H.own 9).getD ((osLvA c l).posOff + k) 0) := fun rd hm k hk ↦ by
    rw [← osPtrA_mul]
    exact osMemA_load_mul (osMemA_of_lk hlen hm) h9 (by decide) (by rw [hlen9]; exact hposIn k hk)
  refine ⟨fun c' hc' ht ↦ ?_, rfl, ?_, fun p c' hc' ht ↦ ?_⟩
  · -- before the positions: named
    have hcb := hin c' (List.mem_append_left _ hc')
    obtain ⟨K, hK⟩ := named_of_plain hB (fun s hs ↦ lvPre_sub_body hl hs) hc'
    exact os_kid_namedO hall hdo hfl ⟨rd0, hl0, hm0⟩ hcb ht hK
      (hnamed c'.f (osKids_names hdo c' hcb) K hK · · Lk)
  · -- `level_positions`
    have hnm : osPositionsName (osLvA c l) ∈ osCalleeNames c := by
      have := osKids_names hdo _ (hin _ (List.mem_append_right _ (List.mem_cons_self ..)))
      rw [← hsel l osPositionsName]
      exact this
    have hE := hlp _ hlpE hnm
    simp only at hE
    obtain ⟨ha, hr, -⟩ := hHV l hl
    show CompleteAtPO fs cert κ (selName σ c l osPositionsName) (fun p ↦ Lk ++ winW fs cert c b0 l p)
      ((osLpCallOf c l).1.map σ) ((osLpCallOf c l).2.map σ) (runsS fs cert c H.D l)
      (Bd.map (· (selName σ c l osPositionsName)))
    rw [hsel, ha, hr, osPtrA_mul, osPtrA_mul, hpo]
    refine hE (H.D l).w0 (H.D l).capL (baseA c b0 9 + l * ligPosCap) (baseA c b0 osIxQbpA + l * ligPosCap)
      tabs (fun p ↦ Lk ++ winW fs cert c b0 l p) (H.capL_len l hl) (fun fp k hk ↦ ⟨?_, ?_⟩)
      (fun fp t ht ↦ ?_) (fun fp rd hlow hm ↦ ?_)
    · have := hposR k hk
      rw [hpo, ← Nat.add_assoc] at this
      exact regionL_append_left this
    · exact regionL_append_right (regionL_winW hk)
    · obtain ⟨i, hi, hR⟩ := os_addr_in_regionL
        (fun rd hl' hm ↦ ((hLin rd hl' hm).2 t (lt_of_lt_of_le ht (by norm_num [winTabBits]))).2)
        hl0 (memL_lin_of_lkA hm0)
      exact ⟨i, hi, regionL_append_left (regionL_lkA_lin hR)⟩
    · obtain ⟨hmk, hmw⟩ := Main.memL_append.mp hm
      refine ⟨(hLin rd hlow (memL_lin_of_lkA hmk)).2, fun j hj i hi ↦ ⟨?_, ?_⟩⟩
      · have hk : j * (128 / (osLvA c l).depth) + i < (osLvA c l).squeezes * (128 / (osLvA c l).depth) := by
          have : (j + 1) * (128 / (osLvA c l).depth) ≤ (osLvA c l).squeezes * (128 / (osLvA c l).depth) :=
            Nat.mul_le_mul_right _ hj
          rw [Nat.add_mul, one_mul] at this
          omega
        have := hposL rd hmk _ hk
        rw [hpo, ← Nat.add_assoc, ← hpo, H.posW l hl j hj i hi] at this
        rw [← hpo]
        exact this
      · obtain ⟨hk, he⟩ := sqWinPtrs_get (fs := fs) (cert := cert)
          (lv := lpLvP (osLvA c l).depth (osLvA c l).capDepth) (L := lpLoopA c l)
          (b := lpKidsAt fs (osPositionsName (osLvA c l)) (osLvA c l).squeezes fp) hj hi
        have := memL_run_load (ws := sqWinPtrs fs cert (lpLvP (osLvA c l).depth (osLvA c l).capDepth)
          (lpLoopA c l) (osLvA c l).squeezes (lpKidsAt fs (osPositionsName (osLvA c l))
            (osLvA c l).squeezes fp)) hmw hk
        rw [he] at this
        exact this
  · -- `level_queries`
    have hnm0 := osKids_names hdo _ (hin _ (List.mem_append_right _ (List.mem_cons_of_mem _ hc')))
    simp only [lvK, List.mem_singleton] at hc'
    have hnm : osQueriesName c l (osLvA c l) ∈ osCalleeNames c := by
      subst hc'
      rw [← hsel l (osQueriesName c l)]
      exact hnm0
    subst hc'
    have hE := hlq _ hlqE hnm
    simp only at hE
    obtain ⟨-, -, ha, hr, -⟩ := hHV l hl
    set ehs : ℕ := if l = c.yrLevel then baseA c b0 (osIxLaneA c) else baseA c b0 osIxHsA + l * hsStride
      with hehs
    have hhs : osHsPtrA c b0 l = ofK (addressOfIndex ehs) := by
      unfold osHsPtrA
      split
      · next h => simp only [hehs, h, ↓reduceIte]; rfl
      · next h => simp only [hehs, h, ↓reduceIte, osPtrA_mul]
    set lam' : E := if l = c.yrLevel then 0 else (H.D l).lam
    set lamInv' : E := if l = c.yrLevel then 0 else (H.D l).lamInv
    set eb : ℕ → ℕ := sqEb fs cert (lpLvP (osLvA c l).depth (osLvA c l).capDepth) (lpLoopA c l)
      (osLvA c l).squeezes (lpKidsAt fs (osPositionsName (osLvA c l)) (osLvA c l).squeezes p)
    have hbat : (H.D l).batched = lqSum (oqSA c l) (oqOddA c l)
        (lqIters (osLvA c l).queries (lvBase l)) lamInv' (H.rounds l) (H.qs l) (H.rows l) := by
      rw [H.batched_eq l hl]
      unfold lqSum
      by_cases hf : l = c.yrLevel
      · simp only [hfinE.mpr hf, ↓reduceIte]
      · have hf' : ¬ (oqSA c l).final = 1 := fun h ↦ hf (hfinE.mp h)
        simp only [hf', ↓reduceIte]
        have hN : oqNA c l = lqIters (osLvA c l).queries (lvBase l) := by
          unfold oqNA lqIters lvBase
          split_ifs <;> simp_all
        simp only [lamInv', hf, ↓reduceIte, hN]
    show CompleteAtO fs cert κ (selName σ c l (osQueriesName c l)) _ ((osLqCallOf c l).1.map σ)
      (Returns ((osLqCallOf c l).2.map σ)) (Bd.map (· (selName σ c l (osQueriesName c l))))
    rw [hsel, ha, hr, osPtrA_mul, osPtrA_mul, osPtrA_mul, hhs, hbat, hpo]
    have hst := H.static l hl
    rw [hQ] at hst
    obtain ⟨hcl, hfll, hvr, hcq⟩ := H.caps l hl
    rw [hQ] at hcq
    have h2fo : ∀ j < 2 * (oqSA c l).folds, 2 * (osLvA c l).foldsOff + j < (osOwnA H.own 3).length :=
      fun j hj ↦ by rw [hlen3]; omega
    refine hE (Lk ++ winW fs cert c b0 l p ++ runsS fs cert c H.D l p) lam' lamInv'
      (baseA c b0 3 + 2 * (osLvA c l).foldsOff) ehs (baseA c b0 9 + l * ligPosCap)
      (baseA c b0 osIxQbpA + l * ligPosCap) (H.rounds l) (H.hsv l) eb (H.qs l) (H.rows l)
      (H.sibs l) (H.capW l) (H.flW l) (osRootA H.own l).1 (osRootA H.own l).2 (H.rounds_len l hl)
      (H.hsv_len l hl) hst ⟨hcl, hfll, hvr, hcq⟩ ⟨fun j hj ↦ ?_, fun hf j hj ↦ ?_, fun k hk ↦ ⟨?_, ?_, fun i hi ↦ ?_⟩⟩
      (fun rd hlow hm ↦ ?_)
    · rw [Nat.add_assoc]
      exact regionL_append_left (regionL_append_left (regionL_lkA_buf hlen h3 (by decide) (h2fo j hj)))
    · have hfin : l = c.yrLevel := hfinE.mp hf
      have hix : osIxLaneA c < (osSizesL c).length := by unfold osIxLaneA; omega
      have hlane : (osOwnA H.own (osIxLaneA c)).length = c.yrLen + (osLvA c l).folds := by
        rw [osOwnA, forall₂_getD_len H.own_len hix, osIxLaneA, show 11 + c.yrLevel = 11 + c.yrLevel + 0 by rfl,
          osSizesL_hi hyr.le 0, hfin]
        rfl
      simp only [hehs, hfin, ↓reduceIte]
      refine regionL_append_left (regionL_append_left (regionL_lkA_buf hlen hix
        (by simp only [osIxLaneA, osIxQbpA]; omega) ?_))
      rw [← osOwnA, hlane]
      exact lt_of_lt_of_le hj (hnhs hfin)
    · have hk' : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth) := lt_of_lt_of_le hk hqS
      have := hposR k hk'
      rw [hpo, ← Nat.add_assoc] at this
      exact regionL_append_left (regionL_append_left this)
    · exact regionL_append_left (regionL_append_right (regionL_winW (lt_of_lt_of_le hk hqS)))
    · have hk' : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth) := lt_of_lt_of_le hk hqS
      change i < qwN ((oqSA c l).pd + (oqSA c l).cd) (oqSA c l).cd at hi
      rw [hpdcd, hcdE] at hi
      exact regionL_append_right (sqGroup_region (lv := lpLvP (osLvA c l).depth (osLvA c l).capDepth) hk' hi)
    · -- the words
      obtain ⟨hmkw, hms⟩ := Main.memL_append.mp hm
      obtain ⟨hmk, hmw⟩ := Main.memL_append.mp hmkw
      have hM := osMemA_of_lk hlen hmk
      obtain ⟨q1, q2⟩ := H.qMem b0 rd hM l hl
      rw [osPtrA_mul] at q1
      refine ⟨q1, fun hf ↦ by rw [← hhs]; exact q2 hf, fun k hk ↦ ⟨?_, ?_, fun i hi ↦ ?_⟩⟩
      · have hk' : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth) := lt_of_lt_of_le hk hqS
        have hper' : 0 < osPerA c l := hper
        have hj : k / osPerA c l < (osLvA c l).squeezes :=
          Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
        have hdm := Nat.div_add_mod k (osPerA c l)
        have := hposL rd hmk k hk'
        have hv := H.posW l hl (k / osPerA c l) hj (k % osPerA c l) (Nat.mod_lt _ hper')
        rw [Nat.add_assoc, Nat.mul_comm, hdm] at hv
        rw [hv, ← H.qs_eq l hl k (by rw [hQ]; exact hk), hpo] at this
        exact this
      · have hk' : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth) := lt_of_lt_of_le hk hqS
        have hkl : k < (sqWinPtrs fs cert (lpLvP (osLvA c l).depth (osLvA c l).capDepth) (lpLoopA c l)
            (osLvA c l).squeezes (lpKidsAt fs (osPositionsName (osLvA c l)) (osLvA c l).squeezes p)).length := by
          simp only [sqWinPtrs, List.length_map, List.length_range]; exact hk'
        have := memL_run_load hmw hkl
        simp only [winPtrsA, sqWinPtrs, List.getElem_map, List.getElem_range] at this
        have e : qwPtrAt cert (sqDecName (lpLvP (osLvA c l).depth (osLvA c l).capDepth))
            (sqDecPos fs (lpLvP (osLvA c l).depth (osLvA c l).capDepth) (lpLoopA c l)
              (osLvA c l).squeezes (lpKidsAt fs (osPositionsName (osLvA c l)) (osLvA c l).squeezes p)
              (k / sqPer (lpLvP (osLvA c l).depth (osLvA c l).capDepth)))
            (lpLvP (osLvA c l).depth (osLvA c l).capDepth).depth
            (lpLvP (osLvA c l).depth (osLvA c l).capDepth).capDepth
            (k % sqPer (lpLvP (osLvA c l).depth (osLvA c l).capDepth)) = ofK (addressOfIndex (eb k)) := by
          rw [qwPtrAt, ofK_addr_mul_gen_pow]; rfl
        rw [e] at this
        exact this
      · have hk' : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth) := lt_of_lt_of_le hk hqS
        change i < qwN ((oqSA c l).pd + (oqSA c l).cd) (oqSA c l).cd at hi
        change LoadHolds rd (ofK (addressOfIndex (eb k))) i
          (gen ^ qwVal ((oqSA c l).pd + (oqSA c l).cd) (oqSA c l).cd (H.qs l k) i)
        rw [hpdcd, hcdE] at hi ⊢
        have := sqGroup_wins (fs := fs) (cert := cert) (lv := lpLvP (osLvA c l).depth (osLvA c l).capDepth)
          (L := lpLoopA c l) hms hk' hi
        rw [H.qs_eq l hl k (by rw [hQ]; exact hk)]
        exact this

/-! ## After the levels -/

/-- The residual dispatches' frames, each at its level. -/
theorem mem_resFrames (σ : Val) (c : OsCfg) (ich bd ls la : ℕ) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (mats : List OsMat) (k : ℕ) (x : Option V × String × List V × List V),
      x ∈ resFrames σ c ich bd ls la lvl lvs mats k → ∃ j < lvs.length,
        x = (none, selName σ c (lvl + j) osResidualName,
          ((osResCallsL c ich bd ls la lvl lvs mats k).getD j ([], [])).1,
          ((osResCallsL c ich bd ls la lvl lvs mats k).getD j ([], [])).2)
  | _, [], _, _, x, h => by simp [resFrames, osResCallsL] at h
  | lvl, lv :: rest, mats, k, x, h => by
    unfold resFrames at h
    simp only [osResCallsL, List.zipIdx_cons, List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp, by simp [osResCallsL]⟩
    · obtain ⟨j, hj, rfl⟩ := mem_resFrames σ c ich bd ls la (lvl + 1) rest _ _ x h
      refine ⟨j + 1, by simp; omega, ?_⟩
      simp only [osResCallsL, List.getD_cons_succ, show lvl + 1 + j = lvl + (j + 1) by omega]

theorem osResCallsL_length (c : OsCfg) (ich bd ls la : ℕ) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (mats : List OsMat) (k : ℕ),
      (osResCallsL c ich bd ls la lvl lvs mats k).length = lvs.length
  | _, [], _, _ => rfl
  | lvl, _ :: rest, _, _ => by simp [osResCallsL, osResCallsL_length c ich bd ls la (lvl + 1) rest]

/-- **The finish's frames**: `fold_final_msg`, then non-final level `j`'s residual dispatch. -/
theorem mem_finFrames {σ : Val} {c : OsCfg} {x : Option V × String × List V × List V}
    (h : x ∈ finFrames σ c) :
    x = (none, "fold_final_msg__L" ++ natStr c.yrLog,
        [.n osFmsg, .n (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.2],
        [.n (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.1.k]) ∨
      ∃ j < (c.levels.take c.yrLevel).length, x = (none, selName σ c j osResidualName,
        ((osLrCalls c).getD j ([], [])).1, ((osLrCalls c).getD j ([], [])).2) := by
  unfold finFrames at h
  dsimp only at h
  rw [osFinishA_callSF, List.mem_cons] at h
  rcases h with rfl | h
  · exact Or.inl rfl
  · obtain ⟨j, hj, rfl⟩ := mem_resFrames σ c _ _ _ _ 0 _ _ _ x h
    refine Or.inr ⟨j, hj, ?_⟩
    rw [Nat.zero_add]
    rfl

theorem ffm_mem_body (c : OsCfg) :
    Stmt.call ("fold_final_msg__L" ++ natStr c.yrLog)
      [.n osFmsg, .n (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.2]
      [.n (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.1.k] ∈ osBodyA c := by
  unfold osBodyA osFinishA
  dsimp only
  exact List.mem_append_right _ (by simp)

theorem tl_sub_body {c : OsCfg} {s : Stmt} (h : s ∈ osTlA c) : s ∈ osBodyA c := by
  unfold osBodyA
  exact List.mem_append_left _ (List.mem_append_right _ h)

set_option maxHeartbeats 800000 in
/-- **The frames after the levels are placed.** -/
theorem arm_rest_ok {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) {Lin : Layout} {b0 : ℕ} {σ : Val}
    (hall : ∀ rd, LowDef κ rd → MemL rd (osLkA c b0 H.own Lin) →
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ (osLkA c b0 H.own Lin))) rd σ (osBodyA c))
    (hdo : ∀ s ∈ osBodyA c, DispOk σ s)
    (hfl : ∀ s ∈ osBodyA c, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1)
    (hB : (osBodyA c).all bodyOkS = true)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLkA c b0 H.own Lin))
    (hHV : OsHelperVals c b0 tabs H.own H.D σ)
    (hsel : ∀ l (f : OsLv → String), selName σ c l f = f (osLvA c l))
    (hyr : c.yrLevel < c.levels.length)
    (hLv : ∀ l < c.levels.length, LvFacts c l)
    (hnamed : ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hlr : ∀ e ∈ lrTable, e.1 ∈ osCalleeNames c →
      LrAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 (Bd.map (· e.1)))
    {c' : Call}
    (hc' : c' ∈ ((osTlA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
      (finFrames σ c).map (Main.mkCall σ))
    (hin : c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (ht : c'.taken = true) :
    CompleteAtO fs cert κ c'.f (osLkA c b0 H.own Lin) (c'.args.map σ) (Returns (c'.rets.map σ))
      (Bd.map (· c'.f)) := by
  set Lk := osLkA c b0 H.own Lin with hLk
  have hlen : H.own.length = (osSizesL c).length := H.own_len.length_eq
  have hSL := osSizesL_length (c := c) hyr.le
  have hnm : ∀ K, osKindOf c'.f = some K →
      CompleteAtO fs cert κ c'.f Lk (c'.args.map σ) (Returns (c'.rets.map σ)) (Bd.map (· c'.f)) :=
    fun K hK ↦ os_kid_namedO hall hdo hfl hex hin ht hK
      (hnamed c'.f (osKids_names hdo c' hin) K hK · · Lk)
  rcases List.mem_append.mp hc' with hc | hc
  · obtain ⟨K, hK⟩ := named_of_plain hB (fun s hs ↦ tl_sub_body hs) hc
    exact hnm K hK
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  rcases mem_finFrames hx with rfl | ⟨j, hj, rfl⟩
  · have hok := List.all_eq_true.mp hB _ (ffm_mem_body c)
    obtain ⟨K, hK⟩ := Option.isSome_iff_exists.mp hok
    exact hnm K hK
  -- a residual dispatch
  have hjy : j < c.yrLevel := by simpa [Nat.min_eq_left hyr.le] using hj
  have hjl : j < c.levels.length := by omega
  obtain ⟨-, -, -, -, hlrv⟩ := hHV j hjl
  obtain ⟨ha, hr⟩ := hlrv hjy
  obtain ⟨-, -, hlrE, hpo, hSper, hqS, -, -, -, -, -, -, -, hcols, hfolds, -⟩ := hLv j hjl
  have hnm : osResidualName (osLvA c j) ∈ osCalleeNames c := by
    have := osKids_names hdo _ hin
    rw [← hsel j osResidualName]
    exact this
  have hE := hlr _ (hlrE hjy) hnm
  simp only at hE
  show CompleteAtO fs cert κ (selName σ c j osResidualName) Lk
    (((osLrCalls c).getD j ([], [])).1.map σ) (Returns (((osLrCalls c).getD j ([], [])).2.map σ))
    (Bd.map (· (selName σ c j osResidualName)))
  rw [hsel, ha, hr]
  have h6 : 6 < (osSizesL c).length := by omega
  have h9 : 9 < (osSizesL c).length := by omega
  have hbd : osIxBdA c < (osSizesL c).length := by unfold osIxBdA; omega
  have hlen6 : (osOwnA H.own 6).length = c.levels.length * hsStride := by
    rw [osOwnA, forall₂_getD_len H.own_len h6]; rfl
  have hlen9 : (osOwnA H.own 9).length = c.levels.length * ligPosCap := by
    rw [osOwnA, forall₂_getD_len H.own_len h9]; rfl
  have hlenB : (osOwnA H.own (osIxBdA c)).length = c.levels.length * ligColsCap := by
    rw [osOwnA, forall₂_getD_len H.own_len hbd, osIxBdA,
      show 15 + c.yrLevel = 11 + c.yrLevel + 4 by omega, osSizesL_hi hyr.le 4]
    rfl
  have hstep : ∀ (w j' : ℕ), j' < c.levels.length → ∀ t < w, j' * w + t < c.levels.length * w :=
    fun w j' hj' t ht ↦ by
      have : (j' + 1) * w ≤ c.levels.length * w := Nat.mul_le_mul_right _ hj'
      rw [Nat.add_mul, one_mul] at this; omega
  have hq : (osLvA c j).queries ≤ ligPosCap := le_trans hqS hSper
  refine hE Lk (osPtrA c b0 9 * gen ^ (osLvA c j).posOff)
    (osPtrA c b0 (osIxBdA c) * gen ^ (j * ligColsCap)) (osPtrA c b0 osIxHsA * gen ^ (j * hsStride))
    (H.D j).mu (fun s ↦ (osOwnA H.own (osIxBdA c)).getD (j * ligColsCap + s) 0)
    (fun i ↦ (osOwnA H.own osIxQposA).getD ((osLvA c j).posOff + i) 0)
    ((List.range (osLvA c j).folds).map fun i ↦ (osOwnA H.own osIxHsA).getD (j * hsStride + i) 0)
    (by simp) (fun q hq' t ht ↦ ?_) (fun rd hlow hm ↦ ?_)
  · have hptr : ∀ e o t, (osPtrA c b0 e * gen ^ o).limb 0 * addressOfIndex t =
        addressOfIndex (baseA c b0 e + (o + t)) := fun e o t ↦ by
      rw [osPtrA_mul, limb_ofK_addr, Nat.add_assoc]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl
    · exact ⟨_, hptr 9 _ t, regionL_lkA_buf hlen h9 (by decide)
        (by rw [← osOwnA, hlen9, hpo]; exact hstep _ _ hjl _ (lt_of_lt_of_le ht hq))⟩
    · exact ⟨_, hptr (osIxBdA c) _ t, regionL_lkA_buf hlen hbd (by simp only [osIxBdA, osIxQbpA]; omega)
        (by rw [← osOwnA, hlenB]; exact hstep _ _ hjl _ (lt_of_lt_of_le ht hcols))⟩
    · exact ⟨_, hptr osIxHsA _ t, regionL_lkA_buf hlen h6 (by decide)
        (by rw [← osOwnA, hlen6]; exact hstep _ _ hjl _ (lt_of_lt_of_le ht hfolds))⟩
  · have hM := osMemA_of_lk hlen hm
    refine ⟨fun i hi ↦ ?_, fun s hs ↦ ?_, fun t ht ↦ ?_⟩
    · exact osMemA_load_mul hM h9 (by decide)
        (by rw [hlen9, hpo]; exact hstep _ _ hjl _ (lt_of_lt_of_le hi hq))
    · exact osMemA_load_mul hM hbd (by simp only [osIxBdA, osIxQbpA]; omega)
        (by rw [hlenB]; exact hstep _ _ hjl _ (lt_of_lt_of_le hs hcols))
    · have hv : ((List.range (osLvA c j).folds).map fun i ↦
          (osOwnA H.own osIxHsA).getD (j * hsStride + i) 0).getD t 0 =
          (osOwnA H.own osIxHsA).getD (j * hsStride + t) 0 := by
        rw [List.getD_eq_getElem _ _ (by simpa using ht)]
        simp
      rw [hv]
      exact osMemA_load_mul hM h6 (by decide)
        (by rw [hlen6]; exact hstep _ _ hjl _ (lt_of_lt_of_le (by simpa using ht) hfolds))

end
end LeanVM.Guest.B1.Arm
