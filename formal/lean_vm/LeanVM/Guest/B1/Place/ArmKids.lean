/-
  LeanVM.Guest.B1.Place.ArmKids

  `open_stacked`'s callees at the merged template placed, from the helpers' placed statements:
  per level `level_positions` and `level_queries`, after the levels `level_residual`, the named
  callees everywhere.
-/

module

public import LeanVM.Guest.B1.Place.ArmLay
public import LeanVM.Guest.B1.Place.ArmData
public import LeanVM.Guest.B1.Place.OsKidsOT
public import LeanVM.Guest.B1.Place.LqAtOP
public import LeanVM.Guest.B1.Place.Lq
public import LeanVM.Guest.B1.Place.Lr
public import LeanVM.Guest.B1.Place.ArmXT
public import LeanVM.Guest.B1.Place.LpAtE
public import LeanVM.Guest.B1.Place.ArmSlow
public import LeanVM.Guest.B1.Place.Ls

/-!
# The callees, placed

* `LpAtO`, `LqAtO`, `LrAtO`: the helpers' placed statements (`LpAtD`, `LqAtD`, `LrAtD`) at an
  optional words bound; `lpAtO_of_D`, `lqAtO_of_D`, `lrAtO_of_D` at none.
* `winW … l p`: level `l`'s slice of `query_win_ptrs`, its `level_positions` at `p` (the window
  pointers into its decoders' runs, `winPtrsA`); `runsS … l p`: those runs.
* `osLvPops H l`: level `l`'s `level_queries` entries at the honest witness; `arm_lq_ok`: its
  `level_queries` frame by `LqAtOP` on `Lk`, its window pointers and the decoders' runs, popping them.
* `arm_lp_ok`: level `l`'s `level_positions` frame by `LpAtOE` on `Lk` and its window pointers, popping nothing and
  exact at every node.
* `arm_lv_ok`: on a body holding at the dispatch relation on every memory holding the callees'
  words `Lk` (`osLkA`, one such memory existing), with the helpers' dispatches at their honest
  values (`OsHelperVals`), level `l`'s frames satisfy `OsLvKOkOT`: the calls before its positions
  named, `level_positions` by `arm_lp_ok`, `level_queries` by `arm_lq_ok`; within a bound, the trees satisfy
  `armXT` and `level_queries`' pop `osLvPops`.
* `arm_rest_ok`: the frames after the levels: the closing rounds' and `fold_final_msg` named, the
  residuals' by `LrAtO` on `Lk`; `arm_rest_okT`: within a bound by trees satisfying `armXT`.
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

theorem lpAtO_of_D {name loop : String} {S d cd : ℕ} (h : LpAtD fs cert κ name loop S d cd) :
    LpAtO fs cert κ name loop S d cd none := h

theorem lqAtO_of_D {name : String} {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (h : LqAtD fs cert κ name q base folds leaf d cd mu nhs hbits fin) :
    LqAtO fs cert κ name q base folds leaf d cd mu nhs hbits fin none :=
  fun Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 h1 h2 h3 h4 h5 h6 ↦
    (h Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 h1 h2 h3 h4 h5
      h6).toO

theorem lrAtO_of_D {name : String} {cols nhs hbits : ℕ} (h : LrAtD fs cert κ name cols nhs hbits) :
    LrAtO fs cert κ name cols nhs hbits none :=
  fun q hq1 hq2 Lin P BD HS M D p hsv h1 h2 h3 ↦
    (h q hq1 (lt_of_le_of_lt hq2 (by decide)) Lin P BD HS M D p hsv h1 h2 h3).toO

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

/-- A level's frames after its positions: `is_zero`'s, then its `level_queries`'. -/
theorem mem_lvK_B {σ : Val} {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} {c' : Call}
    (h : c' ∈ (lvK σ c lvl lv s).B) :
    c'.f = "is_zero" ∨ c' = Main.mkCall σ (none, selName σ c lvl (osQueriesName c lvl),
      (osQCallOf c lvl lv (osPreQ c lvl lv s)).1, (osQCallOf c lvl lv (osPreQ c lvl lv s)).2) := by
  simp only [lvK, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨x, hx, rfl⟩ | h
  · left
    rw [mkCall_f']
    exact lvIzF_f hx
  · exact Or.inr h

theorem osSizesL_length {c : OsCfg} (h : c.yrLevel ≤ c.levels.length) :
    (osSizesL c).length = 20 + c.yrLevel := by
  simp [osSizesL, Nat.min_eq_left h]
  omega

theorem osSizesL_hi {c : OsCfg} (h : c.yrLevel ≤ c.levels.length) (j : ℕ) :
    (osSizesL c).getD (12 + c.yrLevel + j) 0 =
      [c.yrLen + (c.levels.getD c.yrLevel default).folds, yrLogCap, pointCap, pointCap,
        c.levels.length * ligColsCap, c.levels.length, c.levels.length, 2 * c.levels.length].getD j 0 := by
  unfold osSizesL
  dsimp only
  rw [List.getD_append_right _ _ _ _ (by simp [Nat.min_eq_left h]; omega)]
  congr 1
  simp [Nat.min_eq_left h]
  omega

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
    (h : s ∈ lvPre c l (osLvA c l) (osLvSt c l)) : s ∈ osBodyPre c := by
  have h1 : s ∈ (osLevel c (0 + l) c.levels[l] (osLevels c 0 (c.levels.take l) (osHead c).2).2).1 := by
    rw [Nat.zero_add, levels_getElem_eq hl, osLevel_split]
    exact List.mem_append_left _ h
  have h2 := mem_osLevels c 0 c.levels (osHead c).2 l hl s h1
  unfold osBodyPre
  exact List.mem_append_left _ (List.mem_append_right _ h2)

/-- A named statement's frame names a callee of `osKindOf`. -/
theorem named_of_plain {c : OsCfg} (hB : (osBodyPre c).all bodyOkS = true) {σ : Val}
    {pre : List Stmt} (hsub : ∀ s ∈ pre, s ∈ osBodyPre c) {c' : Call}
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

/-- Level `l`'s slice of `query_win_ptrs`, at the level's offset, its `level_positions` at `p`. -/
def winW (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (b0 l p : ℕ) : Layout :=
  [(baseA c b0 osIxQbpA + (osLvA c l).posOff, winPtrsA fs cert c l p)]

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
    winW fs cert c b0 l p = [(baseA c b0 osIxQbpA + (osLvA c l).posOff, winPtrsA fs cert c l p)] := rfl

theorem regionL_winW {c : OsCfg} {b0 l p k : ℕ}
    (hk : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth)) :
    RegionL (winW fs cert c b0 l p) (baseA c b0 osIxQbpA + (osLvA c l).posOff + k) := by
  rw [winW_eq]
  exact ⟨_, List.mem_singleton_self _, by simp, by simp only [winPtrsA_length]; omega⟩

/-! ## A level -/

/-- Level `l`'s `level_queries` entries at the honest witness: its cap and flags, then its queries' rows and walks'
children. -/
def osLvPops {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (l : ℕ) : List Pop :=
  lqCapE (H.capW l) (H.flW l) ++ oqPops (oqSA c l) (oqW (H.qs l) (H.rows l) (H.sibs l)) (oqQA c l)

/-- **Level `l`'s `level_queries` frame is placed popping its honest entries**, its `level_positions` at
any `p`. -/
theorem arm_lq_ok {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) {Lin : Layout} {b0 : ℕ} {σ : Val}
    (hdo : ∀ s ∈ osBodyA c, DispOk σ s) (hHV : OsHelperVals c b0 tabs H.own H.D σ)
    (hsel : ∀ l (f : OsLv → String), selName σ c l f = f (osLvA c l))
    (hyr : c.yrLevel < c.levels.length)
    (hlq : ∀ e ∈ lqTable, e.1 ∈ osCalleeNames c →
      LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1
      e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.2.2 (Bd.map (· e.1)))
    {l : ℕ} (hl : l < c.levels.length) (hF : LvFacts c l)
    (hin : ∀ c' ∈ (lvK σ c l (osLvA c l) (osLvSt c l)).calls,
      c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (p : ℕ) :
    ∀ c' ∈ (lvK σ c l (osLvA c l) (osLvSt c l)).B, c'.f ≠ "is_zero" →
      CompleteAtOP fs cert κ c'.f (osLkA c b0 H.own Lin ++ winW fs cert c b0 l p ++ runsS fs cert c H.D l p)
        (c'.args.map σ) (Returns (c'.rets.map σ)) (Bd.map (· c'.f)) (fun _ ↦ osLvPops H l) := by
  intro c' hc' hiz
  set Lk := osLkA c b0 H.own Lin with hLk
  have hlen : H.own.length = (osSizesL c).length := H.own_len.length_eq
  have hSL := osSizesL_length (c := c) hyr.le
  obtain ⟨-, hlqE, -, hpo, hqS, hper, -, -, hpdcd, hfinE, hfo, hnhs, -, -, hQ⟩ := hF
  have h3 : 3 < (osSizesL c).length := by omega
  have h9 : osIxQposA < (osSizesL c).length := by simp only [osIxQposA]; omega
  have hlen3 : (osOwnA H.own 3).length = 2 * c.nFolds := by
    rw [osOwnA, forall₂_getD_len H.own_len h3]; rfl
  have hlen9 : (osOwnA H.own osIxQposA).length = osPosTotal c := by
    rw [osOwnA, forall₂_getD_len H.own_len h9]; rfl
  have hposIn : ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      (osLvA c l).posOff + k < osPosTotal c := fun k hk ↦ posOff_add_lt hl hpo hk
  have hposR : ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      RegionL Lk (baseA c b0 osIxQposA + ((osLvA c l).posOff + k)) := fun k hk ↦
    regionL_lkA_buf hlen h9 (by decide) (by rw [← osOwnA, hlen9]; exact hposIn k hk)
  have hposL : ∀ rd, MemL rd Lk → ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      LoadHolds rd (ofK (addressOfIndex (baseA c b0 osIxQposA + (osLvA c l).posOff))) k
        ((osOwnA H.own osIxQposA).getD ((osLvA c l).posOff + k) 0) := fun rd hm k hk ↦ by
    rw [← osPtrA_mul]
    exact osMemA_load_mul (osMemA_of_lk hlen hm) h9 (by decide) (by rw [hlen9]; exact hposIn k hk)
  have hnm0 := osKids_names hdo _ (hin _ (List.mem_append_right _ (List.mem_cons_of_mem _ hc')))
  replace hc' := (mem_lvK_B hc').resolve_left hiz
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
  show CompleteAtOP fs cert κ (selName σ c l (osQueriesName c l)) _ ((osLqCallOf c l).1.map σ)
    (Returns ((osLqCallOf c l).2.map σ)) (Bd.map (· (selName σ c l (osQueriesName c l)))) _
  have hP : osLvPops H l = lqCapE (H.capW l) (H.flW l) ++
      oqPops (oqSA c l) (oqW (H.qs l) (H.rows l) (H.sibs l)) (osLvA c l).queries := by
    rw [osLvPops, hQ]
  rw [hsel, ha, hr, osPtrA_mul, osPtrA_mul, osPtrA_mul, hhs, hbat, hP]
  have hst := H.static l hl
  rw [hQ] at hst
  obtain ⟨hcl, hfll, hvr, hcq⟩ := H.caps l hl
  rw [hQ] at hcq
  have h2fo : ∀ j < 2 * (oqSA c l).folds, 2 * (osLvA c l).foldsOff + j < (osOwnA H.own 3).length :=
    fun j hj ↦ by rw [hlen3]; omega
  refine hE (Lk ++ winW fs cert c b0 l p ++ runsS fs cert c H.D l p) lam' lamInv'
    (baseA c b0 3 + 2 * (osLvA c l).foldsOff) ehs (baseA c b0 osIxQposA + (osLvA c l).posOff)
    (baseA c b0 osIxQbpA + (osLvA c l).posOff) (H.rounds l) (H.hsv l) eb (H.qs l) (H.rows l)
    (H.sibs l) (H.capW l) (H.flW l) (osRootA H.own l).1 (osRootA H.own l).2 (H.rounds_len l hl)
    (H.hsv_len l hl) hst ⟨hcl, hfll, hvr, hcq⟩ ⟨fun j hj ↦ ?_, fun hf j hj ↦ ?_, fun k hk ↦ ⟨?_, ?_, fun i hi ↦ ?_⟩⟩
    (fun rd hlow hm ↦ ?_)
  · rw [Nat.add_assoc]
    exact regionL_append_left (regionL_append_left (regionL_lkA_buf hlen h3 (by decide) (h2fo j hj)))
  · have hfin : l = c.yrLevel := hfinE.mp hf
    have hix : osIxLaneA c < (osSizesL c).length := by unfold osIxLaneA; omega
    have hlane : (osOwnA H.own (osIxLaneA c)).length = c.yrLen + (osLvA c l).folds := by
      rw [osOwnA, forall₂_getD_len H.own_len hix, osIxLaneA, show 12 + c.yrLevel = 12 + c.yrLevel + 0 by rfl,
        osSizesL_hi hyr.le 0, hfin]
      rfl
    simp only [hehs, hfin, ↓reduceIte]
    refine regionL_append_left (regionL_append_left (regionL_lkA_buf hlen hix
      (by simp only [osIxLaneA, osIxQbpA]; omega) ?_))
    rw [← osOwnA, hlane]
    exact lt_of_lt_of_le hj (hnhs hfin)
  · have hk' : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth) := lt_of_lt_of_le hk hqS
    have := hposR k hk'
    rw [← Nat.add_assoc] at this
    exact regionL_append_left (regionL_append_left this)
  · exact regionL_append_left (regionL_append_right (regionL_winW (lt_of_lt_of_le hk hqS)))
  · have hk' : k < (osLvA c l).squeezes * (128 / (osLvA c l).depth) := lt_of_lt_of_le hk hqS
    change i < qwN ((oqSA c l).pd + (osLvA c l).capDepth) (osLvA c l).capDepth at hi
    rw [hpdcd] at hi
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
      rw [hv, ← H.qs_eq l hl k (by rw [hQ]; exact hk)] at this
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
      change i < qwN ((oqSA c l).pd + (osLvA c l).capDepth) (osLvA c l).capDepth at hi
      change LoadHolds rd (ofK (addressOfIndex (eb k))) i
        (gen ^ qwVal ((oqSA c l).pd + (osLvA c l).capDepth) (osLvA c l).capDepth (H.qs l k) i)
      rw [hpdcd] at hi ⊢
      have := sqGroup_wins (fs := fs) (cert := cert) (lv := lpLvP (osLvA c l).depth (osLvA c l).capDepth)
        (L := lpLoopA c l) hms hk' hi
      rw [H.qs_eq l hl k (by rw [hQ]; exact hk)]
      exact this

/-- **`CompleteAtPOE` within a bound is `OsCompleteAtPBT` by a tree popping nothing, exact at every node.** -/
theorem poe_toPBT {f : String} {Lin : ℕ → Layout} {args rets : List E} {Lout : ℕ → Layout} {B : ℕ}
    (h : CompleteAtPOE fs cert κ f Lin args rets Lout (some B)) :
    OsCompleteAtPBT fs cert κ f Lin args rets Lout
      (fun rd t ↦ t.pops coreProgram rd = [] ∧ t.Every (ExactAt coreProgram rd)) B := fun fp ↦
  let ⟨n, Lown, hW, hD, hn, hr⟩ := h fp
  ⟨n, Lown, hW, hD, hn B rfl, hr⟩

/-- **Level `l`'s `level_positions` frame is placed by a tree popping nothing, exact at every node**, at any `p`. -/
theorem arm_lp_ok {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) {Lin : Layout}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) {b0 : ℕ}
    {σ : Val} (hdo : ∀ s ∈ osBodyA c, DispOk σ s)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLkA c b0 H.own Lin))
    (hHV : OsHelperVals c b0 tabs H.own H.D σ)
    (hsel : ∀ l (f : OsLv → String), selName σ c l f = f (osLvA c l))
    (hyr : c.yrLevel < c.levels.length)
    (hlp : ∀ l < c.levels.length, osPositionsName (osLvA c l) ∈ osCalleeNames c → LpAtOE fs cert κ (osPositionsName (osLvA c l)) (lpLoopA c l)
      (osLvA c l).squeezes (osLvA c l).depth (osLvA c l).capDepth (Bd.map (· (osPositionsName (osLvA c l)))))
    {l : ℕ} (hl : l < c.levels.length) (hF : LvFacts c l)
    (hin : ∀ c' ∈ (lvK σ c l (osLvA c l) (osLvSt c l)).calls,
      c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) :
    CompleteAtPOE fs cert κ (lvK σ c l (osLvA c l) (osLvSt c l)).sq.f
      (fun p ↦ osLkA c b0 H.own Lin ++ winW fs cert c b0 l p)
      ((lvK σ c l (osLvA c l) (osLvSt c l)).sq.args.map σ) ((lvK σ c l (osLvA c l) (osLvSt c l)).sq.rets.map σ)
      (runsS fs cert c H.D l) (Bd.map (· (lvK σ c l (osLvA c l) (osLvSt c l)).sq.f)) := by
  set Lk := osLkA c b0 H.own Lin with hLk
  have hlen : H.own.length = (osSizesL c).length := H.own_len.length_eq
  have hSL := osSizesL_length (c := c) hyr.le
  obtain ⟨rd0, hl0, hm0⟩ := hex
  obtain ⟨-, -, -, hpo, -, -, -, -, -, -, -, -, -, -, -⟩ := hF
  have h9 : osIxQposA < (osSizesL c).length := by simp only [osIxQposA]; omega
  have hlen9 : (osOwnA H.own osIxQposA).length = osPosTotal c := by
    rw [osOwnA, forall₂_getD_len H.own_len h9]; rfl
  have hposIn : ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      (osLvA c l).posOff + k < osPosTotal c := fun k hk ↦ posOff_add_lt hl hpo hk
  have hposR : ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      RegionL Lk (baseA c b0 osIxQposA + ((osLvA c l).posOff + k)) := fun k hk ↦
    regionL_lkA_buf hlen h9 (by decide) (by rw [← osOwnA, hlen9]; exact hposIn k hk)
  have hposL : ∀ rd, MemL rd Lk → ∀ k < (osLvA c l).squeezes * (128 / (osLvA c l).depth),
      LoadHolds rd (ofK (addressOfIndex (baseA c b0 osIxQposA + (osLvA c l).posOff))) k
        ((osOwnA H.own osIxQposA).getD ((osLvA c l).posOff + k) 0) := fun rd hm k hk ↦ by
    rw [← osPtrA_mul]
    exact osMemA_load_mul (osMemA_of_lk hlen hm) h9 (by decide) (by rw [hlen9]; exact hposIn k hk)
  have hnm : osPositionsName (osLvA c l) ∈ osCalleeNames c := by
    have := osKids_names hdo _ (hin _ (List.mem_append_right _ (List.mem_cons_self ..)))
    rw [← hsel l osPositionsName]
    exact this
  have hE := hlp l hl hnm
  obtain ⟨ha, hr, -⟩ := hHV l hl
  show CompleteAtPOE fs cert κ (selName σ c l osPositionsName) (fun p ↦ Lk ++ winW fs cert c b0 l p)
    ((osLpCallOf c l).1.map σ) ((osLpCallOf c l).2.map σ) (runsS fs cert c H.D l)
    (Bd.map (· (selName σ c l osPositionsName)))
  rw [hsel, ha, hr, osPtrA_mul, osPtrA_mul]
  refine hE (H.D l).w0 (H.D l).capL (baseA c b0 osIxQposA + (osLvA c l).posOff)
    (baseA c b0 osIxQbpA + (osLvA c l).posOff)
    tabs (fun p ↦ Lk ++ winW fs cert c b0 l p) (H.capL_len l hl) (fun fp k hk ↦ ⟨?_, ?_⟩)
    (fun fp t ht ↦ ?_) (fun fp rd hlow hm ↦ ?_)
  · have := hposR k hk
    rw [← Nat.add_assoc] at this
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
      rw [← Nat.add_assoc, H.posW l hl j hj i hi] at this
      exact this
    · obtain ⟨hk, he⟩ := sqWinPtrs_get (fs := fs) (cert := cert)
        (lv := lpLvP (osLvA c l).depth (osLvA c l).capDepth) (L := lpLoopA c l)
        (b := lpKidsAt fs (osPositionsName (osLvA c l)) (osLvA c l).squeezes fp) hj hi
      have := memL_run_load (ws := sqWinPtrs fs cert (lpLvP (osLvA c l).depth (osLvA c l).capDepth)
        (lpLoopA c l) (osLvA c l).squeezes (lpKidsAt fs (osPositionsName (osLvA c l))
          (osLvA c l).squeezes fp)) hmw hk
      rw [he] at this
      exact this

/-- **Level `l`'s frames are placed**, its `level_positions` at any `p`, within a bound by trees satisfying `armXT`,
its `level_queries` popping `osLvPops`. -/
theorem arm_lv_ok {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) {Lin : Layout}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) {b0 : ℕ}
    {σ : Val}
    (hall : ∀ rd, LowDef κ rd → MemL rd (osLkA c b0 H.own Lin) → ∃ σ',
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ (osLkA c b0 H.own Lin))) rd σ' (osBodyA c) ∧
        CallAg (osBodyA c) σ' σ)
    (hdo : ∀ s ∈ osBodyA c, DispOk σ s)
    (hfl : ∀ s ∈ osBodyA c, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1)
    (hB : (osBodyPre c).all bodyOkS = true)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLkA c b0 H.own Lin))
    (hHV : OsHelperVals c b0 tabs H.own H.D σ)
    (hsel : ∀ l (f : OsLv → String), selName σ c l f = f (osLvA c l))
    (hyr : c.yrLevel < c.levels.length)
    (hnamed : ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hnamedT : ∀ Bk ∈ Bd, ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtDTBR fs cert κ f L' args (Returns rets) armXT (Bk f))
    (hlp : ∀ l < c.levels.length, osPositionsName (osLvA c l) ∈ osCalleeNames c → LpAtOE fs cert κ (osPositionsName (osLvA c l)) (lpLoopA c l)
      (osLvA c l).squeezes (osLvA c l).depth (osLvA c l).capDepth (Bd.map (· (osPositionsName (osLvA c l)))))
    (hlq : ∀ e ∈ lqTable, e.1 ∈ osCalleeNames c →
      LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1
      e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.2.2 (Bd.map (· e.1)))
    {l : ℕ} (hl : l < c.levels.length) (hF : LvFacts c l)
    (hin : ∀ c' ∈ (lvK σ c l (osLvA c l) (osLvSt c l)).calls,
      c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) :
    OsLvKOkOT fs cert κ σ (osLkA c b0 H.own Lin) (winW fs cert c b0 l) (runsS fs cert c H.D l) Bd armXT armXT
      (fun rd t ↦ (t.name ≠ "is_zero" → t.pops coreProgram rd = osLvPops H l) ∧ armXT rd t)
      (lvK σ c l (osLvA c l) (osLvSt c l)) := by
  have hq := arm_lq_ok (Lin := Lin) (b0 := b0) H hdo hHV hsel hyr hlq hl hF hin
  have hsq := arm_lp_ok (Bd := Bd) H hLin hdo hex hHV hsel hyr hlp hl hF hin
  have hqx : ∀ c' ∈ (lvK σ c l (osLvA c l) (osLvSt c l)).B, c'.f ≠ "is_zero" → armExactS c'.f = false := by
    intro c' hc' hiz
    replace hc' := (mem_lvK_B hc').resolve_left hiz
    subst hc'
    show armExactS (selName σ c l (osQueriesName c l)) = false
    rw [hsel]
    have h := armExactS_lq hF.2.1
    exact h
  have hBin : ∀ c' ∈ (lvK σ c l (osLvA c l) (osLvSt c l)).B,
      c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ) :=
    fun c' hc' ↦ hin c' (List.mem_append_right _ (List.mem_cons_of_mem _ hc'))
  refine ⟨⟨fun c' hc' ht ↦ ?_, rfl, hsq.toPO, fun p c' hc' ht ↦ ?_⟩,
    fun Bk hBk c' hc' ht ↦ ?_, fun Bk hBk ↦ ?_, fun Bk hBk p c' hc' ht ↦ ?_⟩
  · -- before the positions: named
    have hcb := hin c' (List.mem_append_left _ hc')
    obtain ⟨K, hK⟩ := named_of_plain hB (fun s hs ↦ lvPre_sub_body hl hs) hc'
    exact os_kid_namedO hall hdo hfl hex hcb ht hK (hnamed c'.f (osKids_names hdo c' hcb) K hK · · _)
  · by_cases hiz : c'.f = "is_zero"
    · have hK : osKindOf c'.f = some .iz := by rw [hiz]; exact osKindOf_isZero
      have hcb := hBin c' hc'
      exact os_kid_namedX (X := fun a r ↦ CompleteAtO fs cert κ c'.f
          (osLkA c b0 H.own Lin ++ winW fs cert c b0 l p ++ runsS fs cert c H.D l p) a (Returns r)
          (Bd.map (· c'.f))) hall hdo hfl hex hcb ht hK fun a r _ hpre ↦
        hnamed c'.f (osKids_names hdo c' hcb) .iz hK a r _ (fun _ hp ↦ by simp [OsKind.spec] at hp)
          fun rd hl hm ↦ hpre rd hl (Main.memL_append.mp (Main.memL_append.mp hm).1).1
    · exact (hq p c' hc' hiz).toO
  · have hcb := hin c' (List.mem_append_left _ hc')
    obtain ⟨K, hK⟩ := named_of_plain hB (fun s hs ↦ lvPre_sub_body hl hs) hc'
    exact os_kid_namedX hall hdo hfl hex hcb ht hK (hnamedT Bk hBk c'.f (osKids_names hdo c' hcb) K hK · · _)
  · obtain rfl : Bd = some Bk := hBk
    exact (poe_toPBT hsq).mono le_rfl fun _ _ h _ ↦ h.2
  · obtain rfl : Bd = some Bk := hBk
    by_cases hiz : c'.f = "is_zero"
    · have hK : osKindOf c'.f = some .iz := by rw [hiz]; exact osKindOf_isZero
      have hcb := hBin c' hc'
      have h := os_kid_namedX (X := fun a r ↦ CompleteAtDTBR fs cert κ c'.f
          (osLkA c b0 H.own Lin ++ winW fs cert c b0 l p ++ runsS fs cert c H.D l p) a (Returns r) armXT
          (Bk c'.f)) hall hdo hfl hex hcb ht hK fun a r _ hpre ↦
        hnamedT Bk rfl c'.f (osKids_names hdo c' hcb) .iz hK a r _ (fun _ hp ↦ by simp [OsKind.spec] at hp)
          fun rd hl hm ↦ hpre rd hl (Main.memL_append.mp (Main.memL_append.mp hm).1).1
      exact h.monoN le_rfl fun _ t hn h ↦ ⟨fun hne ↦ absurd (hn.trans hiz) hne, h⟩
    · exact (hq p c' hc' hiz).toDTBR.monoN le_rfl fun _ t hn h ↦
        ⟨fun _ ↦ h, armXT_of_not (by rw [hn]; exact hqx c' hc' hiz)⟩

/-! ## After the levels -/

/-- The residual frames, each at its level: `is_zero`'s, the dispatches into `level_residual` and
into `level_residual_slow`. -/
theorem mem_resFrames (σ : Val) (c : OsCfg) (rts : List (List ℕ)) (tch ich bd ls la : ℕ) :
    ∀ (lvl : ℕ) (lvs : List OsLv) (mats : List OsMat) (k : ℕ) (x : Option V × String × List V × List V),
      x ∈ resFrames σ c rts tch ich bd ls la lvl lvs mats k → x.2.1 = "is_zero" ∨ ∃ j < lvs.length,
        x = (none, osResidualName (lvs.getD j default),
          ((osResCallsL c rts tch ich bd ls la lvl lvs mats k).getD j ([], [])).1,
          ((osResCallsL c rts tch ich bd ls la lvl lvs mats k).getD j ([], [])).2) ∨
        x = (none, selName σ c (lvl + j) (osSlowName c),
          ((osSlowCallsL c rts tch ich bd ls la lvl lvs mats k).getD j ([], [])).1,
          ((osSlowCallsL c rts tch ich bd ls la lvl lvs mats k).getD j ([], [])).2)
  | _, [], _, _, x, h => by simp [resFrames] at h
  | lvl, lv :: rest, mats, k, x, h => by
    rw [resFrames, List.mem_append] at h
    rcases h with h | h
    · unfold resFrames1 at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact Or.inr ⟨0, by simp, Or.inl (by simp [osResCallsL])⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨0, by simp, Or.inr (by simp [osSlowCallsL])⟩
    · rcases mem_resFrames σ c rts tch ich bd ls la (lvl + 1) rest _ _ x h with h | ⟨j, hj, h⟩
      · exact Or.inl h
      refine Or.inr ⟨j + 1, by simp; omega, ?_⟩
      simp only [osResCallsL, osSlowCallsL, List.getD_cons_succ,
        show lvl + 1 + j = lvl + (j + 1) by omega] at h ⊢
      exact h

/-- **The finish's frames**: `fold_final_msg`, `is_zero`'s, then non-final level `j`'s dispatches into
`level_residual` and `level_residual_slow`. -/
theorem mem_finFrames {σ : Val} {c : OsCfg} {x : Option V × String × List V × List V}
    (h : x ∈ finFrames σ c) :
    x = (none, "fold_final_msg__L" ++ natStr c.yrLog,
        [.n osFmsg, .n (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.2],
        [.n (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.1.k]) ∨ x.2.1 = "is_zero" ∨
      ∃ j < (c.levels.take c.yrLevel).length, x = (none, osResidualName (osLvA c j),
        ((osLrCalls c).getD j ([], [])).1, ((osLrCalls c).getD j ([], [])).2) ∨
        x = (none, selName σ c j (osSlowName c), ((osSlowCalls c).getD j ([], [])).1,
          ((osSlowCalls c).getD j ([], [])).2) := by
  unfold finFrames at h
  dsimp only at h
  rw [osFinishA_callSF, List.mem_cons] at h
  rcases h with rfl | h
  · exact Or.inl rfl
  dsimp only at h
  rw [List.mem_append] at h
  rcases h with h | h
  · exact Or.inr (Or.inl (osBases_callSF σ c _ _ _ _ 0 _ _ x h))
  · rcases mem_resFrames σ c _ _ _ _ _ _ 0 _ _ _ x h with h | ⟨j, hj, h⟩
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ⟨j, hj, ?_⟩)
      have hj' : j < c.yrLevel := by simp at hj; omega
      simp only [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_take, hj', ↓reduceIte] at h
      exact h

theorem tl_sub_body {c : OsCfg} {s : Stmt} (h : s ∈ osTlA c) : s ∈ osBodyPre c := by
  unfold osBodyPre
  exact List.mem_append_right _ h

set_option maxHeartbeats 800000 in
/-- **The frames after the levels are placed.** -/
theorem arm_rest_ok {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) {Lin : Layout} {b0 : ℕ} {σ : Val}
    (hall : ∀ rd, LowDef κ rd → MemL rd (osLkA c b0 H.own Lin) → ∃ σ',
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ (osLkA c b0 H.own Lin))) rd σ' (osBodyA c) ∧
        CallAg (osBodyA c) σ' σ)
    (hdo : ∀ s ∈ osBodyA c, DispOk σ s)
    (hfl : ∀ s ∈ osBodyA c, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1)
    (hB : (osBodyPre c).all bodyOkS = true)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLkA c b0 H.own Lin))
    (hHV : OsHelperVals c b0 tabs H.own H.D σ)
    (hsel : ∀ l (f : OsLv → String), selName σ c l f = f (osLvA c l))
    (hyr : c.yrLevel < c.levels.length)
    (hLv : ∀ l < c.levels.length, LvFacts c l)
    (hnamed : ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hlr : ∀ j < c.yrLevel, osResidualName (osLvA c j) ∈ osCalleeNames c → LrAtOq fs cert κ (osResidualName (osLvA c j)) (osLvA c j).logCols (osLvA c j).folds
      (osLvA c j).highBits (osLvA c j).queries (Bd.map (· (osResidualName (osLvA c j)))))
    (hffm : (osKindOf ("fold_final_msg__L" ++ natStr c.yrLog)).isSome = true) (hsf : SlowFacts c)
    (hls : ∀ j < c.yrLevel, osSlowName c (osLvA c j) ∈ osCalleeNames c →
      LsAtO fs cert κ (osSlowName c (osLvA c j)) (osLvA c j).queries (osLvA c j).prefixLen c.yrLog
        (osLvA c j).vanish (Bd.map (· (osSlowName c (osLvA c j)))))
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
  rcases mem_finFrames hx with rfl | hiz | ⟨j, hj, rfl | rfl⟩
  · obtain ⟨K, hK⟩ := Option.isSome_iff_exists.mp hffm
    exact hnm K hK
  · exact hnm .iz (by rw [mkCall_f', hiz]; exact osKindOf_isZero)
  rotate_left
  · -- a slow dispatch
    have hjy : j < c.yrLevel := by simpa [Nat.min_eq_left hyr.le] using hj
    have hjl : j < c.levels.length := by omega
    obtain ⟨-, -, -, -, hlrv⟩ := hHV j hjl
    obtain ⟨-, -, hsa, hsr⟩ := hlrv hjy
    obtain ⟨-, -, -, hpo, hqS, hper, -⟩ := hLv j hjl
    obtain ⟨hyl, hsl⟩ := hsf
    obtain ⟨hfo, -, -⟩ := hsl j hjy
    show CompleteAtO fs cert κ (selName σ c j (osSlowName c)) Lk
      (((osSlowCalls c).getD j ([], [])).1.map σ) (Returns (((osSlowCalls c).getD j ([], [])).2.map σ))
      (Bd.map (· (selName σ c j (osSlowName c))))
    have hnm : osSlowName c (osLvA c j) ∈ osCalleeNames c := by
      have := osKids_names hdo _ hin
      rw [← hsel j (osSlowName c)]
      exact this
    rw [hsel, hsa, hsr]
    have h2 : 2 < (osSizesL c).length := by omega
    have h9 : osIxQposA < (osSizesL c).length := by simp only [osIxQposA]; omega
    have htc : osIxTchA c < (osSizesL c).length := by unfold osIxTchA; omega
    have hlen2 : (osOwnA H.own 2).length = c.nFolds := by
      rw [osOwnA, forall₂_getD_len H.own_len h2]; rfl
    have hlen9 : (osOwnA H.own osIxQposA).length = osPosTotal c := by
      rw [osOwnA, forall₂_getD_len H.own_len h9]; rfl
    have hlenT : (osOwnA H.own (osIxTchA c)).length = yrLogCap := by
      rw [osOwnA, forall₂_getD_len H.own_len htc, osIxTchA,
        show 13 + c.yrLevel = 12 + c.yrLevel + 1 by omega, osSizesL_hi hyr.le 1]
      rfl
    have hpos : ∀ i < (osLvA c j).queries, (osLvA c j).posOff + i < osPosTotal c :=
      fun i hi ↦ posOff_add_lt hjl hpo (lt_of_lt_of_le hi hqS)
    unfold osSlowRetA
    refine hls j hjy hnm Lk _ _ _ _ _ _ _ (zeroOf_01 _) (fun q hq' t ht ↦ ?_) (fun rd hlow hm ↦ ?_)
    · have hptr : ∀ e o t, (osPtrA c b0 e * gen ^ o).limb 0 * addressOfIndex t =
          addressOfIndex (baseA c b0 e + (o + t)) := fun e o t ↦ by
        rw [osPtrA_mul, limb_ofK_addr, Nat.add_assoc]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl <;> simp only at ht
      · exact ⟨_, hptr osIxQposA _ t, regionL_lkA_buf hlen h9 (by decide)
          (by rw [← osOwnA, hlen9]; exact hpos t ht)⟩
      · exact ⟨_, hptr osIxFchA _ t, regionL_lkA_buf hlen h2 (by decide) (by rw [← osOwnA, hlen2]; omega)⟩
      · exact ⟨_, limb_ofK_addr _ t, regionL_lkA_buf hlen htc (by simp only [osIxTchA, osIxQbpA]; omega)
          (by rw [← osOwnA, hlenT]; omega)⟩
    · have hM := osMemA_of_lk hlen hm
      refine ⟨fun i hi ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
      · exact osMemA_load_mul hM h9 (by decide) (by rw [hlen9]; exact hpos i hi)
      · simp only [ht, ↓reduceIte]
        exact osMemA_load_mul hM h2 (by decide) (by rw [hlen2]; omega)
      · simp only [show ¬ ((osLvA c j).prefixLen + t < (osLvA c j).prefixLen) by omega, ↓reduceIte,
          Nat.add_sub_cancel_left]
        exact osMemA_load hM htc (by simp only [osIxTchA, osIxQbpA]; omega) (by rw [hlenT]; omega)
  -- a residual dispatch
  have hjy : j < c.yrLevel := by simpa [Nat.min_eq_left hyr.le] using hj
  have hjl : j < c.levels.length := by omega
  obtain ⟨-, -, -, -, hlrv⟩ := hHV j hjl
  obtain ⟨ha, hr, -, -⟩ := hlrv hjy
  obtain ⟨-, -, -, hpo, hqS, -, -, -, -, -, -, -, hcols, hfolds, -⟩ := hLv j hjl
  have hE := hlr j hjy (osKids_names hdo _ hin)
  show CompleteAtO fs cert κ (osResidualName (osLvA c j)) Lk
    (((osLrCalls c).getD j ([], [])).1.map σ) (Returns (((osLrCalls c).getD j ([], [])).2.map σ))
    (Bd.map (· (osResidualName (osLvA c j))))
  rw [ha, hr]
  have h6 : 6 < (osSizesL c).length := by omega
  have h9 : osIxQposA < (osSizesL c).length := by simp only [osIxQposA]; omega
  have hbd : osIxBdA c < (osSizesL c).length := by unfold osIxBdA; omega
  have hlen6 : (osOwnA H.own 6).length = c.levels.length * hsStride := by
    rw [osOwnA, forall₂_getD_len H.own_len h6]; rfl
  have hlen9 : (osOwnA H.own osIxQposA).length = osPosTotal c := by
    rw [osOwnA, forall₂_getD_len H.own_len h9]; rfl
  have hlenB : (osOwnA H.own (osIxBdA c)).length = c.levels.length * ligColsCap := by
    rw [osOwnA, forall₂_getD_len H.own_len hbd, osIxBdA,
      show 16 + c.yrLevel = 12 + c.yrLevel + 4 by omega, osSizesL_hi hyr.le 4]
    rfl
  have hstep : ∀ (w j' : ℕ), j' < c.levels.length → ∀ t < w, j' * w + t < c.levels.length * w :=
    fun w j' hj' t ht ↦ by
      have : (j' + 1) * w ≤ c.levels.length * w := Nat.mul_le_mul_right _ hj'
      rw [Nat.add_mul, one_mul] at this; omega
  have hpos : ∀ i < (osLvA c j).queries, (osLvA c j).posOff + i < osPosTotal c :=
    fun i hi ↦ posOff_add_lt hjl hpo (lt_of_lt_of_le hi hqS)
  refine hE Lk (osPtrA c b0 osIxQposA * gen ^ (osLvA c j).posOff)
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
    · exact ⟨_, hptr osIxQposA _ t, regionL_lkA_buf hlen h9 (by decide)
        (by rw [← osOwnA, hlen9]; exact hpos t ht)⟩
    · exact ⟨_, hptr (osIxBdA c) _ t, regionL_lkA_buf hlen hbd (by simp only [osIxBdA, osIxQbpA]; omega)
        (by rw [← osOwnA, hlenB]; exact hstep _ _ hjl _ (lt_of_lt_of_le ht hcols))⟩
    · exact ⟨_, hptr osIxHsA _ t, regionL_lkA_buf hlen h6 (by decide)
        (by rw [← osOwnA, hlen6]; exact hstep _ _ hjl _ (lt_of_lt_of_le ht hfolds))⟩
  · have hM := osMemA_of_lk hlen hm
    refine ⟨fun i hi ↦ ?_, fun s hs ↦ ?_, fun t ht ↦ ?_⟩
    · exact osMemA_load_mul hM h9 (by decide) (by rw [hlen9]; exact hpos i hi)
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

/-- **The frames after the levels are placed within a bound by trees satisfying `armXT`.** -/
theorem arm_rest_okT {Bd : Option (String → ℕ)} {c : OsCfg} {args : List E} {cur tabs : E}
    {xs : List E} {tgt inn res : E} {pt pt1 : List E}
    (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) {Lin : Layout} {b0 : ℕ} {σ : Val}
    (hall : ∀ rd, LowDef κ rd → MemL rd (osLkA c b0 H.own Lin) → ∃ σ',
      Whir.AllOk (osCR rd (fun _ _ _ ↦ True) (OsXOk κ (osLkA c b0 H.own Lin))) rd σ' (osBodyA c) ∧
        CallAg (osBodyA c) σ' σ)
    (hdo : ∀ s ∈ osBodyA c, DispOk σ s)
    (hfl : ∀ s ∈ osBodyA c, ∀ x fs a r, s = .dispatch x fs a r → fs.length < 2 ^ 64 - 1)
    (hB : (osBodyPre c).all bodyOkS = true)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLkA c b0 H.own Lin))
    (hHV : OsHelperVals c b0 tabs H.own H.D σ)
    (hsel : ∀ l (f : OsLv → String), selName σ c l f = f (osLvA c l))
    (hyr : c.yrLevel < c.levels.length)
    (hLv : ∀ l < c.levels.length, LvFacts c l)
    (hnamed : ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hnamedT : ∀ Bk ∈ Bd, ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtDTBR fs cert κ f L' args (Returns rets) armXT (Bk f))
    (hlr : ∀ j < c.yrLevel, osResidualName (osLvA c j) ∈ osCalleeNames c → LrAtOq fs cert κ (osResidualName (osLvA c j)) (osLvA c j).logCols (osLvA c j).folds
      (osLvA c j).highBits (osLvA c j).queries (Bd.map (· (osResidualName (osLvA c j)))))
    (hffm : (osKindOf ("fold_final_msg__L" ++ natStr c.yrLog)).isSome = true) (hsf : SlowFacts c)
    (hls : ∀ j < c.yrLevel, osSlowName c (osLvA c j) ∈ osCalleeNames c →
      LsAtO fs cert κ (osSlowName c (osLvA c j)) (osLvA c j).queries (osLvA c j).prefixLen c.yrLog
        (osLvA c j).vanish (Bd.map (· (osSlowName c (osLvA c j)))))
    {Bk : String → ℕ} (hBk : Bk ∈ Bd) {c' : Call}
    (hc' : c' ∈ ((osTlA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
      (finFrames σ c).map (Main.mkCall σ))
    (hin : c' ∈ ((osBodyA c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (ht : c'.taken = true) :
    CompleteAtDTBR fs cert κ c'.f (osLkA c b0 H.own Lin) (c'.args.map σ) (Returns (c'.rets.map σ)) armXT
      (Bk c'.f) := by
  have hO := arm_rest_ok H hall hdo hfl hB hex hHV hsel hyr hLv hnamed hlr hffm hsf hls hc' hin ht
  obtain rfl : Bd = some Bk := hBk
  have hnm : ∀ K, osKindOf c'.f = some K → CompleteAtDTBR fs cert κ c'.f (osLkA c b0 H.own Lin) (c'.args.map σ)
      (Returns (c'.rets.map σ)) armXT (Bk c'.f) :=
    fun K hK ↦ os_kid_namedX hall hdo hfl hex hin ht hK (hnamedT Bk rfl c'.f (osKids_names hdo c' hin) K hK · · _)
  rcases List.mem_append.mp hc' with hc | hc
  · obtain ⟨K, hK⟩ := named_of_plain hB (fun s hs ↦ tl_sub_body hs) hc
    exact hnm K hK
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  rcases mem_finFrames hx with rfl | hiz | ⟨j, hj, rfl | rfl⟩
  · obtain ⟨K, hK⟩ := Option.isSome_iff_exists.mp hffm
    exact hnm K hK
  · exact hnm .iz (by rw [mkCall_f', hiz]; exact osKindOf_isZero)
  · have hjy : j < c.yrLevel := by simpa [Nat.min_eq_left hyr.le] using hj
    have hjl : j < c.levels.length := by omega
    refine hO.toB.toDTB.toR.monoN le_rfl fun _ _ hn _ ↦ armXT_of_not ?_
    rw [hn]
    show armExactS (osResidualName (osLvA c j)) = false
    have h := armExactS_lr ((hLv j hjl).2.2.1 hjy).1
    exact h
  · have hjy : j < c.yrLevel := by simpa [Nat.min_eq_left hyr.le] using hj
    refine hO.toB.toDTB.toR.monoN le_rfl fun _ _ hn _ ↦ armXT_of_not ?_
    rw [hn]
    show armExactS (selName σ c j (osSlowName c)) = false
    rw [hsel]
    exact (hsf.2 j hjy).2.1

end
end LeanVM.Guest.B1.Arm
