/-
  LeanVM.Guest.WalkOsPre

  `open_stacked`'s window pointers name windows on every prefix of its body that reaches a level's
  `opening_queries` call: the walk's obligation at that call (`OqMainWins`), from the decodes
  before it.
-/

module

public import LeanVM.Guest.WalkOsDefs
public import LeanVM.Guest.B1.Whir.Flatness
public import LeanVM.Guest.B1.Whir.Head
public import LeanVM.Guest.B1.Opening.QueriesWalk

/-!
# `open_stacked`'s walk obligations, on a prefix (TRIAGE G #42)

Checker K cuts `open_stacked__L{m}` before each level's `opening_queries` call and asks there, on the
statements before the cut, the callee's precondition `OqMainWins` on the call's `query_win_ptrs`
(REC-GUEST-IFACE 'tool: walk obligations'). The cut comes before the call's constant `n_iters_g`
(the compiler sets it in the call's setup), after the window pointers' materialization.

* `osPre c ℓ`: the head, the levels before `ℓ`, and level `ℓ` up to its window pointers
  (`osLevelPre`), a prefix of the body (`osPre_prefix`); every statement of it holds on any prefix of
  the body at least as long (`allOk_osPre`).
* `osPre_queryWinsOk`: from those statements, the level's window pointers
  `σ (osPreBp c ℓ) = query_win_ptrs·g^posOff` (the materializations, `osLevels_mats`) name, for
  each of the level's queries, a frame run of its windows (the squeeze loop's decodes,
  `osSqueezes_wins`, reading the window table the head writes, `osHead_winTabs`).
* `osPre_oqMainWins`: hence `OqMainWins` at `n_iters_g = g^(queries / (1 + base))`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Prefixes -/

theorem allOk_of_prefix {ss ts : List Stmt} (h : ss <+: ts) (hok : AllOk C rd σ ts) :
    AllOk C rd σ ss :=
  fun s hs ↦ hok s (h.subset hs)

theorem flat_of_prefix {ss ts : List Stmt} (h : ss <+: ts) (hf : Flat ts) : Flat ss := by
  obtain ⟨t, rfl⟩ := h
  simp only [Flat, List.all_append, Bool.and_eq_true] at hf
  exact hf.1

theorem osQueriesA_prefix (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt) :
    osQueriesA c lvl lv s <+: (osQueries c lvl lv lam lamN s).1 :=
  ⟨_, rfl⟩

theorem osLevelPre_prefix (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    osLevelPre c lvl lv s <+: (osLevel c lvl lv s).1 := by
  have h1 := osQueriesA_prefix c lvl lv
    ((osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).2.k - 1)
    (osLamPow lvl ((osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).2.k - 1) lv.queries
      (osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).2.k).2.1 (osLevelQ c lvl lv s)
  refine List.IsPrefix.trans ((List.prefix_append_right_inj _).mpr h1) ?_
  exact ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans (List.prefix_append _ _)

/-- The levels before `ℓ` and level `ℓ` up to its window pointers. -/
theorem osLevels_pre (c : OsCfg) : ∀ (ℓ lvl : ℕ) (lvs : List OsLv) (s : OsSt) (h : ℓ < lvs.length),
    (osLevels c lvl (lvs.take ℓ) s).1 ++
      osLevelPre c (lvl + ℓ) lvs[ℓ] (osLevels c lvl (lvs.take ℓ) s).2 <+: (osLevels c lvl lvs s).1
  | 0, lvl, lv :: rest, s, _ => by
    simp only [List.take_zero, osLevels, List.nil_append, Nat.add_zero, List.getElem_cons_zero]
    exact (osLevelPre_prefix c lvl lv s).trans (List.prefix_append _ _)
  | ℓ + 1, lvl, lv :: rest, s, h => by
    have ih := osLevels_pre c ℓ (lvl + 1) rest (osLevel c lvl lv s).2 (by simp at h; omega)
    simp only [List.take_succ_cons, osLevels, List.getElem_cons_succ, List.append_assoc]
    rw [show lvl + (ℓ + 1) = lvl + 1 + ℓ by omega]
    exact (List.prefix_append_right_inj _).mpr ih

theorem osPre_prefixA {c : OsCfg} {ℓ : ℕ} (h : ℓ < c.levels.length) : osPre c ℓ <+: osBodyA c := by
  have hL := osLevels_pre c ℓ 0 c.levels (osHead c).2 h
  rw [Nat.zero_add] at hL
  rw [← List.getD_eq_getElem _ default h] at hL
  refine List.IsPrefix.trans ((List.prefix_append_right_inj _).mpr hL) ?_
  unfold osBodyA
  exact (List.prefix_append _ _).trans (List.prefix_append _ _)

theorem osPre_prefix {c : OsCfg} {ℓ : ℕ} (h : ℓ < c.levels.length) : osPre c ℓ <+: osBody c := by
  rw [osBody_split]
  exact (osPre_prefixA h).trans (List.prefix_append _ _)

/-- **Every statement up to level `ℓ`'s window pointers holds**, on a prefix of the body at least
as long. -/
theorem allOk_osPre {c : OsCfg} {ℓ : ℕ} (h : ℓ < c.levels.length) {n : ℕ}
    (hn : (osPre c ℓ).length ≤ n) {next : Prop} {kret : List E → Prop}
    (hl : Stmt.HoldsList C rd σ ((osBody c).take n) next kret) : AllOk C rd σ (osPre c ℓ) := by
  obtain ⟨t, ht⟩ := osPre_prefix h
  rw [← ht, List.take_append, List.take_of_length_le hn, holdsList_append,
    holdsList_flat _ (flat_of_prefix (osPre_prefixA h) (osBodyA_flat c))] at hl
  exact hl.1

/-! ## The window table -/

theorem osHead_winTabs {c : OsCfg} (h : AllOk C rd σ (osHead c).1) : WinTabs rd (σ (.n osWin)) := by
  apply osWinTabs_sound (C := C)
  intro x hx
  refine h x ?_
  simp only [osHead, List.mem_append]
  simp [hx]

/-! ## The materializations -/

theorem osLevelM_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt}
    (hb : (lvl + 1) * ligColsCap < u128Bound) (hm : MatsOk σ s.mats)
    (h : AllOk C rd σ (osLevelM c lvl lv s).1) : MatsOk σ (osLevelM c lvl lv s).2.1.mats := by
  unfold osLevelM at h ⊢
  split
  · show MatsOk σ (osFolds osFch lv.foldsOff lv.folds s).2.mats
    rw [osFolds_mats]; exact hm
  · rename_i hne
    simp only [hne, ↓reduceIte] at h
    have hm' : MatsOk σ (osFolds osFch lv.foldsOff lv.folds s).2.mats := by
      rw [osFolds_mats]; exact hm
    refine osMatsAfter_ok hm' hb fun x hx ↦ h x ?_
    simp only [osCommit, List.mem_append]
    simp [hx]

/-- **A level's materializations hold** up to its window pointers, and the pointers are
`query_win_ptrs·g^posOff`. -/
theorem osLevelPre_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} (hb : LvMatB lvl lv)
    (hm : MatsOk σ s.mats) (h : AllOk C rd σ (osLevelPre c lvl lv s)) :
    MatsOk σ (osQueriesM3 c lv (osLevelQ c lvl lv s)) ∧
      σ (.n (osQueriesBpS c lv (osLevelQ c lvl lv s)).2.1) = σ (.n osQbp) * gen ^ lv.posOff ∧
      MatsOk σ (osQueriesMats c lv (osLevelQ c lvl lv s)) := by
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hb
  unfold osLevelPre at h
  simp only [allOk_append] at h
  obtain ⟨⟨⟨⟨⟨-, hM⟩, -⟩, -⟩, -⟩, hQ⟩ := h
  have hq0 : MatsOk σ (osLevelQ c lvl lv s).mats := by
    show MatsOk σ (osLevelM c lvl lv s).2.1.mats
    exact osLevelM_mats hb0 hm hM
  unfold osQueriesA at hQ
  simp only [allOk_append] at hQ
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hfp⟩, -⟩, hcp⟩, hflp⟩, -⟩, -⟩, -⟩, hbp⟩ := hQ
  have k1 := osMatsAfter_ok hq0 hb1 hfp
  have k2 := osMatsAfter_ok k1 hb2 hcp
  have k3 := osMatsAfter_ok k2 hb3 hflp
  exact ⟨k3, osMatP_val k3 hb4 hbp, osMatsAfter_ok k3 hb4 hbp⟩

theorem osLevel_mats_eq (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osLevel c lvl lv s).2.mats = osQueriesMats c lv (osLevelQ c lvl lv s) := by
  unfold osLevel osLevelQ osLevelM
  by_cases h : lvl = c.yrLevel
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    rfl

/-- **A level's materializations hold** after it. -/
theorem osLevel_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} (hb : LvMatB lvl lv)
    (hm : MatsOk σ s.mats) (h : AllOk C rd σ (osLevel c lvl lv s).1) :
    MatsOk σ (osLevel c lvl lv s).2.mats := by
  rw [osLevel_mats_eq]
  exact (osLevelPre_mats hb hm (allOk_of_prefix (osLevelPre_prefix c lvl lv s) h)).2.2

theorem osLevels_mats {c : OsCfg} : ∀ (lvl : ℕ) (lvs : List OsLv) (s : OsSt),
    (∀ i (hi : i < lvs.length), LvMatB (lvl + i) lvs[i]) → MatsOk σ s.mats →
    AllOk C rd σ (osLevels c lvl lvs s).1 → MatsOk σ (osLevels c lvl lvs s).2.mats
  | _, [], _, _, hm, _ => hm
  | lvl, lv :: rest, s, hb, hm, h => by
    simp only [osLevels, allOk_append] at h ⊢
    have h0 := osLevel_mats (hb 0 (by simp)) hm h.1
    exact osLevels_mats (lvl + 1) rest _ (fun i hi ↦ by
      have := hb (i + 1) (by simp; omega)
      rwa [show lvl + (i + 1) = lvl + 1 + i by omega] at this) h0 h.2

/-! ## The squeezes' decodes -/

/-- **A level's squeeze loop decodes** every squeeze's positions and windows at
`query_win_ptrs·g^(posOff + jj·(192/depth))`. -/
theorem osSqueezes_wins {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hok : AllOk (coreProgram.Rel rd) rd σ (osSqueezes c lvl lv st).1)
    (hloop : FnIs (c.sqLoop lvl) (osParams 6) (sqLoopBody lv (c.sqLoop lvl)))
    (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth)
    (hpo : lv.posOff < u128Bound)
    (hdec : ∀ args rets, WinTabs rd (args.getD 3 0) →
      coreProgram.Rel rd ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth)
        args rets → MeaningDecodeQueryWindows lv.depth lv.capDepth rd args rets)
    (hwt : WinTabs rd (σ (.n osWin)))
    (hn0 : 0 < lv.squeezes) (hn : lv.squeezes < ordG) :
    ∀ jj < lv.squeezes, ∃ w, MeaningDecodeQueryWindows lv.depth lv.capDepth rd
      [w, σ (.n osQpos) * gen ^ (lv.posOff + jj * (192 / lv.depth)),
        σ (.n osQbp) * gen ^ (lv.posOff + jj * (192 / lv.depth)), σ (.n osWin)] [] := by
  obtain ⟨fn, hfind, hps, hbody⟩ := hloop
  set k := st.k
  have hstm : (osSqueezes c lvl lv st).1 = osHeap ((c.maxSq + 1) * 5) k ++
      (st.fs.zipIdx.map fun (f, i) ↦ .atom (.load (.n f) (.n (k + 1)) i)) ++
      osLoopCall (c.sqLoop lvl) lv.squeezes [k + 1, osQpos, osQbp, osWin] (k + 2) ++
      [.atom (.const (.n (k + 7)) (gw (lv.squeezes * 5))),
        .atom (.mul (.n (k + 8)) (.n (k + 1)) (.n (k + 7)))] ++
      ((List.range 5).map fun i ↦ .atom (.load (.n (k + 9 + i)) (.n (k + 8)) i)) ++
      (osPad st.pad (k + 14)).1 ++ osSqueeze0 (osPad st.pad (k + 14)).2.1
        [k + 9, k + 10, k + 11, k + 12, k + 13] (osPad st.pad (k + 14)).2.2 := rfl
  rw [hstm] at hok
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hL⟩, -⟩, -⟩, -⟩, -⟩ := hok
  simp only [osLoopCall, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons,
    List.map_nil] at hL
  obtain ⟨c2, c3, a4, c5, c6, -, hcall⟩ := hL
  have hgn : gw lv.squeezes = gen ^ lv.squeezes := gw_eq (by
    have : ordG < u128Bound := by unfold ordG u128Bound; norm_num
    omega)
  have hit := sqLoop_sound hfind lv hps hbody hpw hpo hdec hn0 hn (σ (.n (k + 1))) (σ (.n osQpos))
    (σ (.n osQbp)) (σ (.n osWin)) hwt (by
      rw [a4, c2, c3, c5, c6, hgn, word_one] at hcall
      exact hcall)
  intro jj hjj
  obtain ⟨cap, -, -, -, h3⟩ := sqIter_at (hit jj hjj)
  exact ⟨_, h3⟩

/-- **The window pointers name windows**: every decoded query's pointer, at `qbp·g^po`, a frame
run of its windows at a position below `2^d`. -/
theorem queryWinsOk_of_decodes {d cd po q nsq : ℕ} (hd : 1 ≤ 192 / d) (hq : q ≤ nsq * (192 / d))
    {qpos qbp tabs : E}
    (hdec : ∀ jj < nsq, ∃ w, MeaningDecodeQueryWindows d cd rd [w,
      qpos * gen ^ (po + jj * (192 / d)), qbp * gen ^ (po + jj * (192 / d)), tabs] []) :
    QueryWinsOk rd (qbp * gen ^ po) q d cd := by
  intro k hk bp hbp
  set per := 192 / d
  have hjj : k / per < nsq := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact lt_of_lt_of_le hk hq
  have ht : k % per < per := Nat.mod_lt _ (by omega)
  have hk' : po + k = po + k / per * per + k % per := by
    have := Nat.div_add_mod k per; rw [Nat.mul_comm] at this; omega
  obtain ⟨w, hw⟩ := hdec (k / per) hjj
  obtain ⟨-, hall⟩ := hw
  obtain ⟨-, p, hptr, hrun⟩ := hall (k % per) ht
  rw [loadHolds_mul_gen_pow] at hbp
  rw [loadHolds_mul_gen_pow, ← hk'] at hptr
  rw [loadHolds_unique hbp hptr]
  exact ⟨qwPosOf d w (k % per), by unfold qwPosOf; exact Nat.mod_lt _ (by positivity), hrun⟩

/-! ## The obligation -/

/-- What `osPre_queryWinsOk` needs of a candidate's level: its squeeze loop's body, the decode's
specification, the numbers the loop and the materializations need. -/
structure OsWalkLv (rd : Reader) (c : OsCfg) (ℓ : ℕ) : Prop where
  loop : FnIs (c.sqLoop ℓ) (osParams 6) (sqLoopBody (c.levels.getD ℓ default) (c.sqLoop ℓ))
  pw : digitsVal (osPowDigits (192 / (c.levels.getD ℓ default).depth)) 1 =
    192 / (c.levels.getD ℓ default).depth
  per : 1 ≤ 192 / (c.levels.getD ℓ default).depth
  q : (c.levels.getD ℓ default).queries ≤
    (c.levels.getD ℓ default).squeezes * (192 / (c.levels.getD ℓ default).depth)
  sq0 : 0 < (c.levels.getD ℓ default).squeezes
  sqOrd : (c.levels.getD ℓ default).squeezes < ordG
  mats : ∀ i ≤ ℓ, i < c.levels.length → LvMatB i (c.levels.getD i default)
  dec : ∀ args rets, WinTabs rd (args.getD 3 0) →
    coreProgram.Rel rd ("decode_query_windows__L" ++ natStr (c.levels.getD ℓ default).depth ++ "_L" ++
      natStr (c.levels.getD ℓ default).capDepth) args rets →
    MeaningDecodeQueryWindows (c.levels.getD ℓ default).depth (c.levels.getD ℓ default).capDepth
      rd args rets

/-- **Level `ℓ`'s window pointers name windows**, on any prefix of `open_stacked`'s body reaching
them. -/
theorem osPre_queryWinsOk {c : OsCfg} {ℓ : ℕ} (hℓ : ℓ < c.levels.length) (hF : OsWalkLv rd c ℓ)
    {n : ℕ} (hn : (osPre c ℓ).length ≤ n) {next : Prop} {kret : List E → Prop}
    (hl : Stmt.HoldsList (coreProgram.Rel rd) rd σ ((osBody c).take n) next kret) :
    QueryWinsOk rd (σ (.n (osPreBp c ℓ))) (c.levels.getD ℓ default).queries
      (c.levels.getD ℓ default).depth (c.levels.getD ℓ default).capDepth := by
  have hok := allOk_osPre hℓ hn hl
  unfold osPre at hok
  simp only [allOk_append] at hok
  obtain ⟨hH, hLs, hP⟩ := hok
  have hwt := osHead_winTabs hH
  have hm0 : MatsOk σ (osStAt c ℓ).mats := by
    refine osLevels_mats 0 _ _ (fun i hi ↦ ?_) (matsOk_nil σ) hLs
    simp only [List.length_take] at hi
    simp only [Nat.zero_add, List.getElem_take]
    rw [← List.getD_eq_getElem _ default (by omega)]
    exact hF.mats i (by omega) (by omega)
  obtain ⟨-, hbp, -⟩ := osLevelPre_mats (hF.mats ℓ le_rfl hℓ) hm0 hP
  unfold osPreBp
  rw [hbp]
  unfold osLevelPre at hP
  simp only [allOk_append] at hP
  obtain ⟨⟨⟨-, hS⟩, -⟩, -⟩ := hP
  exact queryWinsOk_of_decodes hF.per hF.q (osSqueezes_wins hS hF.loop hF.pw
    (hF.mats ℓ le_rfl hℓ).2.2.2.2 hF.dec hwt hF.sq0 hF.sqOrd)

/-- **`opening_queries`' obligation at level `ℓ`'s call** (`OqMainWins` at `n_iters_g =
g^(queries / (1 + base))`), on any prefix of `open_stacked`'s body reaching the window pointers. -/
theorem osPre_oqMainWins {c : OsCfg} {ℓ : ℕ} (hℓ : ℓ < c.levels.length) (hF : OsWalkLv rd c ℓ)
    {n : ℕ} (hn : (osPre c ℓ).length ≤ n) {next : Prop} {kret : List E → Prop}
    (hl : Stmt.HoldsList (coreProgram.Rel rd) rd σ ((osBody c).take n) next kret) :
    OqMainWins rd (c.levels.getD ℓ default).depth (c.levels.getD ℓ default).capDepth
      ((c.levels.getD ℓ default).queries % 2 * (if ℓ = 0 then 1 else 0)) (if ℓ = 0 then 1 else 0)
      (σ (.n (osPreBp c ℓ)))
      (gen ^ ((c.levels.getD ℓ default).queries / (1 + if ℓ = 0 then 1 else 0))) := by
  have h := osPre_queryWinsOk hℓ hF hn hl
  rw [← oqCount_q (c.levels.getD ℓ default).queries ℓ] at h
  refine oqMainWins_of_queryWinsOk (fun h1 ↦ ?_) h
  by_cases h0 : ℓ = 0
  · simp [h0]
  · simp [h0] at h1

end
end LeanVM.Guest.B1.Whir
