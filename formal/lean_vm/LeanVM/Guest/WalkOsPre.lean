/-
  LeanVM.Guest.WalkOsPre

  `open_stacked`'s window pointers name windows on every prefix of its body that reaches a level's
  `opening_queries` call: the walk's obligation at that call (`OqMainWins`), from the decodes
  before it and the window table `tabs` the function assumes.
-/

module

public import LeanVM.Guest.WalkOsDefs
public import LeanVM.Guest.B1.Whir.Flatness
public import LeanVM.Guest.B1.Whir.Squeezes
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
  each of the level's queries, a frame run of its windows (the squeezes' decodes,
  `osSqueezes_sound`, reading the window table at `tabs`, which the function assumes).
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

theorem osQueriesA_prefix (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osQueriesA c lvl lv s).1 <+: (osQueries c lvl lv s).1 :=
  ⟨_, rfl⟩

theorem osLevelPre_prefix (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    osLevelPre c lvl lv s <+: (osLevel c lvl lv s).1 :=
  ((List.prefix_append_right_inj _).mpr (osQueriesA_prefix c lvl lv (osQState c lvl lv s))).trans
    (List.prefix_append _ _)

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
  rw [osBody_eq]
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

/-! ## The materializations -/

theorem osRound_mats {P : List (ℕ × ℕ × ℕ)} {i : ℕ} {s : OsSt} (hb : 3 * i < u128Bound)
    (hm : MatsOk σ s.mats) (h : AllOk C rd σ (osRound P i s).1) :
    MatsOk σ (osRound P i s).2.mats := by
  unfold osRound at h ⊢
  simp only [allOk_append] at h
  obtain ⟨⟨⟨-, hf⟩, hc⟩, -⟩ := h
  exact (osMatS_val' hc (osMatS_val' hf hm (by omega)).2 hb).2

theorem osRounds_mats {P : List (ℕ × ℕ × ℕ)} : ∀ (i n : ℕ) (s : OsSt), 3 * (i + n) < u128Bound →
    MatsOk σ s.mats → AllOk C rd σ (osRounds P i n s).1 → MatsOk σ (osRounds P i n s).2.mats
  | _, 0, _, _, hm, _ => hm
  | i, n + 1, s, hb, hm, h => by
    simp only [osRounds, allOk_append] at h ⊢
    exact osRounds_mats (i + 1) n _ (by omega) (osRound_mats (by omega) hm h.1) h.2

theorem osCommit_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt}
    (hb : (oodSamples * (lvl + 1) + 1) * ligColsCap < u128Bound) (hm : MatsOk σ s.mats)
    (h : AllOk C rd σ (osCommit c lvl lv s).1) : MatsOk σ (osCommit c lvl lv s).2.mats := by
  have hb0 : oodSamples * (lvl + 1) * ligColsCap < u128Bound :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ _)) hb
  unfold osCommit at h ⊢
  simp only [allOk_append, and_assoc] at h
  obtain ⟨-, -, -, h0, -, h1, -⟩ := h
  exact (osMatS_val' h1 (osMatS_val' h0 hm hb0).2 hb).2

theorem osMsg_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt}
    (hb : (oodSamples * (lvl + 1) + 1) * ligColsCap < u128Bound) (hm : MatsOk σ s.mats)
    (h : AllOk C rd σ (if lvl = c.yrLevel then osFinalMsg c lv s else osCommit c lvl lv s).1) :
    MatsOk σ (if lvl = c.yrLevel then osFinalMsg c lv s else osCommit c lvl lv s).2.mats := by
  split_ifs at h ⊢
  · exact hm
  · exact osCommit_mats hb hm h

theorem osMsg_fs (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (if lvl = c.yrLevel then osFinalMsg c lv s else osCommit c lvl lv s).2.fs.length = 5 := by
  split_ifs <;> rfl

theorem osSqueezes_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} (hb : lv.posOff < u128Bound)
    (hm : MatsOk σ s.mats) (h : AllOk C rd σ (osSqueezes c lvl lv s).1) :
    MatsOk σ (osSqueezes c lvl lv s).2.mats := by
  unfold osSqueezes at h ⊢
  simp only [allOk_append, and_assoc] at h
  obtain ⟨-, -, hq, hw, -⟩ := h
  exact (osMatS_val' hw (osMatS_val' hq hm hb).2 hb).2

theorem osLa_mats (c : OsCfg) (lvl : ℕ) (s : OsSt) :
    (if lvl = c.yrLevel then (([] : List Stmt), s) else osLam s).2.mats = s.mats := by
  split_ifs <;> rfl

theorem osCap_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} (hb : 4 * lv.capOff < u128Bound)
    (hm : MatsOk σ s.mats) (h : AllOk C rd σ (osCap c lvl lv s).1) :
    MatsOk σ (osCap c lvl lv s).2.mats := by
  unfold osCap at h ⊢
  simp only [allOk_append, and_assoc] at h
  obtain ⟨hc, hf, -⟩ := h
  exact (osMatS_val' hf (osMatS_val' hc hm hb).2 (by omega)).2

theorem osHs_mats (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (if lvl = c.yrLevel then osHsFinal c lv s else osHsMid lvl lv s).2.mats = s.mats := by
  split_ifs <;> rfl

/-- **A level's queries block up to its window pointers**: the pointers are
`query_win_ptrs·g^posOff`, and the materializations hold after the block. -/
theorem osQueriesA_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} (hb : LvMatB lvl lv)
    (hm : MatsOk σ s.mats) (h : AllOk C rd σ (osQueriesA c lvl lv s).1) :
    σ (.n (osQueriesA c lvl lv s).2) = σ (.n osQbp) * gen ^ lv.posOff ∧
      MatsOk σ (osQueries c lvl lv s).2.mats := by
  obtain ⟨hb0, -, hb2, hb3, hb4⟩ := hb
  unfold osQueriesA osQueries at *
  simp only [allOk_append] at h
  obtain ⟨⟨⟨⟨⟨⟨hcp, hfl⟩, hli⟩, hcf⟩, hhp⟩, hqp⟩, hwp⟩ := h
  obtain ⟨-, hm1⟩ := osMatS_val' hcp hm hb2
  obtain ⟨-, hm2⟩ := osMatS_val' hfl hm1 (by omega)
  by_cases hfin : lvl = c.yrLevel
  · simp only [hfin, ↓reduceIte] at hcf hhp hqp hwp ⊢
    obtain ⟨-, hm3⟩ := osMatS_val' hcf hm2 (by omega)
    obtain ⟨-, hm4⟩ := osMatS_val' hqp hm3 hb4
    exact osMatS_val' hwp hm4 hb4
  · simp only [hfin, ↓reduceIte] at hcf hhp hqp hwp ⊢
    obtain ⟨-, hm3⟩ := osMatS_val' hcf hm2 (by omega)
    obtain ⟨-, hm4⟩ := osMatS_val' hhp hm3 hb3
    obtain ⟨-, hm5⟩ := osMatS_val' hqp hm4 hb4
    exact osMatS_val' hwp hm5 hb4

/-- **A level's materializations hold** up to its window pointers, and the pointers are
`query_win_ptrs·g^posOff`. -/
theorem osLevelPre_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} (hb : LvMatB lvl lv)
    (hm : MatsOk σ s.mats) (h : AllOk C rd σ (osLevelPre c lvl lv s)) :
    σ (.n (osQueriesA c lvl lv (osQState c lvl lv s)).2) = σ (.n osQbp) * gen ^ lv.posOff ∧
      MatsOk σ (osQueries c lvl lv (osQState c lvl lv s)).2.mats := by
  have hb' := hb
  obtain ⟨hb0, hb1, hb2, -, hb4⟩ := hb'
  unfold osLevelPre at h
  simp only [allOk_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hf, hM⟩, -⟩, hS⟩, -⟩, hC⟩, -⟩, hA⟩ := h
  have k1 := osRounds_mats (P := c.plan) lv.foldsOff lv.folds s (by omega) hm hf
  have k2 := osMsg_mats hb1 k1 hM
  have k3 := osSqueezes_mats hb4 k2 hS
  rw [← osLa_mats c lvl] at k3
  have k4 := osCap_mats hb2 k3 hC
  rw [← osHs_mats c lvl lv] at k4
  exact osQueriesA_mats hb k4 hA

theorem osLevel_mats_eq (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    (osLevel c lvl lv s).2.mats = (osQueries c lvl lv (osQState c lvl lv s)).2.mats := by
  by_cases h : lvl = c.yrLevel
  · simp only [osLevel, osQState, h, ↓reduceIte]
  · simp only [osLevel, osQState, h, ↓reduceIte]
    rfl

/-- **A level's materializations hold** after it. -/
theorem osLevel_mats {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} (hb : LvMatB lvl lv)
    (hm : MatsOk σ s.mats) (h : AllOk C rd σ (osLevel c lvl lv s).1) :
    MatsOk σ (osLevel c lvl lv s).2.mats := by
  rw [osLevel_mats_eq]
  exact (osLevelPre_mats hb hm (allOk_of_prefix (osLevelPre_prefix c lvl lv s) h)).2

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

/-- **The window pointers name windows**: every decoded query's pointer, at `qbp·g^po`, a frame
run of its windows at a position below `2^d`. -/
theorem queryWinsOk_of_decodes {d cd po q nsq : ℕ} (hd : 1 ≤ 128 / d) (hq : q ≤ nsq * (128 / d))
    {qpos qbp tabs : E}
    (hdec : ∀ jj < nsq, ∃ w, MeaningDecodeQueryWindows d cd rd [w,
      qpos * gen ^ (po + jj * (128 / d)), qbp * gen ^ (po + jj * (128 / d)), tabs] []) :
    QueryWinsOk rd (qbp * gen ^ po) q d cd := by
  intro k hk bp hbp
  set per := 128 / d
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
  pw : digitsVal (osPowDigits (128 / (c.levels.getD ℓ default).depth)) 1 =
    128 / (c.levels.getD ℓ default).depth
  per : 1 ≤ 128 / (c.levels.getD ℓ default).depth
  q : (c.levels.getD ℓ default).queries ≤
    (c.levels.getD ℓ default).squeezes * (128 / (c.levels.getD ℓ default).depth)
  sq1 : 1 ≤ (c.levels.getD ℓ default).squeezes
  sqOrd : (c.levels.getD ℓ default).squeezes < ordG
  sq5 : (c.levels.getD ℓ default).squeezes * 5 < u128Bound
  mats : ∀ i ≤ ℓ, i < c.levels.length → LvMatB i (c.levels.getD i default)
  dec : ∀ args rets, WinTabs rd (args.getD 3 0) →
    coreProgram.Rel rd (decName (c.levels.getD ℓ default)) args rets →
    MeaningDecodeQueryWindows (c.levels.getD ℓ default).depth (c.levels.getD ℓ default).capDepth
      rd args rets

/-- **A level's window pointers name windows**, from its statements up to them. -/
theorem osLevelPre_wins {c : OsCfg} {lvl : ℕ} {lv : OsLv} {s : OsSt} (hb : LvMatB lvl lv)
    (hloop : FnIs (c.sqLoop lvl) (osParams 6) (sqLoopBody lv (c.sqLoop lvl)))
    (hpw : digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth) (hper : 1 ≤ 128 / lv.depth)
    (hq : lv.queries ≤ lv.squeezes * (128 / lv.depth)) (hS : 1 ≤ lv.squeezes)
    (hSo : lv.squeezes < ordG) (hS5 : lv.squeezes * 5 < u128Bound)
    (hdec : ∀ a r, WinTabs rd (a.getD 3 0) → coreProgram.Rel rd (decName lv) a r →
      MeaningDecodeQueryWindows lv.depth lv.capDepth rd a r)
    (hwt : WinTabs rd (σ (.n osTabs))) (hm : MatsOk σ s.mats)
    (h : AllOk (coreProgram.Rel rd) rd σ (osLevelPre c lvl lv s)) :
    QueryWinsOk rd (σ (.n (osQueriesA c lvl lv (osQState c lvl lv s)).2)) lv.queries lv.depth
      lv.capDepth := by
  have hb' := hb
  obtain ⟨hb0, hb1, -, -, hb4⟩ := hb'
  rw [(osLevelPre_mats hb hm h).1]
  unfold osLevelPre at h
  simp only [allOk_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hf, hM⟩, -⟩, hS'⟩, -⟩, -⟩, -⟩, -⟩ := h
  have k1 := osRounds_mats (P := c.plan) lv.foldsOff lv.folds s (by omega) hm hf
  have k2 := osMsg_mats hb1 k1 hM
  have out := osSqueezes_sound (fun _ _ _ h ↦ h) hdec hloop hpw hb4 hS hSo hS5 hwt k2
    (osMsg_fs c lvl lv _) rfl rfl hS'
  exact queryWinsOk_of_decodes hper hq fun jj hjj ↦ ⟨_, out.dec jj hjj⟩

/-- **Level `ℓ`'s window pointers name windows**, on any prefix of `open_stacked`'s body reaching
them, the window table at `tabs`. -/
theorem osPre_queryWinsOk {c : OsCfg} {ℓ : ℕ} (hℓ : ℓ < c.levels.length) (hF : OsWalkLv rd c ℓ)
    (hwt : WinTabs rd (σ (.n osTabs))) {n : ℕ} (hn : (osPre c ℓ).length ≤ n) {next : Prop}
    {kret : List E → Prop}
    (hl : Stmt.HoldsList (coreProgram.Rel rd) rd σ ((osBody c).take n) next kret) :
    QueryWinsOk rd (σ (.n (osPreBp c ℓ))) (c.levels.getD ℓ default).queries
      (c.levels.getD ℓ default).depth (c.levels.getD ℓ default).capDepth := by
  have hok := allOk_osPre hℓ hn hl
  unfold osPre at hok
  simp only [allOk_append] at hok
  obtain ⟨-, hLs, hP⟩ := hok
  have hm0 : MatsOk σ (osStAt c ℓ).mats := by
    refine osLevels_mats 0 _ _ (fun i hi ↦ ?_) (matsOk_nil σ) hLs
    simp only [List.length_take] at hi
    simp only [Nat.zero_add, List.getElem_take]
    rw [← List.getD_eq_getElem _ default (by omega)]
    exact hF.mats i (by omega) (by omega)
  exact osLevelPre_wins (hF.mats ℓ le_rfl hℓ) hF.loop hF.pw hF.per hF.q hF.sq1 hF.sqOrd hF.sq5
    hF.dec hwt hm0 hP

/-- A level's queries are `oqCount` of its call's `odd`, `base` and iterations. -/
theorem oqCount_q (q ℓ : ℕ) : oqCount (q % 2 * (if ℓ = 0 then 1 else 0)) (if ℓ = 0 then 1 else 0)
    (q / (1 + if ℓ = 0 then 1 else 0)) = q := by
  by_cases h : ℓ = 0
  · simp [oqCount, h]
    omega
  · simp [oqCount, h]

/-- **`opening_queries`' obligation at level `ℓ`'s call** (`OqMainWins` at `n_iters_g =
g^(queries / (1 + base))`), on any prefix of `open_stacked`'s body reaching the window pointers. -/
theorem osPre_oqMainWins {c : OsCfg} {ℓ : ℕ} (hℓ : ℓ < c.levels.length) (hF : OsWalkLv rd c ℓ)
    (hwt : WinTabs rd (σ (.n osTabs))) {n : ℕ} (hn : (osPre c ℓ).length ≤ n) {next : Prop}
    {kret : List E → Prop}
    (hl : Stmt.HoldsList (coreProgram.Rel rd) rd σ ((osBody c).take n) next kret) :
    OqMainWins rd (c.levels.getD ℓ default).depth (c.levels.getD ℓ default).capDepth
      ((c.levels.getD ℓ default).queries % 2 * (if ℓ = 0 then 1 else 0)) (if ℓ = 0 then 1 else 0)
      (σ (.n (osPreBp c ℓ)))
      (gen ^ ((c.levels.getD ℓ default).queries / (1 + if ℓ = 0 then 1 else 0))) := by
  have h := osPre_queryWinsOk hℓ hF hwt hn hl
  rw [← oqCount_q (c.levels.getD ℓ default).queries ℓ] at h
  refine oqMainWins_of_queryWinsOk (fun h1 ↦ ?_) h
  by_cases h0 : ℓ = 0
  · simp [h0]
  · simp [h0] at h1

end
end LeanVM.Guest.B1.Whir
