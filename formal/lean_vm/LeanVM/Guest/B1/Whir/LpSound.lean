/-
  LeanVM.Guest.B1.Whir.LpSound

  `level_positions` (a level's query positions: the first word decoded, the other squeezes and
  their decodes), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Squeezes
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Whir.RateCfg

/-!
# `level_positions`, soundly

`MeaningLevelPositions S d cd`: on `[w0, f0..f4, qpos, qbp, tabs]`, sample `j < S` (`sqSample`:
`w0`, then the squeezes from the capacity `[f0..f4]`) decoded at `qpos·g^(j·(128/d))` and
`qbp·g^(j·(128/d))`, the returns the capacity after `S - 1` squeezes. `lp_sound`: a call of a
specialization whose body and loop are the templates establishes it (`sqLoop_sound`, `sqChain`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **What `level_positions__L{S}_L{d}_L{cd}` establishes** on `[w0, f0..f4, qpos, qbp, tabs]`. -/
def MeaningLevelPositions (S d cd : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  (∀ j < S, MeaningDecodeQueryWindows d cd rd
      [sqSample (args.getD 0 0) ((args.drop 1).take 5) j,
        args.getD 6 0 * gen ^ (j * (128 / d)), args.getD 7 0 * gen ^ (j * (128 / d)),
        args.getD 8 0] []) ∧
    rets = ((⟨(args.drop 1).take 5, []⟩ : Fs).squeezeN (S - 1)).2.cap

theorem lpBody_split (S d cd : ℕ) (loop : String) :
    lpBody S d cd loop =
      (osHeap ((S + 1) * 5) 9 ++ ((List.range 5).map fun i ↦ osLd (1 + i) 10 (5 + i)) ++
        [Stmt.call (dqwName d cd) [.n 0, .n 6, .n 7, .n 8] []] ++ osLoopCall loop 1 S [10, 6, 7, 8] 11 ++
        [osCst 16 (gw (S * 5)), osMul 17 10 16] ++
        ((List.range 5).map fun i ↦ osLd (18 + i) 17 i) ++
        ((List.range 5).map fun i ↦ osCp (23 + i) (18 + i))) ++
      [.ret ((List.range 5).map fun i ↦ .n (23 + i))] := by
  simp only [lpBody, List.append_assoc]

theorem lpBodyA_flat (S d cd : ℕ) (loop : String) :
    (osHeap ((S + 1) * 5) 9 ++ ((List.range 5).map fun i ↦ osLd (1 + i) 10 (5 + i)) ++
        [Stmt.call (dqwName d cd) [.n 0, .n 6, .n 7, .n 8] []] ++ osLoopCall loop 1 S [10, 6, 7, 8] 11 ++
        [osCst 16 (gw (S * 5)), osMul 17 10 16] ++
        ((List.range 5).map fun i ↦ osLd (18 + i) 17 i) ++
        ((List.range 5).map fun i ↦ osCp (23 + i) (18 + i))).all Stmt.flat = true := by
  simp [osHeap, osLoopCall, Stmt.flat, List.range_succ]

/-- **`level_positions`, soundly**: a call of a specialization whose body is `lpBody S d cd loop`
and whose loop is `lpLoopBody d cd loop`, on a memory image whose window tables are at the
argument `tabs`, establishes `MeaningLevelPositions`. -/
theorem lp_sound {name loop : String} {S d cd : ℕ}
    (hf : FnIs name (osParams 9) (lpBody S d cd loop))
    (hl : FnIs loop (osParams 6) (lpLoopBody d cd loop))
    (hpw : digitsVal (osPowDigits (128 / d)) 1 = 128 / d)
    (hS : 1 ≤ S) (hSo : S < ordG) (hS5 : S * 5 < u128Bound)
    (hdec : ∀ a r, WinTabs rd (a.getD 3 0) → coreProgram.Rel rd (dqwName d cd) a r →
      MeaningDecodeQueryWindows d cd rd a r)
    {args rets : List E} (hwt : WinTabs rd (args.getD 8 0))
    (hrel : coreProgram.Rel rd name args rets) : MeaningLevelPositions S d cd rd args rets := by
  obtain ⟨fn, hfind, hps, hb⟩ := hf
  obtain ⟨fn', hf', σ, hp, hh⟩ := (rel_iff coreProgram _ _ _).mp hrel
  rw [hfind] at hf'
  cases hf'
  rw [hb, lpBody_split, holdsList_flat_ret _ (lpBodyA_flat S d cd loop)] at hh
  obtain ⟨hok, hret⟩ := hh
  rw [hps] at hp
  have ha : ∀ i < 9, σ (.n i) = args.getD i 0 := by
    intro i hi
    rw [← hp]
    simp [osParams, List.getD_eq_getElem?_getD, hi]
  simp only [allOk_append, and_assoc] at hok
  obtain ⟨-, hst, hdc, hlp, e16, hlast, hcp⟩ := hok
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_copy, osLd,
    osCp] at hst hlast hcp
  obtain ⟨l0, l1, l2, l3, l4⟩ := hst
  obtain ⟨m0, m1, m2, m3, m4⟩ := hlast
  obtain ⟨c0, c1, c2, c3, c4⟩ := hcp
  set cap := [σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5)] with hcapd
  have hcapA : (args.drop 1).take 5 = cap := by
    rw [hcapd, ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
      ha 5 (by decide), ← hp]
    simp [osParams, List.range_succ]
  have hwt' : WinTabs rd (σ (.n 8)) := by rw [ha 8 (by decide)]; exact hwt
  -- the first word
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_call, List.map_cons, List.map_nil] at hdc
  have hD0 := hdec _ _ (by simpa using hwt') hdc
  -- the loop
  simp only [osLoopCall, allOk_cons, allOk_nil, and_true, holds_const, holds_add, osCst, osAdd,
    StmtOk, List.map_cons, List.map_nil] at hlp
  obtain ⟨g1, gS, gsum, g3, g4, -, hcall⟩ := hlp
  have hg1 : gw 1 = gen ^ 1 := gw_eq (by decide)
  have hgS : gw S = gen ^ S := gw_eq (lt_trans (by omega) hS5)
  have h0 : ∀ i < 5, LoadHolds rd (σ (.n 10)) (5 * 1 + i) (cap.getD i 0) := by
    intro i hi
    interval_cases i
    exacts [l0, l1, l2, l3, l4]
  have hit : ∀ j, 1 ≤ j → j < 1 + (S - 1) →
      SqIter rd d cd 0 (σ (.n 10)) (σ (.n 6)) (σ (.n 7)) (σ (.n 8)) (gen ^ j) := by
    intro j h1 h2
    obtain ⟨fl, hfl, hpl, hbl⟩ := hl
    exact sqLoop_sound hfl (lpLv d cd) hpl hbl hpw (by unfold u128Bound; positivity)
      (fun a r ha hc ↦ hdec a r ha hc) (e := 1) (by omega) hSo _ _ _ _ hwt'
      (fun hne ↦ by
        have := hcall (by rw [gsum, g1, gS, hg1, hgS]; exact hne)
        rwa [g3, g4, hg1, hgS] at this) j h1 (by omega)
  obtain ⟨hrows, hdecs⟩ := sqChain cap rfl h0 hit
  -- the last capacity
  simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_mul, osCst,
    osMul] at e16
  obtain ⟨e5, e6⟩ := e16
  have hS5' : gw (S * 5) = gen ^ (S * 5) := gw_eq hS5
  have hoff : 5 * (1 + (S - 1)) = S * 5 := by omega
  have hrowE : ∀ i < 5, LoadHolds rd (σ (.n 10)) (5 * (1 + (S - 1)) + i)
      ([σ (.n 18), σ (.n 19), σ (.n 20), σ (.n 21), σ (.n 22)].getD i 0) := by
    intro i hi
    rw [hoff, ← loadHolds_mul_gen_pow, ← hS5', ← e5, ← e6]
    interval_cases i
    exacts [m0, m1, m2, m3, m4]
  have hcl : ((⟨cap, []⟩ : Fs).squeezeN (S - 1)).2.cap.length = 5 := by
    rcases h : S - 1 with _ | n
    · rfl
    · rw [squeezeN_snoc]; simp [Fs.squeeze, capOf]
  have hfin := five_eq (by rfl) hcl hrowE (hrows _ le_rfl)
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [hcapA]
    rcases j with _ | j
    · rw [← ha 0 (by decide), ← ha 6 (by decide), ← ha 7 (by decide), ← ha 8 (by decide)]
      simpa [sqSample] using hD0
    · have := hdecs j (by omega)
      rw [← ha 0 (by decide), ← ha 6 (by decide), ← ha 7 (by decide), ← ha 8 (by decide)]
      simpa [sqSample, Nat.add_comm 1 j] using this
  · rw [hcapA, ← hret, ← hfin]
    simp [List.range_succ, c0, c1, c2, c3, c4]


/-! ## The template's positions -/

/-- **A level's positions, soundly**: the level's slots of `query_positions` and `query_win_ptrs`
materialized and the dispatch on the rate into `level_positions` (whose calls of `C` give
`MeaningLevelPositions` at the rate's row `lv`), from the capacity `cap` the guest carries and the
query grind's challenge `w0`. -/
theorem osPositions_sound {C : CallRel} {σ : Val} {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt}
    (hlp : ∀ a r, WinTabs rd (a.getD 8 0) → C (osPositionsName lv) a r →
      MeaningLevelPositions lv.squeezes lv.depth lv.capDepth rd a r)
    (hr : LvRate σ c lvl lv) (hwt : WinTabs rd (σ (.n osTabs))) (hpo : lv.posOff < u128Bound)
    (hm : MatsOk σ st.mats) (hfs : st.fs.length = 5) {cap : List E} (hF : st.F σ = ⟨cap, []⟩)
    {w0 : E} (hw0 : σ (.n st.word0) = w0) (hok : AllOk C rd σ (osPositions c lvl lv st).1) :
    SqOut rd σ lv st (osPositions c lvl lv st).2 w0 cap := by
  unfold osPositions at hok ⊢
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at hok
  obtain ⟨⟨hqp, hwp⟩, hd⟩ := hok
  obtain ⟨eqp, hmq⟩ := osMatS_val' hqp hm hpo
  obtain ⟨ewp, hmw⟩ := osMatS_val' hwp hmq hpo
  have hcap : cap = st.fs.map fun i ↦ σ (.n i) := by
    have := congrArg Fs.cap hF; simpa [OsSt.F] using this.symm
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hfs
  have hc := hlp _ _ (by simpa [hf] using hwt) (dispatch_rate hr osPositionsName hd)
  obtain ⟨hdec, hret⟩ := hc
  have hargs : ((((st.word0 :: st.fs ++ [(osMatS c.plan osQpos lv.posOff st).2.1,
      (osMatS c.plan osQbp lv.posOff (osMatS c.plan osQpos lv.posOff st).2.2).2.1, osTabs]).map
        V.n).map σ).drop 1).take 5 = cap := by
    rw [hcap, hf]; simp
  rw [hargs] at hdec hret
  dsimp only
  refine ⟨fun j hj ↦ ?_, ?_, by simp, hmw, rfl, rfl, rfl, rfl⟩
  · have := hdec j hj
    simp only [List.map_cons, List.map_append, List.map_nil, hw0, hf] at this
    simpa [eqp, ewp, mul_assoc, ← pow_add] using this
  · simp only [OsSt.F]
    refine (fs_mk_eq ?_ (squeezeN_pend rfl _)).symm
    rw [← hret]
    simp [osRun, List.range_succ]

end
end LeanVM.Guest.B1.Whir
