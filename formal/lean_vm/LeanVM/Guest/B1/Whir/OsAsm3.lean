/-
  LeanVM.Guest.B1.Whir.OsAsm3

  `open_stacked`'s body in its parts, and the tail of a run of the stacked opening.
-/

module

public import LeanVM.Guest.B1.Whir.OsAsm2
public import LeanVM.Guest.B1.Whir.OsCfgFacts

/-!
# The body's parts and the run's tail (TRIAGE #36)

`os_pre_eq`: the body's statements before its return are the head's, the levels', the tail's and
the finish's before its return; the head sets up no frame. `os_tail_data`: a run's tail is its
fold rounds from the state after the levels, its end the rotated challenges, the glued weight, the
residual's value and the final claim.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The finish before its return. -/
def osFinPre (cfg : OsCfg) : List Stmt := (osFinish cfg (OsRun.sT cfg) (OsRun.tch cfg)).dropLast

theorem osFinish_ne (cfg : OsCfg) (st : OsSt) (tch : ℕ) : osFinish cfg st tch ≠ [] := by
  unfold osFinish; simp

/-- **The body's statements before its return.** -/
theorem os_pre_eq (cfg : OsCfg) : (osBody cfg).dropLast =
    (osHead cfg).1 ++ (osLevels cfg 0 cfg.levels (osHead cfg).2).1 ++ (osTail cfg.yrLog (OsRun.sL cfg)).1 ++
      osFinPre cfg := by
  unfold osBody osFinPre
  rw [List.dropLast_append_of_ne_nil (osFinish_ne _ _ _)]
  rfl

theorem os_finish_eq {cfg : OsCfg} (hbf : OsBodyFacts cfg) :
    osFinish cfg (OsRun.sT cfg) (OsRun.tch cfg) = osFinPre cfg ++ [.ret (osRetVs cfg)] := by
  have h := hbf.last
  rw [os_pre_eq] at h
  have e : osBody cfg = ((osHead cfg).1 ++ (osLevels cfg 0 cfg.levels (osHead cfg).2).1 ++
      (osTail cfg.yrLog (OsRun.sL cfg)).1) ++ osFinish cfg (OsRun.sT cfg) (OsRun.tch cfg) := rfl
  rw [e, List.append_assoc _ (osFinPre cfg)] at h
  exact List.append_cancel_left h

theorem os_head_noCalls (cfg : OsCfg) : (osHead cfg).1.filterMap Main.Stmt.callS = [] := by
  unfold osHead osHeap osFsNext fsNextT fsCompressT
  simp [Main.Stmt.callS]

theorem os_one_add_gw {m : ℕ} (h0 : 0 < m) (hm : m < 2 ^ 62) : 1 + osGw m ≠ 0 := by
  rw [os_gw_eq (by omega)]
  intro h
  have h1 : gen ^ m = gen ^ 0 := by rw [pow_zero]; exact (e_add_eq_zero_iff.mp h).symm
  have := gen_pow_inj (show m < ordG by simp only [ordG]; omega) (by norm_num) h1
  omega

/-- **The tail of a run**, from the levels' data. -/
theorem os_tail_data {cfg : OsCfg} {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {xs : List E}
    {cv0 : Digest} {w0 : WhirState} {os : List Opening} {roots : List (Digest × ℕ × ℕ)} {Hs : List OsLvH}
    {e : WhirEnd} {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} (hHl : Hs.length = cfg.levels.length)
    (hch : OsChain cfg μ (cfg.lv 0).folds xs Lall e sp' Q 0 cv0 2 w0 os roots Hs) :
    ∃ (w1 : WhirState) (chs : List E) (cv1 : Digest) (ospT : List Opening) (rootsT : List (Digest × ℕ × ℕ)),
      Runs (foldRounds (cfg.yrLog - 1) ⟨(osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.2.target,
          (osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.2.quad, [], []⟩ [])
        ⟨(osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).1, xs.drop (osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.1, ospT, rootsT⟩
        (w1, chs) ⟨cv1, xs.drop ((osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.1 + 2 * (cfg.yrLog - 1)), ospT, rootsT⟩ ∧
      chs.length = cfg.yrLog - 1 ∧
      e = ⟨((osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.2.folds ++ (chs ++ [challengeOf (sqCv cv1)])).drop (cfg.lv 0).folds ++
          ((osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.2.folds ++ (chs ++ [challengeOf (sqCv cv1)])).take (cfg.lv 0).folds,
        (osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.2.glued.foldl (fun w c ↦ w + c.scalar * c.weightAt
          ((osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.2.folds.drop c.foldStart ++ (chs ++ [challengeOf (sqCv cv1)]))) 0,
        multilinearEval (osHMs cfg cfg.yrLevel xs ((osLvsList cfg xs 0 cv0 2 w0 os roots Hs).getD cfg.yrLevel default).p)
          (chs ++ [challengeOf (sqCv cv1)]),
        polyEval w1.quad (challengeOf (sqCv cv1))⟩ := by
  have hn := hok.len2
  have hne : Hs ≠ [] := by intro h; rw [h] at hHl; simp at hHl; omega
  have ht := os_chain_tail Hs 0 _ _ _ _ _ hch
  rw [os_lvsLast_eq cfg xs Hs 0 cv0 2 w0 os roots hne] at ht
  set Ls := osLvsList cfg xs 0 cv0 2 w0 os roots Hs
  have hLl : Ls.length = cfg.levels.length := by rw [os_lvsList_length, hHl]
  have hlast : Ls.getLastD default = Ls.getD cfg.yrLevel default := by
    rw [hok.yrLevel, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hLl, List.getD_eq_getElem?_getD]
  have hlv : (Ls.getD cfg.yrLevel default).lvl = cfg.yrLevel := by
    rw [List.getD_eq_getElem _ _ (by rw [hLl, hok.yrLevel]; omega)]
    have := os_lvsList_lvl cfg xs Hs 0 cv0 2 w0 os roots cfg.yrLevel (by rw [hLl, hok.yrLevel]; omega)
    simpa using this
  rw [hlast, hlv] at ht
  have hml : μ - osLevelF cfg cfg.yrLevel = cfg.yrLog := by
    rw [hok.yrLevel, hok.nFolds, ← hok.total]; omega
  rw [hml] at ht
  obtain ⟨w1, chs, st1, hr, he, -⟩ := os_tailOpen_inv (by have := hok.yr2; omega) ht
  obtain ⟨hs1, ho1, hr1, -⟩ := os_foldRounds_st hr
  obtain ⟨chs', -, hc2, hc3⟩ := os_foldRounds_folds hr
  simp only [List.nil_append] at hc2
  refine ⟨w1, chs, st1.cv, (Ls.getD cfg.yrLevel default).H.osq, (Ls.getD cfg.yrLevel default).roots, ?_,
    by rw [hc2, hc3], he⟩
  have est : st1 = ⟨st1.cv, xs.drop ((osLvsEnd cfg xs 0 cv0 2 w0 roots Hs).2.1 + 2 * (cfg.yrLog - 1)),
      (Ls.getD cfg.yrLevel default).H.osq, (Ls.getD cfg.yrLevel default).roots⟩ := by
    cases st1; simp only at hs1 ho1 hr1 ⊢; rw [hs1, ho1, hr1]
  rw [← est]; exact hr

end
end LeanVM.Guest.B1
