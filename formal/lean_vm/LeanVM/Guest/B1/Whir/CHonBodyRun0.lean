/-
  LeanVM.Guest.B1.Whir.CHonBodyRun0

  The run's facts the body's completeness takes, level by level.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFinRun
public import LeanVM.Guest.B1.Whir.CHonFields0

/-!
# The run's facts for the body

On an accepting run's honest data (`HonRun`): each level's carried capacity has five cells, its
roots one entry a level before it (`br_Rlen`), its root's height its row's depth (`br_ht`), the
next root the message's cells (`br_rootN`), the final level's challenges extend each level's
(`br_G`), its rounds counted by its row (`br_rl`), its positions below the depth (`br_ps`), some
(`br_q0`), its openings agreeing (`br_ag`); the final lane's length, the closing rounds' words and
count, the capacity after the positions' squeezes.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

theorem br_cap5 : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length, (Ls.getD l default).cap.length = 5
  | 0, _ => by rw [hR.start.2.1]; rfl
  | l + 1, hl => by
    have hy := hR.yr
    obtain ⟨rw, W, -, -, -, -, -, -, -, hc, -⟩ := hR.step (l := l) (by omega)
    rw [hc]; rfl

theorem br_Rlen : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length, (Ls.getD l default).R.length = l + 1
  | 0, _ => by rw [hR.start.2.2.1]; rfl
  | l + 1, hl => by
    have hy := hR.yr
    obtain ⟨rw, W, -, -, -, -, -, -, -, -, hRR⟩ := hR.step (l := l) (by omega)
    rw [hRR, NextW.roots, List.length_append, br_Rlen l (by omega)]
    rfl

/-- The next level's root entry. -/
theorem br_Rnext {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel) :
    ∃ (rw : List E) (W : NextW), (Ls.getD l default).d = .next rw W ∧
      (Ls.getD (l + 1) default).R.getD (l + 1) default =
        (digestFromHalves (W.x0, W.x1), levelShape (μ - (Ls.getD l default).s1.alphas.length)
          (Ls.getD (l + 1) default).level (2 * 2 ^ (Ls.getD (l + 1) default).level.fold)) := by
  have hy := hR.yr
  obtain ⟨rw, W, hd, -, -, -, -, -, -, -, hRR⟩ := hR.step hl
  have hrw : (Ls.getD l default).rw = rw := by unfold LvAt.rw; rw [hd]
  refine ⟨rw, W, hd, ?_⟩
  rw [hRR, NextW.roots, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by rw [br_Rlen hR l (by omega)]), br_Rlen hR l (by omega), Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some, LvAt.s1, hrw]

theorem br_rootN {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel) :
    digestHalves ((hdOf μ r Ls).root (l + 1)) =
      (((hdOf μ r Ls).L l).nw.x0, ((hdOf μ r Ls).L l).nw.x1) := by
  obtain ⟨rw, W, hd, he⟩ := hR.br_Rnext hl
  show digestHalves ((Ls.getD (l + 1) default).R.getD (l + 1) default).1 =
    ((Ls.getD l default).nw.x0, (Ls.getD l default).nw.x1)
  rw [he]
  have hnw : (Ls.getD l default).nw = W := by unfold LvAt.nw; rw [hd]
  rw [hnw]
  exact digestScalars_digestOfScalars _

/-- A level's `μ` and depth against its row. -/
theorem br_dep {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth = (Ls.getD l default).dp μ ∧
      (Ls.getD l default).level.fold = (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).folds ∧
      (Ls.getD l default).level.queries = (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).queries ∧
      0 < (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).queries := by
  have hy := hR.yr
  have hg := hR.alphas l hl
  by_cases hf : l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel
  · subst hf
    obtain ⟨-, hfold, hlog, -, hdepth, hqueries, hq0, -⟩ := hR.fin
    refine ⟨?_, hfold, hqueries, hq0⟩
    rw [hdepth]
    show _ = μ - (Ls.getD _ default).s1.alphas.length + _
    rw [LvAt.s1, roundsSpec_alphas_length, hg, hfold, hlog]
  · obtain ⟨-, hfold, hcols, -, hdepth, hqueries, hq0, -⟩ := hR.mid (l := l) (by omega)
    refine ⟨?_, hfold, hqueries, hq0⟩
    rw [hdepth]
    show _ = μ - (Ls.getD l default).s1.alphas.length + _
    rw [LvAt.s1, roundsSpec_alphas_length, hg, hfold, hcols]

theorem br_ht : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    ((Ls.getD l default).R.getD l default).2.1 = (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth
  | 0, hl => by
    rw [hR.start.2.2.1]
    have hs := hR.cand.2.1
    show (stackShape μ r).1 = _
    rw [hs]
    simp [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getD_eq_getElem?_getD]
  | l + 1, hl => by
    have hy := hR.yr
    obtain ⟨rw, W, hd, he⟩ := hR.br_Rnext (l := l) (by omega)
    obtain ⟨-, hfold, hcols, -⟩ := hR.mid (l := l) (by omega)
    have hshape := (hR.mid (l := l) (by omega)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [he]
    show (levelShape (μ - (Ls.getD l default).s1.alphas.length) _ _).1 = _
    rw [LvAt.s1, roundsSpec_alphas_length, hR.alphas l (by omega), hfold, hcols, hshape]

theorem br_rl : ∀ i < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    (Ls.getD i default).rounds.length = (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD i default)).folds := by
  intro i hi
  rw [LvAt.rounds, rsRounds, roundsSpec_rounds_length]
  exact (hR.br_dep hi).2.1

/-- **Each level's challenges begin the final level's.** -/
theorem br_prefix : ∀ d l, l + d = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel →
    (Ls.getD l default).s1.alphas <+: (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).s1.alphas
  | 0, l, h => by rw [Nat.add_zero] at h; subst h; exact List.prefix_refl _
  | d + 1, l, h => by
    have ih := br_prefix d (l + 1) (by omega)
    have e := (hR.stepS (l := l) (by omega)).1
    obtain ⟨gs, hg, -⟩ := roundsSpec_alphas (Ls.getD (l + 1) default).level.fold (Ls.getD (l + 1) default).s
      (Ls.getD (l + 1) default).cap (Ls.getD (l + 1) default).rw
    refine List.IsPrefix.trans ?_ ih
    rw [LvAt.s1, rsSt, hg, e]
    exact List.prefix_append _ _

theorem br_G : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length, ∀ j < (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).folds,
    (hdOf μ r Ls).G.getD ((((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).foldsOff + j) 0 =
      (roundsSpec (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).folds (Ls.getD l default).s (Ls.getD l default).cap
        (Ls.getD l default).rw).1.alphas.getD ((Ls.getD l default).s.alphas.length + j) 0 := by
  intro l hl j hj
  have hy := hR.yr
  have hfold := (hR.br_dep hl).2.1
  have hp := hR.br_prefix ((osCfgR (μ - minOpenLog) (r - 1)).yrLevel - l) l (by omega)
  have hlen : (Ls.getD l default).s1.alphas.length = (Ls.getD l default).s.alphas.length +
      (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).folds := by
    rw [LvAt.s1, roundsSpec_alphas_length, hfold]
  have e1 : (Ls.getD l default).s1 =
      (roundsSpec (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).folds (Ls.getD l default).s (Ls.getD l default).cap
        (Ls.getD l default).rw).1 := by rw [LvAt.s1, rsSt, hfold]
  rw [← e1, ← hR.alphas l hl]
  show (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).s1.alphas.getD _ 0 = _
  obtain ⟨t, ht⟩ := hp
  rw [← ht, List.getD_append _ _ _ _ (by omega)]

theorem br_ps : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length, ∀ q ∈ (Ls.getD l default).qs μ,
    q < 2 ^ (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth := by
  intro l hl q hq
  rw [LvAt.qs_eq_sq, sqPositions, List.mem_map] at hq
  obtain ⟨k, -, rfl⟩ := hq
  rw [(hR.br_dep hl).1, qwPosOf]
  exact Nat.mod_lt _ (by positivity)

theorem br_q0 : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length, 0 < ((Ls.getD l default).qs μ).length := by
  intro l hl
  rw [LvAt.qs_length, (hR.br_dep hl).2.2.1]
  exact (hR.br_dep hl).2.2.2

theorem br_ag : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    Guest.Limits.OpeningsAgree (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth
      (((Ls.getD l default).qs μ).zip (Ls.getD l default).phase) := by
  intro l hl
  have hRl := hR.br_Rlen l hl
  have hget : (Ls.getD l default).R[l]? = some (((Ls.getD l default).R.getD l default).1,
      ((Ls.getD l default).R.getD l default).2.1, ((Ls.getD l default).R.getD l default).2.2) := by
    rw [List.getD_eq_getElem (Ls.getD l default).R default (by omega), List.getElem?_eq_getElem (by omega)]
  have := hR.agree l (by rw [hR.len]; exact hl) _ _ _ hget
  rwa [hR.br_ht l hl] at this

/-! ## The final level -/

theorem br_lane : (hdOf μ r Ls).Lf.fw.fold.length =
    (osCfgR (μ - minOpenLog) (r - 1)).yrLen + ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).folds := by
  obtain ⟨cF, -, -, -, -, -, cyl, cylen, -⟩ := hR.cand
  obtain ⟨rw, W, hd, -, -, -, -, hok, -⟩ := hR.last
  obtain ⟨-, ffold, -⟩ := hR.fin
  have hrw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).rw = rw := by unfold LvAt.rw; rw [hd]
  have hfw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw = W := by unfold LvAt.fw; rw [hd]
  rw [← hrw] at hok
  show (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw.fold.length = _
  rw [hfw, hok.flen]
  show 2 ^ (μ - (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).s1.alphas.length) + _ = _
  rw [hR.fin_s1, show μ - (osCfgR (μ - minOpenLog) (r - 1)).nFolds = (osCfgR (μ - minOpenLog) (r - 1)).yrLog by omega, cylen,
    ffold]

theorem br_pl : (hdOf μ r Ls).Lf.fw.pairs.length = (osCfgR (μ - minOpenLog) (r - 1)).yrLog := by
  obtain ⟨cF, -⟩ := hR.cand
  obtain ⟨rw, W, hd, -, -, -, -, hok, -⟩ := hR.last
  have hrw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).rw = rw := by unfold LvAt.rw; rw [hd]
  have hfw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw = W := by unfold LvAt.fw; rw [hd]
  rw [← hrw] at hok
  show (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw.pairs.length = _
  rw [hfw, hok.plen2]
  show μ - (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).s1.alphas.length = _
  rw [hR.fin_s1]; omega

theorem br_tsuf : tailWords (hdOf μ r Ls).Lf.fw.pairs <:+ xs := by
  have hy := hR.yr
  obtain ⟨rw, W, hd, -, -, hxs, -⟩ := hR.last
  have hfw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw = W := by unfold LvAt.fw; rw [hd]
  obtain ⟨p, hp⟩ := lvsAt_suffix hR.run (osCfgR (μ - minOpenLog) (r - 1)).yrLevel (by rw [hR.len]; omega)
  show tailWords (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).fw.pairs <:+ xs
  rw [hfw]
  refine ⟨p ++ rw ++ W.fold ++ [W.nn], ?_⟩
  rw [hp, hxs]
  simp [FinW.words]

omit hR in
theorem br_f3 : ((hdOf μ r Ls).Lf.F3 (hdOf μ r Ls).logN).cap.length = 5 := by
  show ((Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).F3 μ).cap.length = 5
  unfold LvAt.F3
  split <;> exact squeezeN_cap_length _ _ rfl

end HonRun

end
end LeanVM.Guest.B1.Whir
