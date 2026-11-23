/-
  LeanVM.Guest.B1.Whir.CHonBodyRun1

  open_stacked's body on an accepting run: the run's honest data has the body's facts.
-/

module

public import LeanVM.Guest.B1.Whir.CHonBodyRun0
public import LeanVM.Guest.B1.Whir.CHonBodyRun
public import LeanVM.Guest.B1.Whir.CHonAllocAll
public import LeanVM.Guest.B1.Whir.CHonStaticAll
public import LeanVM.Guest.B1.Whir.CHonNamesAll

/-!
# The body on a run

`HonRun.bodyFacts`: the run's honest data (`hdOf`) has `BodyFacts` at the arm's arguments, the
rate's selector `rateSel r` first, the configuration's facts decided (`*_all`), every other fact
from the run (`Whir/CHonBodyRun0`, `CHonFinRun`, `CHonRes`). `HonRun.body_run`: the body on the
run (`body_gen`), its calls' values fixed before the memory (`Stmt.callVarsS` is `callVs`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

theorem callVarsS_eq : Stmt.callVarsS = callVs := by
  funext s
  cases s <;> rfl

/-- **Every load of the body reads a word the caller's memory facts fix**, from its loads holding on
every memory with those facts. -/
theorem osLoadsIn_of {c : OsCfg} {b : ℕ} {own : List (List E)} {cur tabs : E} {xs : List E} {σ : Val}
    (h : LoadsIn (OsM c b own cur tabs xs) (osBodyA c) σ) : OsLoadsIn c b own cur tabs xs σ := by
  intro q hq
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp hq
  match s, he with
  | .atom (.load d p off), he =>
    simp only [B1.Stmt.loadS, Option.some.injEq] at he
    subst he
    exact ⟨σ d, fun rd' h1 h2 h3 ↦ h rd' ⟨h1, h2, h3, fun _ _ _ _ _ _ _ ↦ trivial, fun _ _ _ _ ↦ trivial⟩
      (d, p, off) (List.mem_filterMap.mpr ⟨_, hs, rfl⟩)⟩

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **The run's honest data has the body's facts.** -/
theorem bodyFacts (cur tabs : E) :
    BodyFacts (hdOf μ r Ls)
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs]) xs
      ((cfg.head?.map (·.fold)).getD 0) w := by
  have hy := hR.yr
  have hm : μ - minOpenLog < 11 := hR.m11
  have hr4 : r - 1 < 4 := hR.r4
  refine ⟨⟨bodyStatic_all _ _ hm hr4, honStatic_all _ _ hm hr4, honNames_all _ _ hm hr4, hR.len,
    fun l hl ↦ hR.step hl, fun l hl ↦ hR.mid hl, hR.last, hR.fin, hR.alphas, fun l hl ↦ (hR.recs l hl).1,
    fun l hl ↦ lvsAt_suffix hR.run l (by rw [hR.len]; exact hl), hR.br_cap5, fun l hl ↦ hR.br_rootN hl,
    hR.br_G, hR.br_rl, fun l hl ↦ (hR.recRun_run l hl).z0, hR.br_lane⟩,
    hR.br_tsuf, hR.br_pl, br_f3, hR.finStatic_run, hR.recRun_run, hR.hylen, hR.hfold, hR.hffm,
    hR.fld_resEq, hR.fld_slowEq, ?_, ?_, ?_, ?_, fun l _ ↦ ?_, ?_⟩
  · rw [OsHD.capAt_of _ (Nat.zero_le _)]
    show _ = (Ls.getD 0 default).cap
    rw [hR.start.2.1]
    rfl
  · rw [OsHD.claimAt_of _ (Nat.zero_le _)]
    show _ = (Ls.getD 0 default).s.claim + recsDeficit (lvsRecs μ Ls 0) (Ls.getD 0 default).s.alphas
    rw [hR.start.1]
    simp only [lvsRecs, List.take_zero, List.map_nil, recsDeficit, List.sum_nil, add_zero]
    rfl
  · rw [OsHD.xsAt_of _ (Nat.zero_le _)]
    show (Ls.getD 0 default).xs.length = _
    rw [hR.start.2.2.2]
  · show _ = digestHalves ((Ls.getD 0 default).R.getD 0 default).1
    rw [hR.start.2.2.1]
    rfl
  · refine ⟨r - 1, hr4, rfl, osCfgR_lvAt_length _ _ l, osCfgR_lvAt_getD l hr4⟩
  · refine ⟨r - 1, hr4, by show rateSel r = _; rw [rateSel, gen_pow_eq_ofK], ?_⟩
    refine (honStatic_all _ _ hm hr4).posTot hr4 ?_
    simp only [osCfgR, OsCfg.withLevels, osCfg]
    rw [List.getD_eq_getElem _ _ (by simpa using hr4)]
    simp only [List.getElem_map, List.getElem_range]

/-- **The body on the run**, its calls' values fixed before the memory. -/
theorem body_run {cur tabs : E} (b : ℕ) : ∃ CV : List (List E), ∀ (rd0 : Reader), LowDef 11 rd0 →
    ∃ (kEnd : ℕ) (f : ℕ → E), ∀ (C : CallRel) (rd : Reader),
      OsHA C rd (osCfgR (μ - minOpenLog) (r - 1)) b (hdOf μ r Ls).own cur tabs xs → LowAgree rd rd0 →
      BlkF C rd (Val.ofArgs (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2,
          cur, tabs]))
        11 kEnd f (osBodyA (osCfgR (μ - minOpenLog) (r - 1)))
        (fun σ' ↦ OsOutA (osCfgR (μ - minOpenLog) (r - 1)) b tabs
          ((hdOf μ r Ls).tr.2.1 + (hdOf μ r Ls).T.prod * recsDeficit (hdOf μ r Ls).recs (hdOf μ r Ls).G)
          (((hdOf μ r Ls).recs.flatMap recGlued).foldl
            (fun w g ↦ w + g.scalar * g.weightAt (((hdOf μ r Ls).G ++ (hdOf μ r Ls).T).drop g.foldStart)) 0)
          (multilinearEval ((hdOf μ r Ls).Lf.fw.fold.take (osCfgR (μ - minOpenLog) (r - 1)).yrLen)
            (hdOf μ r Ls).T)
          (hdOf μ r Ls).own (hdOf μ r Ls).D σ' ∧
          ((osBodyA (osCfgR (μ - minOpenLog) (r - 1))).filterMap Stmt.callVarsS).map (·.map σ') = CV ∧
          OsLoadsIn (osCfgR (μ - minOpenLog) (r - 1)) b (hdOf μ r Ls).own cur tabs xs σ' ∧
          WinEx (osBodyA (osCfgR (μ - minOpenLog) (r - 1))) σ') := by
  refine ⟨(hdOf μ r Ls).cvBody b tabs cur xs
    (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs]), fun rd0 hl0 ↦ ?_⟩
  obtain ⟨kEnd, f, hf⟩ := body_gen (hR.bodyFacts cur tabs) rfl rfl b rd0 hl0
  refine ⟨kEnd, f, fun C rd hH hag ↦ (hf C rd hH hag).mono fun σ' ⟨o, cv, ld, wx⟩ ↦ ⟨o, ?_, osLoadsIn_of ld, wx⟩⟩
  rw [callVarsS_eq]
  exact cv

end HonRun

end
end LeanVM.Guest.B1.Whir
