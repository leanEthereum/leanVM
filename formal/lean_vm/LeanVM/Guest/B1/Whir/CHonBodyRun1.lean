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
run (`body_gen`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

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
    hR.fld_resEq, ?_, ?_, ?_, ?_, fun l _ ↦ ?_⟩
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

/-- **The body on the run.** -/
theorem body_run {cur tabs : E} (b : ℕ) :
    ∃ (kEnd : ℕ) (f : ℕ → E), ∀ (C : CallRel) (rd : Reader),
      OsHA C rd (osCfgR (μ - minOpenLog) (r - 1)) b (hdOf μ r Ls).own cur tabs xs →
      BlkF C rd (Val.ofArgs (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2,
          cur, tabs]))
        11 kEnd f (osBodyA (osCfgR (μ - minOpenLog) (r - 1)))
        (OsOutA (osCfgR (μ - minOpenLog) (r - 1)) b tabs
          ((hdOf μ r Ls).tr.2.1 + (hdOf μ r Ls).T.prod * recsDeficit (hdOf μ r Ls).recs (hdOf μ r Ls).G)
          (((hdOf μ r Ls).recs.flatMap recGlued).foldl
            (fun w g ↦ w + g.scalar * g.weightAt (((hdOf μ r Ls).G ++ (hdOf μ r Ls).T).drop g.foldStart)) 0)
          (multilinearEval ((hdOf μ r Ls).Lf.fw.fold.take (osCfgR (μ - minOpenLog) (r - 1)).yrLen)
            (hdOf μ r Ls).T)
          (hdOf μ r Ls).own (hdOf μ r Ls).D) :=
  body_gen (hR.bodyFacts cur tabs) rfl rfl b

end HonRun

end
end LeanVM.Guest.B1.Whir
