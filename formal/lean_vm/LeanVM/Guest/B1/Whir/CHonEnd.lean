/-
  LeanVM.Guest.B1.Whir.CHonEnd

  The stacked opening's terminal on an accepting run, in the honest data's terms.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFinRun

/-!
# The terminal at the honest data

On `hR : HonRun μ r … w cfg Ls`, at `h := hdOf μ r Ls`: the run's terminal `w` is the guest's
(`finEnd_w` at the final level): its target the closing claim plus the deficit times the tail
challenges (`target_eq`), its inner sum the glued claims' weights (`inner_eq`), its residual the
final lane at the tail challenges (`residual_eq`), its point the rotated challenges (`point_eq`);
`μ` is the folds and the closing rounds (`mu_eq`).
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

/-- `μ` is the folds and the closing rounds. -/
theorem mu_eq : μ = (osCfg (candidate μ r)).nFolds + (osCfg (candidate μ r)).yrLog := hR.cand.1.symm

/-- **The terminal, in the honest data's terms.** -/
theorem end_eq :
    w.target = (hdOf μ r Ls).tr.2.1 + (hdOf μ r Ls).T.prod * recsDeficit (hdOf μ r Ls).recs (hdOf μ r Ls).G ∧
    w.inner = ((hdOf μ r Ls).recs.flatMap recGlued).foldl
      (fun x g ↦ x + g.scalar * g.weightAt (((hdOf μ r Ls).G ++ (hdOf μ r Ls).T).drop g.foldStart)) 0 ∧
    w.residual = multilinearEval ((hdOf μ r Ls).Lf.fw.fold.take (hdOf μ r Ls).c.yrLen) (hdOf μ r Ls).T ∧
    w.point = rotPt (hdOf μ r Ls).G (hdOf μ r Ls).T ((osCfg (candidate μ r)).levels.headD default).folds := by
  have hy := hR.yr
  obtain ⟨cF, -, -, clane, -, -, cyl, cylen, -⟩ := hR.cand
  obtain ⟨-, hfold, hlog, -, hdepth, hqueries, -, -, -, hsq, -⟩ := hR.fin
  obtain ⟨hrecF, hglued⟩ := hR.recs (osCfg (candidate μ r)).yrLevel (by omega)
  have hs1 := hR.fin_s1
  set Lf := Ls.getD (osCfg (candidate μ r)).yrLevel default with hLf
  set lv := osLvAt (osCfg (candidate μ r)) (osCfg (candidate μ r)).yrLevel with hlv
  have hmu : Lf.mu μ = (osCfg (candidate μ r)).yrLog := by
    show μ - Lf.s1.alphas.length = _; rw [hs1]; omega
  have hdep : lv.depth = Lf.dp μ := by rw [hdepth]; show _ = Lf.mu μ + _; rw [hmu]
  have hF := hR.last
  rw [clane] at hF
  have E := finEqs hF hfold hdep hqueries hsq 0 0 0 0 0 (Lf.gcl (lvsRecs μ Ls (osCfg (candidate μ r)).yrLevel))
  obtain ⟨e1, e2, e3, e4, -⟩ := finEnd_w hF hfold hdep hqueries hsq hrecF hglued 0 0 0 0 0
  have htr : tailRun Lf.fw.pairs ((Lf.finWD 0 0 0 0 0).cap3 lv Lf.cap (Lf.gcl (lvsRecs μ Ls (osCfg (candidate μ r)).yrLevel)))
      ((Lf.finWD 0 0 0 0 0).cl1 lv Lf.cap (Lf.gcl (lvsRecs μ Ls (osCfg (candidate μ r)).yrLevel))) =
      (hdOf μ r Ls).tr := by
    rw [E.cap3]; rfl
  rw [htr] at e1 e2 e3 e4
  refine ⟨e1, e2, ?_, e4⟩
  rw [e3, hmu, cylen]
  rfl

theorem target_eq :
    w.target = (hdOf μ r Ls).tr.2.1 + (hdOf μ r Ls).T.prod * recsDeficit (hdOf μ r Ls).recs (hdOf μ r Ls).G :=
  hR.end_eq.1

theorem inner_eq :
    w.inner = ((hdOf μ r Ls).recs.flatMap recGlued).foldl
      (fun x g ↦ x + g.scalar * g.weightAt (((hdOf μ r Ls).G ++ (hdOf μ r Ls).T).drop g.foldStart)) 0 :=
  hR.end_eq.2.1

theorem residual_eq :
    w.residual = multilinearEval ((hdOf μ r Ls).Lf.fw.fold.take (hdOf μ r Ls).c.yrLen) (hdOf μ r Ls).T :=
  hR.end_eq.2.2.1

theorem point_eq :
    w.point = rotPt (hdOf μ r Ls).G (hdOf μ r Ls).T ((osCfg (candidate μ r)).levels.headD default).folds :=
  hR.end_eq.2.2.2

end HonRun

end
end LeanVM.Guest.B1.Whir
