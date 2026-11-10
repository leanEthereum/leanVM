/-
  LeanVM.Guest.B1.Whir.CHonInv

  The honest run's levels against the candidate's rows: their Spec levels and facts, their fold
  challenges so far, their records and glued claims, their words' offsets.
-/

module

public import LeanVM.Guest.B1.Whir.CHonSetup
public import LeanVM.Guest.B1.Whir.CHonLvP

/-!
# The run's invariants

On `HonRun μ r … cfg Ls`, with `c := osCfg (candidate μ r)` and `L l := Ls.getD l default`:

* `HonRun.len`, `HonRun.level`: `Ls` has a level a row, level `l` is `cfg[l]`;
* `HonRun.mid`, `HonRun.fin`: the candidate's checked facts at each level of the run;
* `HonRun.step`, `HonRun.last`: the non-final levels' steps and the final level's end;
* `HonRun.gammas`: level `l` starts after `foldsOff` fold challenges;
* `HonRun.recs`: the records of the levels before `l` are what level `l`'s state glued, their `F`
  within its challenges;
* `HonRun.off`: each level's words' offset in the stream.
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

theorem cnt : (osCfg (candidate μ r)).levels.length = cfg.length :=
  (levelsB_at 0 _ cfg hR.cand.2.2.2.2.2.2.2.2.2.2.2.2).1

theorem len : Ls.length = (osCfg (candidate μ r)).levels.length := by
  rw [hR.run.len, hR.cnt]

theorem n2 : 2 ≤ (osCfg (candidate μ r)).levels.length := hR.cand.2.2.2.2.1

theorem yr : (osCfg (candidate μ r)).yrLevel + 1 = (osCfg (candidate μ r)).levels.length := by
  have := hR.cand.2.2.2.2.2.1; have := hR.n2; omega

theorem level {l : ℕ} (hl : l < (osCfg (candidate μ r)).levels.length) :
    cfg[l]? = some (Ls.getD l default).level :=
  hR.run.level l (by rw [hR.len]; exact hl)

/-- The checked facts at a non-final level. -/
theorem mid {l : ℕ} (hl : l < (osCfg (candidate μ r)).yrLevel) :
    MidOk (osCfg (candidate μ r)) μ l (osLvAt (osCfg (candidate μ r)) l) (Ls.getD l default).level
      (Ls.getD (l + 1) default).level (osLvAt (osCfg (candidate μ r)) (l + 1)) := by
  have hy := hR.yr
  have := (levelsB_at 0 _ cfg hR.cand.2.2.2.2.2.2.2.2.2.2.2.2).2.1 l (by omega) _ _
    (hR.level (by omega)) (hR.level (by omega))
  simpa using this

/-- The checked facts at the final level. -/
theorem fin : FinOkF (osCfg (candidate μ r)) μ (osCfg (candidate μ r)).yrLevel
    (osLvAt (osCfg (candidate μ r)) (osCfg (candidate μ r)).yrLevel)
    (Ls.getD (osCfg (candidate μ r)).yrLevel default).level := by
  have hy := hR.yr
  have e : (osCfg (candidate μ r)).levels.length - 1 = (osCfg (candidate μ r)).yrLevel := by omega
  have := (levelsB_at 0 _ cfg hR.cand.2.2.2.2.2.2.2.2.2.2.2.2).2.2 _ (by rw [e]; exact hR.level (by omega))
  rw [e, Nat.zero_add] at this
  exact this

/-- A non-final level's step. -/
theorem step {l : ℕ} (hl : l < (osCfg (candidate μ r)).yrLevel) :
    LvAt.NextStep μ l (Ls.getD l default) (Ls.getD (l + 1) default) := by
  have hy := hR.yr
  have := hR.run.next l (by rw [hR.len]; omega)
  simpa using this

/-- The final level's end. -/
theorem last : LvAt.FinStep μ ((cfg.head?.map (·.fold)).getD 0) (osCfg (candidate μ r)).yrLevel
    (Ls.getD (osCfg (candidate μ r)).yrLevel default) w := by
  have hy := hR.yr
  have := hR.run.fin (by rw [hR.len]; omega)
  rw [hR.len, show (osCfg (candidate μ r)).levels.length - 1 = (osCfg (candidate μ r)).yrLevel by omega,
    Nat.zero_add] at this
  exact this

/-- The first level's start. -/
theorem start : (Ls.getD 0 default).s = ⟨target, [], []⟩ ∧ (Ls.getD 0 default).cap = capOf S ∧
    (Ls.getD 0 default).R = [(root, stackShape μ r)] ∧ (Ls.getD 0 default).xs = xs := by
  have := hR.run.start (by rw [hR.len]; have := hR.n2; omega)
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩

theorem foldsOff0 : (osLvAt (osCfg (candidate μ r)) 0).foldsOff = 0 := by
  have h := hR.cand.2.2.1
  have hn := hR.n2
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?] at h
  simpa [osLvAt, List.getD_eq_getElem?_getD] using h

/-- The non-final level's next level starts after its folds' challenges, with its record glued. -/
theorem stepS {l : ℕ} (hl : l < (osCfg (candidate μ r)).yrLevel) :
    (Ls.getD (l + 1) default).s.gammas = (Ls.getD l default).s1.gammas ∧
    (Ls.getD (l + 1) default).s.glued = (Ls.getD l default).s.glued ++ recGlued ((Ls.getD l default).osRec μ) := by
  obtain ⟨rw, W, hd, -, -, -, -, -, hs, -, -⟩ := hR.step hl
  obtain ⟨e1, e2⟩ := NextW.glued_glued W μ l (Ls.getD l default).level (Ls.getD l default).s1
    (Ls.getD l default).F (Ls.getD l default).rounds
  have hrw : (Ls.getD l default).rw = rw := by unfold LvAt.rw; rw [hd]
  have hrec : (Ls.getD l default).osRec μ = W.osRec μ (Ls.getD l default).level (Ls.getD l default).s1
      (Ls.getD l default).F := by unfold LvAt.osRec; rw [hd]
  rw [← hrw] at hs
  rw [hs, hrec]
  exact ⟨e2, e1.trans (congrArg (· ++ _) (roundsSpec_glued _ _ _ _))⟩

/-- **Level `l` starts after `foldsOff` fold challenges.** -/
theorem gammas : ∀ l < (osCfg (candidate μ r)).levels.length,
    (Ls.getD l default).s.gammas.length = (osLvAt (osCfg (candidate μ r)) l).foldsOff
  | 0, _ => by rw [hR.start.1, hR.foldsOff0]; rfl
  | l + 1, hl => by
    have hy := hR.yr
    have ih := gammas l (by omega)
    obtain ⟨-, hf, -⟩ := hR.mid (l := l) (by omega)
    have hoff := hR.mid (l := l) (by omega)
    rw [(hR.stepS (by omega)).1, LvAt.s1, roundsSpec_gammas_length, ih, hf]
    exact hoff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm

end HonRun

end
end LeanVM.Guest.B1.Whir
