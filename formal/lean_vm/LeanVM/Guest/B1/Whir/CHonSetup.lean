/-
  LeanVM.Guest.B1.Whir.CHonSetup

  The honest data of an accepting run of the stacked opening and what the run gives of it.
-/

module

public import LeanVM.Guest.B1.Whir.CHonRun
public import LeanVM.Guest.B1.Whir.CHonBuf
public import LeanVM.Guest.B1.Whir.CCaps
public import LeanVM.Guest.B1.Whir.FactsAll
public import LeanVM.Guest.B1.Place.OsSpec
public import LeanVM.Guest.B1.Place.OsProtoSpec

/-!
# The honest data of a run

`hdOf μ r Ls`: the honest data at the arm of `μ` and the rate `r` (`osCfgR`) of the levels `Ls`, each level's cap
cells and flags its phase's (`capCellH`, `capFlH`) at its root's height. `HonRun h …`: `h` is the
honest data of an accepting run (`whirOpen_honest`, `LvsRun.data`, `lvsAt_run`), its levels'
openings agreeing, the configuration's checked facts (`CandOk`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Level `l`'s root's height. -/
def heightAt (Ls : List LvAt) (l : ℕ) : ℕ := ((Ls.getD l default).R.getD l default).2.1

/-- **The honest data** of the levels `Ls` at the arm of `μ`, rate `r`. -/
noncomputable def hdOf (μ r : ℕ) (Ls : List LvAt) : OsHD :=
  ⟨osCfgR (μ - minOpenLog) (r - 1), μ, Ls,
    fun l ↦ capCellH (heightAt Ls l) ((Ls.getD l default).qs μ) (Ls.getD l default).phase,
    fun l ↦ capFlH (heightAt Ls l) ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth
      ((Ls.getD l default).qs μ) (Ls.getD l default).phase⟩

/-- **The run's facts** about its honest data. -/
structure HonRun (μ r : ℕ) (target : E) (S : KeccakState) (root : Digest) (xs : List E)
    (os : List (List Opening)) (w : WhirEnd) (cfg : List Whir.Level) (Ls : List LvAt) : Prop where
  m11 : μ - minOpenLog < 11
  r4 : r - 1 < 4
  hcfg : Whir.ladder μ r = some cfg
  cand : CandOk (μ - minOpenLog) (r - 1) μ r cfg
  run : LvsAtRun μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [], []⟩ (capOf S)
    [(root, stackShape μ r)] xs os w Ls
  agree : ∀ i < Ls.length, ∀ root height width, (Ls.getD i default).R[i]? = some (root, height, width) →
    Guest.Limits.OpeningsAgree height (((Ls.getD i default).qs μ).zip (Ls.getD i default).phase)

end
end LeanVM.Guest.B1.Whir
