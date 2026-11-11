/-
  LeanVM.Guest.B1.Whir.CHonFields2

  Each level of the honest run against its row: the static facts the honest data's fields use.
-/

module

public import LeanVM.Guest.B1.Whir.CHonInv
public import LeanVM.Guest.B1.Whir.CHonFields0

/-!
# A level against its row

`LvB c logN l L`: level `L` of the run at row `l` of the candidate `c`: its folds, depth, queries,
squeezes, fold challenges after its folds, message log, and its `opening_queries` shape (`QshOk`,
final at the final level). `HonRun.lvb`: every level of the run has them.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A level against its row.** -/
structure LvB (c : OsCfg) (logN l : ℕ) (L : LvAt) : Prop where
  fold : L.level.fold = (osLvAt c l).folds
  dep : (osLvAt c l).depth = L.dp logN
  q : L.level.queries = (osLvAt c l).queries
  sq : (osLvAt c l).squeezes = sqCount (128 / (osLvAt c l).depth) (osLvAt c l).queries
  g1 : L.s1.alphas.length = (osLvAt c l).foldsOff + (osLvAt c l).folds
  mu : L.mu logN = (osLvAt c l).logCols
  qsh : QshOk c l (osLvAt c l) (if l = c.yrLevel then 1 else 0)
  P1 : 1 ≤ 128 / (osLvAt c l).depth

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

theorem s1_alphas {l : ℕ} (hl : l < (osCfg (candidate μ r)).levels.length) :
    (Ls.getD l default).s1.alphas.length =
      (osLvAt (osCfg (candidate μ r)) l).foldsOff + (Ls.getD l default).level.fold := by
  rw [LvAt.s1, roundsSpec_alphas_length, hR.alphas l hl]

/-- **Every level of the run against its row.** -/
theorem lvb {l : ℕ} (hl : l < (osCfg (candidate μ r)).levels.length) :
    LvB (osCfg (candidate μ r)) μ l (Ls.getD l default) := by
  have hy := hR.yr
  have hg := hR.s1_alphas hl
  by_cases hlt : l < (osCfg (candidate μ r)).yrLevel
  · obtain ⟨hne, hfold, hcols, -, hdep, hq, -, -, hP1, hsq, -, -, -, -, -, -, -, -, -, -, -, -, hqsh,
      -⟩ := hR.mid hlt
    rw [hfold] at hg
    have hmu : (Ls.getD l default).mu μ = (osLvAt (osCfg (candidate μ r)) l).logCols := by
      simp only [LvAt.mu]; rw [hg, hcols]
    refine ⟨hfold, ?_, hq, hsq, hg, hmu, by simpa [hne] using hqsh, hP1⟩
    rw [hdep, LvAt.dp, hmu]
  · have he : l = (osCfg (candidate μ r)).yrLevel := by omega
    subst he
    obtain ⟨-, hfold, hcols, -, hdep, hq, -, -, hP1, hsq, -, -, -, -, -, -, -, -, -, hqsh, -, -, -, -, -,
      hlc, -⟩ := hR.fin
    rw [hfold] at hg
    have hmu : (Ls.getD (osCfg (candidate μ r)).yrLevel default).mu μ =
        (osLvAt (osCfg (candidate μ r)) (osCfg (candidate μ r)).yrLevel).logCols := by
      simp only [LvAt.mu]; rw [hg, hcols, hlc]
    refine ⟨hfold, ?_, hq, hsq, hg, hmu, by simpa using hqsh, hP1⟩
    rw [hdep, LvAt.dp, hmu, hlc]

end HonRun

end
end LeanVM.Guest.B1.Whir
