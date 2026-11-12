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
  fold : L.level.fold = ((c.levels.getD l default)).folds
  dep : ((c.levels.getD l default)).depth = L.dp logN
  q : L.level.queries = ((c.levels.getD l default)).queries
  sq : ((c.levels.getD l default)).squeezes = sqCount (128 / ((c.levels.getD l default)).depth) ((c.levels.getD l default)).queries
  g1 : L.s1.alphas.length = ((c.levels.getD l default)).foldsOff + ((c.levels.getD l default)).folds
  mu : L.mu logN = ((c.levels.getD l default)).logCols
  qsh : QshOk c l ((c.levels.getD l default)) (if l = c.yrLevel then 1 else 0)
  P1 : 1 ≤ 128 / ((c.levels.getD l default)).depth

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

theorem s1_alphas {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    (Ls.getD l default).s1.alphas.length =
      (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).foldsOff + (Ls.getD l default).level.fold := by
  rw [LvAt.s1, roundsSpec_alphas_length, hR.alphas l hl]

/-- **Every level of the run against its row.** -/
theorem lvb {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    LvB (osCfgR (μ - minOpenLog) (r - 1)) μ l (Ls.getD l default) := by
  have hy := hR.yr
  have hg := hR.s1_alphas hl
  by_cases hlt : l < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel
  · obtain ⟨hne, hfold, hcols, -, hdep, hq, -, -, hP1, hsq, -, -, -, -, -, -, -, -, -, -, -, hqsh,
      -⟩ := hR.mid hlt
    rw [hfold] at hg
    have hmu : (Ls.getD l default).mu μ = (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).logCols := by
      simp only [LvAt.mu]; rw [hg, hcols]
    refine ⟨hfold, ?_, hq, hsq, hg, hmu, by simpa [hne] using hqsh, hP1⟩
    rw [hdep, LvAt.dp, hmu]
  · have he : l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel := by omega
    subst he
    obtain ⟨-, hfold, hcols, -, hdep, hq, -, -, hP1, hsq, -, -, -, -, -, -, -, -, -, -, hqsh, -, -, -, -, -,
      hlc, -⟩ := hR.fin
    rw [hfold] at hg
    have hmu : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).mu μ =
        ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).logCols := by
      simp only [LvAt.mu]; rw [hg, hcols, hlc]
    refine ⟨hfold, ?_, hq, hsq, hg, hmu, by simpa using hqsh, hP1⟩
    rw [hdep, LvAt.dp, hmu, hlc]

end HonRun

end
end LeanVM.Guest.B1.Whir
