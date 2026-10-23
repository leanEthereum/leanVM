/-
  LeanVM.Guest.B1.Tables.VerifyTablesAir

  `verify_tables`' per-table constraint evaluations: each table's forms on the three sides,
  computed from its column evaluations, are the specification's.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesPoly
public import LeanVM.Guest.B1.Tables.VerifyTablesBase
public import LeanVM.Protocol.EndToEnd.Complete.Flushes

/-!
# The tables' constraint evaluations (G:1752-1812)

For each table `t`, `verify_tables` reads its column evaluations (`col_evals`, `vtEvalVars`) and
computes `constraint_eval`: `JUMP`'s two identities, plus each side's form, `Σ_b eq_hi(b)·(β +
Σ_i fp_w[i]·coord_i)` over the side's blocks of `t`, weighted by `ξ^(2 + side)`. The value is the
expression `ceEx t`, built from the specification's flushes with symbolic coefficients
(`pySideC`, whose coefficients lie in `K`): the normal forms agree by kernel evaluation
(`vt_ce`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-- Each table's column evaluations, by value number: the words read (`col_evals`). -/
def vtEvalVars : List (List ℕ) :=
  [[4661, 4677, 4693, 4709, 4725, 4741, 4757, 4773, 4789, 4805, 4821, 4837, 4853, 4869, 4885],
    [5149, 5165, 5181, 5197, 5213, 5229, 5245, 5261, 5277, 5293, 5309, 5325, 5341, 5357, 5373],
    [5678, 5694, 5710, 5726, 5742, 5758, 5774, 5790],
    [5955, 5971, 5987, 6003, 6019, 6035, 6051, 6067, 6083, 6099, 6115, 6131, 6147, 6163, 6179],
    [6478, 6494, 6510, 6526, 6542, 6558, 6574, 6590, 6606, 6622, 6638, 6654, 6670, 6686],
    [6980, 6996, 7012, 7028, 7044, 7060, 7076, 7092, 7108, 7124, 7140, 7156, 7172, 7188, 7204, 7220, 7236, 7252, 7268, 7284, 7300, 7316, 7332, 7348, 7364, 7380, 7396, 7412, 7428, 7444, 7460, 7476, 7492, 7508, 7524, 7540, 7556]]

/-- Each table's blocks' `eq_hi`, by value number, per side (push, pull, count). -/
def vtEqhiVars : List (List (List ℕ)) :=
  [[[2105, 2134, 2163, 2192, 2221], [3469, 3476, 3483, 3490, 3497], [3733, 3762, 3791, 3820]],
    [[2250, 2279, 2308, 2337, 2366], [3504, 3511, 3518, 3525, 3532], [3849, 3878, 3907, 3936]],
    [[2395, 2424, 2453], [3539, 3546, 3553], [3965, 3994]],
    [[2482, 2511, 2540, 2569, 2598], [3560, 3567, 3574, 3581, 3588], [4023, 4052, 4081, 4110]],
    [[2627, 2656, 2685, 2714, 2743], [3595, 3602, 3609, 3616, 3623], [4139, 4168, 4197, 4226]],
    [[2772, 2801, 2830, 2859, 2888, 2917, 2946, 2975, 3004, 3033, 3062], [3630, 3637, 3644, 3651, 3658, 3665, 3672, 3679, 3686, 3693, 3700], [4255, 4284, 4313, 4342, 4371, 4400, 4429, 4458, 4487, 4516]]]

/-- Each table's `constraint_eval`, by value number. -/
def vtCeVars : List ℕ := [5140, 5668, 5945, 6468, 6970, 8131]

/-- Each table's window of statements: its first statement and its length. -/
def vtTableWin : List (ℕ × ℕ) := [(4374, 481), (4862, 521), (5391, 269), (5668, 515), (6191, 494), (6693, 1153)]

/-- `ξ^k`, `k < 5`, by value number (`zc_xi_pows`). -/
def vtXiVars : List ℕ := [4622, 4623, 4624, 4625, 4626]

/-- The count columns of each table (`Table.countColumns`). -/
def vtCountCols : List (List ℕ) :=
  [[11, 12, 13, 14], [11, 12, 13, 14], [6, 7], [11, 12, 13, 14], [8, 9, 10, 11],
    [27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]

/-- The loads of `fp_w`: weight `i` is the named quantity `i`. -/
def vtFpwTab : LoadTab := (List.range 16).map fun i => ((11, i), .ext i)

/-- The product of the values. -/
def prodVarsEx : List ℕ → Ex
  | [] => .lit 1
  | v :: vs => .mul (.var v) (prodVarsEx vs)

/-- A sum of expressions. -/
def sumEx (l : List Ex) : Ex := l.foldr .add (.lit 0)

/-- A symbolic form over the column evaluations `ev`. -/
def coordEx (ev : List ℕ) (f : FormC) : Ex :=
  sumEx (f.terms.map fun t => .mul (.lit t.2.evK) (prodVarsEx (t.1.map (ev.getD · 0))))

/-- A push or pull block's form: `β + Σ_i fp_w[i]·coord_i`. -/
def blockEx (ev : List ℕ) (coords : List FormC) : Ex :=
  .add (.var 12) (sumEx (coords.zipIdx.map fun p => .mul (.ext p.2) (coordEx ev p.1)))

/-- A side's form of a table: its blocks' forms weighted by their `eq_hi`. -/
def sideEx (eqh : List ℕ) (forms : List Ex) : Ex :=
  sumEx ((List.zip eqh forms).map fun p => .mul (.var p.1) p.2)

/-- `JUMP`'s two identities: `ξ^0·(b + v_cond·w) + ξ·(v_cond·(b + 1))`. -/
def jumpEx (ev : List ℕ) : Ex :=
  .add (.mul (.var 4622) (.add (.var (ev.getD 13 0)) (.mul (.var (ev.getD 5 0)) (.var (ev.getD 12 0)))))
    (.mul (.var 4623) (.mul (.var (ev.getD 5 0)) (.add (.var (ev.getD 13 0)) (.lit 1))))

/-- Table `t`'s `constraint_eval`, as an expression. -/
def ceEx (t : Fin 6) : Ex :=
  let ev := vtEvalVars.getD t []
  let eqh := vtEqhiVars.getD t []
  let push := sideEx (eqh.getD 0 []) ((pySideC t .push).map (blockEx ev))
  let pull := sideEx (eqh.getD 1 []) ((pySideC t .pull).map (blockEx ev))
  let count := sideEx (eqh.getD 2 []) ((vtCountCols.getD t []).map fun l => .var (ev.getD l 0))
  let forms := Ex.add (.mul (.var 4624) push) (.add (.mul (.var 4625) pull) (.mul (.var 4626) count))
  if t = 4 then .add (jumpEx ev) forms else forms

/-- The guest's value of table `t`'s `constraint_eval`, symbolically. -/
noncomputable def vtCeSym (t : Fin 6) : Ex :=
  (symExec vtFpwTab [] (((vtPre.drop (vtTableWin.getD t (0, 0)).1).take
    (vtTableWin.getD t (0, 0)).2).filterMap atomOf)).get (vtCeVars.getD t 0)

theorem vt_ce0 : (vtCeSym 0).norm = (ceEx 0).norm := by decide +kernel
theorem vt_ce1 : (vtCeSym 1).norm = (ceEx 1).norm := by decide +kernel
theorem vt_ce2 : (vtCeSym 2).norm = (ceEx 2).norm := by decide +kernel
theorem vt_ce3 : (vtCeSym 3).norm = (ceEx 3).norm := by decide +kernel
theorem vt_ce4 : (vtCeSym 4).norm = (ceEx 4).norm := by decide +kernel
theorem vt_ce5 : (vtCeSym 5).norm = (ceEx 5).norm := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
