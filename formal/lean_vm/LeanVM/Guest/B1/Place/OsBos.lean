/-
  LeanVM.Guest.B1.Place.OsBos

  open_stacked's frame-size bound at each stack size: its frame, its buffers, a bound per call
  statement.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.Memory.Uniform

/-!
# The frame-size bound of an opening arm

The arm of size `m` (`open_stacked__L{m}`, stack log `μ = minOpenLog + m`) has the body
`osBody (osCfg m)` (`Whir/Template.lean`, checked equal to the core IR by `Whir/Data*.lean`):
straight-line atoms, calls and dispatches on the rate's selector, then its `ret`. A rate is a
dispatch's arm, so a static bound of the body covers every rate.

* `osSizesL c`: the sizes of the body's `HeapBuf`s, in allocation order.
* `osCallees c`: each call statement's callees, in order: a call's one, a dispatch's every arm.
  `osCalleeNames c`: all of them.
* `osArgsOk m f args`: what arm `m` passes its callee `f`, the exponents a runtime-sized callee reads.
* `osCallB fs Bk names`: a call statement entered within `Bk f` words or skipped (its frame `fs f`)
  at its costliest callee; `osKidsB`, their total; `osBos fs Bk name c`: the frame `fs name`, the
  buffers, the calls.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## The buffers and the calls -/

/-- The query positions of every level at the levels' rate (`LIG_POS_TOTAL`): each level's squeezes
times the positions a squeezed word carries. -/
def osPosTotal (c : OsCfg) : ℕ := (c.levels.map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum

/-- **`open_stacked`'s heap buffers' sizes**, in allocation order (`Whir.osHead`, `osLevel`,
`osTail`, `osFinish`): the head's eleven (`final_msg`, `level_roots`, `fold_challenges`,
`round_coefs`, `level_scales`, `level_lam_invs`, `level_hs`, `ood_z`, `ood_scalars`, `pos_totals`,
`query_positions`, `query_win_ptrs`); each non-final level's message `sent`; the final level's
normalized lane `hs`; `tail_challenges`, `point`, `point1`, `basis_d`, `level_scale`, `level_after`,
`inner_chain`. -/
def osSizesL (c : OsCfg) : List ℕ :=
  let n := c.levels.length
  let lane := c.yrLen + (c.levels.getD c.yrLevel default).folds
  [lane, 2 * n, c.nFolds, 2 * c.nFolds, n, n, n * hsStride, n * ligColsCap, n, ligNRates,
    osPosTotal c, osPosTotal c] ++
  ((c.levels.take c.yrLevel).map fun lv ↦ 2 + lv.folds) ++
  [lane, yrLogCap, pointCap, pointCap, n * ligColsCap, n, n, 2 * n]

/-- The callees of a call statement: a call's, a conditional call's, a dispatch's arms. -/
def Stmt.calleesS : Stmt → Option (List String)
  | .call f _ _ => some [f]
  | .callIf _ f _ => some [f]
  | .dispatch _ fs _ _ => some fs
  | _ => none

/-- The body's call statements' callees, in order. -/
def osCallees (c : OsCfg) : List (List String) := (osBody c).filterMap Stmt.calleesS

/-- Every callee of the body. -/
def osCalleeNames (c : OsCfg) : List String := (osCallees c).flatten

/-! ## The callees' arguments -/

/-- The names of arm `m`'s `level_positions` specializations, at every rate and level. -/
def osPosNames (m : ℕ) : List String :=
  (List.range ligNRates).flatMap fun r ↦ (List.range (osNLevels m)).map fun l ↦ osPositionsName (osLvR m r l)

/-- The names of arm `m`'s `level_residual` specializations, at every level before the final one. -/
def osResNames (m : ℕ) : List String :=
  (List.range (osCfg m).yrLevel).map fun l ↦ osResidualName (osLvR m 0 l)

/-- **What arm `m` passes its callee `f`**: a `level_positions` specialization, the row of some rate `r`'s level
`l`, gets `g^squeezes` at argument `9`; a `level_residual` one, of a level `l` before the final one, `g^(n / resBatch)`
and `g^(n % resBatch)` at `4` and `5`, `n` the queries of rate `r`'s row; any other callee anything. -/
def osArgsOk (m : ℕ) (f : String) (args : List E) : Prop :=
  if f ∈ osPosNames m then
    ∃ r < ligNRates, ∃ l < osNLevels m, f = osPositionsName (osLvR m r l) ∧
      args.getD 9 0 = ofK (addressOfIndex (osLvR m r l).squeezes)
  else if f ∈ osResNames m then
    ∃ r < ligNRates, ∃ l < (osCfg m).yrLevel, f = osResidualName (osLvR m 0 l) ∧
      args.getD 4 0 = ofK (addressOfIndex ((osLvR m r l).queries / resBatch)) ∧
      args.getD 5 0 = ofK (addressOfIndex ((osLvR m r l).queries % resBatch))
  else True

/-- Rate `r`'s level `l` is `osCfgR m r`'s. -/
theorem osLvR_eq_getD {m r l : ℕ} (h : l < osNLevels m) : osLvR m r l = (osCfgR m r).levels.getD l default := by
  simp [osCfgR, osLevelsR, List.getD_eq_getElem?_getD, h]

/-- `osCfgR m r` has `osNLevels m` levels. -/
theorem osCfgR_levels_length (m r : ℕ) : (osCfgR m r).levels.length = osNLevels m := by
  simp [osCfgR, osLevelsR]

/-- `level_residual`'s name is the same at every rate. -/
theorem osResidualName_rate (m r l : ℕ) : osResidualName (osLvR m r l) = osResidualName (osLvR m 0 l) := rfl

/-! ## The bound -/

/-- A call statement: entered within `Bk f` words or skipped (its frame `fs f`), at its costliest
callee. -/
def osCallB (fs Bk : String → ℕ) (names : List String) : ℕ :=
  (names.map fun f ↦ max (fs f) (Bk f)).foldl max 0

/-- The body's calls' total, one `osCallB` per call statement. -/
def osKidsB (fs Bk : String → ℕ) (c : OsCfg) : ℕ := ((osCallees c).map (osCallB fs Bk)).sum

/-- **`open_stacked`'s frame-size bound** at a configuration. -/
def osBos (fs Bk : String → ℕ) (name : String) (c : OsCfg) : ℕ :=
  fs name + (osSizesL c).sum + osKidsB fs Bk c

theorem le_foldl_max_init : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a
  | [], _ => le_rfl
  | y :: l, a => le_trans (le_max_left a y) (le_foldl_max_init l (max a y))

theorem le_foldl_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → ∀ a : ℕ, x ≤ l.foldl max a
  | [], _, h, _ => absurd h List.not_mem_nil
  | y :: l, x, h, a => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a x) (le_foldl_max_init l _)
    · exact le_foldl_max h _

/-- An entry of a mapped list within its `foldl max`. -/
theorem le_foldl_max_map {α : Type} (F : α → ℕ) {l : List α} {a : α} (h : a ∈ l) : F a ≤ (l.map F).foldl max 0 :=
  le_foldl_max (List.mem_map_of_mem h) 0

/-- **A callee within its statement's bound.** -/
theorem le_osCallB {fs Bk : String → ℕ} {names : List String} {f : String} (h : f ∈ names) :
    max (fs f) (Bk f) ≤ osCallB fs Bk names :=
  le_foldl_max (List.mem_map.mpr ⟨f, h, rfl⟩ : max (fs f) (Bk f) ∈ names.map fun f ↦ max (fs f) (Bk f)) 0

end
end LeanVM.Guest.B1
