/-
  LeanVM.Guest.B1.VsC.Os.LeftCalls

  `open_stacked`'s calls, in order, at each arm and rate.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftBody
public import LeanVM.Guest.B1.VsC.Os.WalkArms
public import LeanVM.Guest.Memory.Restrict

/-!
# `open_stacked`'s calls

`calls_flatD_eq`: on a flat body with no conditional call, its selectors all the rate's, the calls
of the path at a valuation whose rate selector is `g^ri` are the statements' calls, each dispatch
taking arm `ri` (`Stmt.callD ri`).

`osCallSpec c`: the calls `open_stacked`'s body makes at the configuration `c`, in order, by name,
and for the helpers (`level_positions`, `level_queries`, `level_residual`, `level_residual_slow`)
with their arguments and returns (`osLpCallOf`, `osLqCallOf`, `osLrCalls`, `osSlowCalls`): per
level, `opening_message`, at a non-final level `squeeze_point_from`, `level_positions`, at a
non-final level `is_zero`, `level_queries`; `opening_tail_round` `yrLog` times; `fold_final_msg`;
`is_zero` per non-final level (the basis rows); per non-final level `level_residual`, `is_zero`,
`level_residual_slow`. `osBody_calls`: the path's calls match it, one kernel decision an arm.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value

@[expose] public section

/-! ## The calls of a flat body -/

/-- A flat statement's call, a dispatch taking arm `ri`. -/
def _root_.LeanVM.Guest.Core.Stmt.callD (ri : ℕ) : Stmt → Option Call
  | .call f a r => some ⟨f, a, r, true⟩
  | .dispatch _ fs a r => some ⟨fs.getD ri "", a, r, true⟩
  | _ => none

/-- A statement of a flat body with no conditional call, its selector the rate's. -/
def _root_.LeanVM.Guest.Core.Stmt.callOkD : Stmt → Bool
  | .callIf .. => false
  | s => s.flatD && s.selV.all (· == .n osRate)

theorem calls_fdEvs {σ : Val} {ri : ℕ} (hri : logG (σ (.n osRate)) = ri) :
    ∀ s : Stmt, s.callOkD = true → calls (fdEvs σ s) = (s.callD ri).toList
  | .atom a, _ => by
    change calls [Ev.atom a] = []
    rfl
  | .call f a r, _ => rfl
  | .callIf .., h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | .match_ x arms, _ => by
    change calls (armEvs (arms.getD (logG (σ x)) [])) = []
    exact calls_armEvs _
  | .dispatch x fs a r, h => by
    change (Stmt.flatD (.dispatch x fs a r) && (some x).all (· == .n osRate)) = true at h
    simp only [Stmt.flatD, Option.all_some, Bool.true_and, beq_iff_eq] at h
    subst h
    change calls [Ev.call (fs.getD (logG (σ (.n osRate))) "") a r] = _
    rw [hri]
    rfl
  | .ite c t e, h => by
    change ((Stmt.ite c t e).flatD && (Stmt.ite c t e).selV.all (· == .n osRate)) = true at h
    simp [Stmt.flatD] at h
  | .ret vs, h => by
    change ((Stmt.ret vs).flatD && (Stmt.ret vs).selV.all (· == .n osRate)) = true at h
    simp [Stmt.flatD] at h

/-- **A flat body's calls are its statements'**, each dispatch at arm `ri`. -/
theorem calls_flatD_eq {σ : Val} {ri : ℕ} (hri : logG (σ (.n osRate)) = ri) :
    ∀ ss : List Stmt, ss.all Stmt.callOkD = true → calls (ss.flatMap (fdEvs σ)) = ss.filterMap (Stmt.callD ri)
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.flatMap_cons, calls_append, calls_fdEvs hri s h.1, calls_flatD_eq hri ss h.2, List.filterMap_cons]
    cases s.callD ri <;> rfl

/-! ## The spec -/

/-- **`open_stacked`'s calls at the configuration `c`**, in order: each callee's name, and a
helper's arguments and returns. -/
def osCallSpec (c : OsCfg) : List (String × Option (List V × List V)) :=
  ((List.range c.levels.length).flatMap fun l ↦
    if l = c.yrLevel then
      [("opening_message__L" ++ natStr (c.yrLen + (osLvA c l).folds) ++ "_L1", none),
        (osPositionsName (osLvA c l), some (osLpCallOf c l)),
        (osQueriesName c l (osLvA c l), some (osLqCallOf c l))]
    else
      [("opening_message__L" ++ natStr (2 + (osLvA c l).folds) ++ "_L1", none),
        ("squeeze_point_from__L" ++ natStr (osLvA c l).logCols, none),
        (osPositionsName (osLvA c l), some (osLpCallOf c l)), ("is_zero", none),
        (osQueriesName c l (osLvA c l), some (osLqCallOf c l))]) ++
  List.replicate c.yrLog ("opening_tail_round", none) ++
  [("fold_final_msg__L" ++ natStr c.yrLog, none)] ++
  List.replicate c.yrLevel ("is_zero", none) ++
  (List.range c.yrLevel).flatMap fun l ↦
    [(osResidualName (osLvA c l), some ((osLrCalls c).getD l ([], []))), ("is_zero", none),
      (osSlowName c (osLvA c l), some ((osSlowCalls c).getD l ([], [])))]

/-- A call matches a spec entry: its name, entered, and a helper's arguments and returns. -/
def callMatches : Call → String × Option (List V × List V) → Bool
  | c, (f, none) => c.f == f && c.taken
  | c, (f, some (a, r)) => c.f == f && c.taken && c.args == a && c.rets == r

/-- Calls matching a spec entry by entry. -/
def callsMatch : List Call → List (String × Option (List V × List V)) → Bool
  | [], [] => true
  | c :: cs, s :: ss => callMatches c s && callsMatch cs ss
  | _, _ => false

theorem callsMatch_forall₂ : ∀ {cs : List Call} {ss : List (String × Option (List V × List V))},
    callsMatch cs ss = true → List.Forall₂ (fun c s ↦ callMatches c s = true) cs ss
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    simp only [callsMatch, Bool.and_eq_true] at h
    exact .cons h.1 (callsMatch_forall₂ h.2)
  | [], _ :: _, h => by simp [callsMatch] at h
  | _ :: _, [], h => by simp [callsMatch] at h

/-- An entry's facts: a call matching `(f, none)` is `f`, entered. -/
theorem callMatches_none {c : Call} {f : String} (h : callMatches c (f, none) = true) : c.f = f ∧ c.taken = true := by
  simpa [callMatches] using h

/-- A call matching `(f, some (a, r))` is `⟨f, a, r, true⟩`. -/
theorem callMatches_some {c : Call} {f : String} {a r : List V} (h : callMatches c (f, some (a, r)) = true) :
    c = ⟨f, a, r, true⟩ := by
  obtain ⟨f', a', r', t'⟩ := c
  simp only [callMatches, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  subst h1 h2 h3 h4
  rfl

/-- What an arm's body checks: no conditional call, the selectors the rate's, the calls the spec's
at every rate. -/
def OsCallsOk (m : ℕ) : Bool :=
  (osBodyA (osCfg m)).all Stmt.callOkD &&
    (List.range 4).all fun ri ↦ callsMatch ((osBodyA (osCfg m)).filterMap (Stmt.callD ri)) (osCallSpec (osCfgR m ri))

set_option maxRecDepth 100000 in
theorem osCallsOk_0 : OsCallsOk 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_1 : OsCallsOk 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_2 : OsCallsOk 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_3 : OsCallsOk 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_4 : OsCallsOk 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_5 : OsCallsOk 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_6 : OsCallsOk 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_7 : OsCallsOk 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_8 : OsCallsOk 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_9 : OsCallsOk 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_10 : OsCallsOk 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_11 : OsCallsOk 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_12 : OsCallsOk 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_13 : OsCallsOk 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osCallsOk_14 : OsCallsOk 14 = true := by decide +kernel

theorem osCallsOk_all (m : ℕ) (hm : m < 15) : OsCallsOk m = true := by
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · exact osCallsOk_0
  · exact osCallsOk_1
  · exact osCallsOk_2
  · exact osCallsOk_3
  · exact osCallsOk_4
  · exact osCallsOk_5
  · exact osCallsOk_6
  · exact osCallsOk_7
  · exact osCallsOk_8
  · exact osCallsOk_9
  · exact osCallsOk_10
  · exact osCallsOk_11
  · exact osCallsOk_12
  · exact osCallsOk_13
  · exact osCallsOk_14
  · omega

/-- **`open_stacked`'s calls at the arm `m` and rate index `ri`** match `osCallSpec`, on a valuation
whose rate selector is `g^ri`. -/
theorem osBody_calls {m ri : ℕ} (hm : m < 15) (hri : ri < 4) {σ : Val} (hs : logG (σ (.n osRate)) = ri) :
    List.Forall₂ (fun c s ↦ callMatches c s = true) (calls ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ)))
      (osCallSpec (osCfgR m ri)) := by
  have h := osCallsOk_all m hm
  simp only [OsCallsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  rw [← osBodyA_rate m ri, calls_flatD_eq hs _ (List.all_eq_true.mpr h.1)]
  exact callsMatch_forall₂ (h.2 ri hri)

/-- The rate selector of `open_stacked`'s arguments names the rate index. -/
theorem logG_rateSel {r : ℕ} (hr1 : 1 ≤ r) (hr4 : r ≤ 4) : logG (rateSel r) = r - 1 :=
  logG_spec (by omega)

end
end LeanVM.Guest.B1.VsC
