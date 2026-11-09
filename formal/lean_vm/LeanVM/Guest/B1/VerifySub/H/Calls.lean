/-
  LeanVM.Guest.B1.VerifySub.H.Calls

  `verify_sub`'s frames: its thirteen calls in order, the dispatch's callee named by the candidate.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Regions

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory

@[expose] public section

/-- A call statement's frame. -/
def vcs (f : String) (args rets : List ℕ) : Option V × String × List V × List V :=
  (none, f, args.map V.n, rets.map V.n)

/-- The calls before the dispatch. -/
def vsCallsA : List (Option V × String × List V × List V) :=
  [vcs "g_power_of_word" [110] [120], vcs "g_power_of_word" [27] [128],
    vcs "log2_ceil_in_the_exponent__L0_L34" [308, 4] [309],
    vcs "assert_canonical" [324] [344], vcs "assert_canonical" [334] [345],
    vcs "verify_bus_gkr" [612, 613, 614, 615, 616, 625, 309, 310] ((List.range 9).map (626 + ·)),
    vcs "verify_tables" [626, 627, 628, 629, 630, 631, 0, 1, 310, 309, 127, 26, 4, 427, 623, 6, 635,
      632, 633, 634] ((List.range 10).map (636 + ·)),
    vcs "verify_keccak" [636, 637, 638, 639, 640, 641, 646, 635, 650, 647, 648]
      ((List.range 8).map (651 + ·)),
    vcs "ring_switch_target" [648, 664] [1091],
    vcs "certify_placement" [139, 4] [1682, 1683],
    vcs "log2_ceil_in_the_exponent__L15_L34" [1682, 4] [1684]]

/-- The dispatch's arguments and returns. -/
def vsDispArgs : List V := [.n 1100, .n 1101, .n 1102, .n 1103, .n 1104, .n 1681, .n 324, .n 334, .n 656]

/-- The calls after the dispatch. -/
def vsCallsB : List (Option V × String × List V × List V) :=
  [vcs "check_opening_terminal" [4, 310, 635, 644, 309, 642, 128, 646, 139, 1111, 1683, 647, 665,
    1701, 1702, 1703, 1704, 1700] []]

/-- No dispatch. -/
def noDispatchB : Stmt → Bool
  | .dispatch .. => false
  | _ => true

theorem vs_split_disp : vsCPre = vsCPre.take 1599 ++
    [.dispatch (.n 1695) vsOpenNames vsDispArgs (vsRun 1700 5)] ++ vsCPre.drop 1600 := by
  have h : (vsCPre.drop 1599).take 1 = [.dispatch (.n 1695) vsOpenNames vsDispArgs (vsRun 1700 5)] :=
    (Tables.tbStmtsEqb_sound (by decide +kernel)).symm
  have e : vsCPre.drop 1599 = (vsCPre.drop 1599).take 1 ++ vsCPre.drop 1600 := by
    rw [show vsCPre.drop 1600 = (vsCPre.drop 1599).drop 1 by simp [List.drop_drop],
      List.take_append_drop]
  rw [List.append_assoc, ← h, ← e, List.take_append_drop]

theorem vs_noDisp : (vsCPre.take 1599).all noDispatchB = true ∧ (vsCPre.drop 1600).all noDispatchB = true := by
  decide +kernel

theorem vs_callsA : (vsCPre.take 1599).filterMap Stmt.callS = vsCallsA := by decide +kernel

theorem vs_callsB : (vsCPre.drop 1600).filterMap Stmt.callS = vsCallsB := by decide +kernel

theorem callSF_noDisp (σ : Val) : ∀ (l : List Stmt), l.all noDispatchB = true →
    l.filterMap (Core.Stmt.callSF σ) = l.filterMap Stmt.callS
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := callSF_noDisp σ l h.2
    cases s with
    | dispatch => simp [noDispatchB] at h
    | _ => simp only [List.filterMap_cons, Core.Stmt.callSF, ih]

/-- **`verify_sub`'s frames**, the dispatch's callee named by the candidate. -/
theorem vs_calls (σ : Val) : (vsCPre.filterMap (Core.Stmt.callSF σ)).map (mkCall σ) =
    (vsCallsA ++ [(none, vsOpenNames.getD (logG (σ (.n 1695))) "", vsDispArgs, vsRun 1700 5)] ++
      vsCallsB).map (mkCall σ) := by
  rw [vs_split_disp, List.filterMap_append, List.filterMap_append,
    callSF_noDisp σ _ vs_noDisp.1, callSF_noDisp σ _ vs_noDisp.2, vs_callsA, vs_callsB]
  rfl

end
end LeanVM.Guest.B1.VerifySub
