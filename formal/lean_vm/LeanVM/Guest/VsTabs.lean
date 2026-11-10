/-
  LeanVM.Guest.VsTabs

  `verify_sub`'s obligation at its dispatch to `open_stacked`: the window table at `tabs`.
-/

module

public import LeanVM.Guest.Sound
public import LeanVM.Guest.B1.VerifySub.Front

/-!
# `verify_sub`'s window table (`VsTabsKnown`)

`open_stacked` assumes the window table at its argument `tabs` (`tagTabs`), so `verify_sub`'s cut
before its dispatch hands it on. Its first `1549` statements do not return, and the next two are
`tabs = g_squares·g^236` (`vsTabsT 1929 1930`, `vsTabsT_holds`); the window section of the
exponent table at `g_squares` (argument `4`) is then the window table at `tabs`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem vs_take1551 : (coreOf 19).body.take 1551 =
    (coreOf 19).body.take 1549 ++ VerifySub.vsTabsT 1929 1930 := by
  rw [show 1551 = 1549 + 2 from rfl, List.take_add, coreOf_19]
  exact congrArg (Data.core18.body.take 1549 ++ ·) (stmtsEqb_sound (by decide +kernel))

theorem vs_noRet1549 : Stmt.noRetList ((coreOf 19).body.take 1549) = true := by
  rw [coreOf_19]; decide +kernel

/-- **`verify_sub`'s window table at its dispatch to `open_stacked`.** -/
theorem vsTabsKnown_proved : VsTabsKnown := by
  intro κ L _ _ σ hw hl
  rw [vs_take1551, holdsList_append, holdsList_noRet _ vs_noRet1549] at hl
  obtain ⟨he, -⟩ := VerifySub.vsTabsT_holds hl.2
  rw [he]
  intro n hn
  rw [loadHolds_mul_gen_pow]
  exact hw n hn

end
end LeanVM.Guest.End
