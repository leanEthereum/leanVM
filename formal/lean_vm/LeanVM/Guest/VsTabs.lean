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
before its dispatch hands it on (`VsAt.lean`). Its statements before the dispatch but the last two
do not return, and those two are `tabs = g_squares·g^236` (`vsTabsT vsTabsC vsTabs`, `vsTabsT_holds`); the window section of the
exponent table at `g_squares` (argument `4`) is then the window table at `tabs`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem vs_takeTabs : (coreOf (fn_idx% «verify_sub»)).body.take vsTabsAt =
    (coreOf (fn_idx% «verify_sub»)).body.take (vsTabsAt - 2) ++ VerifySub.vsTabsT vsTabsC vsTabs := by
  conv_lhs => rw [show vsTabsAt = vsTabsAt - 2 + 2 from rfl]
  rw [List.take_add, coreOf_verify_sub]
  exact congrArg ((fn% «verify_sub»).body.take (vsTabsAt - 2) ++ ·) (stmtsEqb_sound (by decide +kernel))

theorem vs_noRetTabs : Stmt.noRetList ((coreOf (fn_idx% «verify_sub»)).body.take (vsTabsAt - 2)) = true := by
  rw [coreOf_verify_sub]; decide +kernel

/-- **`verify_sub`'s window table at its dispatch to `open_stacked`.** -/
theorem vsTabsKnown_proved : VsTabsKnown := by
  intro κ L _ _ σ hw hl
  rw [vs_takeTabs, holdsList_append, holdsList_noRet _ vs_noRetTabs] at hl
  obtain ⟨he, -⟩ := VerifySub.vsTabsT_holds hl.2
  rw [he]
  intro n hn
  rw [loadHolds_mul_gen_pow]
  exact hw n hn

end
end LeanVM.Guest.End
