/-
  LeanVM.Guest.VsTabs

  `verify_sub`'s window table at `tabs`, from the window section of the exponent table.
-/

module

public import LeanVM.Guest.Sound
public import LeanVM.Guest.B1.Common.Basic

/-!
# `verify_sub`'s window table (`VsTabsKnown`)

`open_stacked` assumes the window table at its argument `tabs` (`tagTabs`), so `verify_sub`'s cut
before its dispatch hands it on (`vs_cutOk`). Its statements before its first `tabs` do not
return, and the next two are `tabs = g_squares·g^WIN_TAB_AT` (`vs_takeTabs`, the constant a
word, `vsTabsWord_eq`); the window section of the exponent table at `g_squares` (argument `4`) is
then the window table at `tabs` (B1's `loadHolds_mul_gen_pow`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- The word `g^WIN_TAB_AT`, as the core IR writes it. -/
def vsTabsWord : E := word (gpowK winTabAt).toBitVec.toNat 0

theorem vsTabsWord_eq : vsTabsWord = gen ^ winTabAt := by
  rw [vsTabsWord, word, K.ofBits_toNat, K.ofBits_zero, ← ofK_eq_ofLimbs, gen_pow_eq_ofK,
    gpowK_eq (by decide)]

/-- `verify_sub`'s statements up to its first `tabs`: the constant, then `g_squares` times it. -/
theorem vs_takeTabs : (coreOf (fn_idx% «verify_sub»)).body.take (vsTabsAt + 2) =
    (coreOf (fn_idx% «verify_sub»)).body.take vsTabsAt ++
      [.atom (.const (.n vsTabsC) vsTabsWord), .atom (.mul (.n vsTabs) (.n 4) (.n vsTabsC))] := by
  rw [List.take_add]
  exact congrArg ((coreOf (fn_idx% «verify_sub»)).body.take vsTabsAt ++ ·) (stmtsEqb_sound (by decide +kernel))

theorem vs_noRetTabs : Stmt.noRetList ((coreOf (fn_idx% «verify_sub»)).body.take vsTabsAt) = true := by
  decide +kernel

/-- **`verify_sub`'s window table at `tabs`.** -/
theorem vsTabsKnown_proved : VsTabsKnown := by
  intro κ L σ hw hl
  rw [vs_takeTabs, holdsList_append, holdsList_noRet _ vs_noRetTabs] at hl
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hl
  obtain ⟨-, hc, hm, -⟩ := hl
  intro n hn
  rw [hm, hc, vsTabsWord_eq, loadHolds_mul_gen_pow]
  exact hw n hn

end
end LeanVM.Guest.End
