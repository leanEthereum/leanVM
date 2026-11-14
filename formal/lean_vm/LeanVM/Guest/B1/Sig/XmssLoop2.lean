/-
  LeanVM.Guest.B1.Sig.XmssLoop2

  An iteration of `main_loop2` (`lean_ethereum.py:4545-4558`) is sound for its leanXMSS check: its
  body holding, the statements before the check hold, the statements after it hold, and with the
  carried chain indices held the signature its valuation holds verifies the claim at `.n 65`.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegSound
public import LeanVM.Guest.B1.Sig.XmssSegData

/-!
# `main_loop2`'s body, sound for its leanXMSS check

`loop2_xmss_sound`: from `(Fn.«main_loop2».core).body = l2Pre ++ (xSeg ++ l2Post)` (`loop2_split`) and
`verify_lean_xmss_sound_holds`. The form `main`'s soundness reads an iteration's claim off.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem l2Pre_atoms : atomsOnly l2Pre = true := rfl

/-- **An iteration of `main_loop2`, sound for its check.** -/
theorem loop2_xmss_sound {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (Fn.«main_loop2».core).body next kret) :
    AtomsHold rd σ l2Pre ∧ Stmt.HoldsList C rd σ l2Post next kret ∧
      (LxTagsHold (fun j => σ (sTagParam j)) → XmssOut rd (σ sSigner) (xmssSigOf σ)) := by
  rw [loop2_split] at h
  have s := holdsList_split_atoms l2Pre_atoms h
  obtain ⟨hr, ho⟩ := verify_lean_xmss_sound_holds C rd σ l2Post next kret s.2
  exact ⟨atomsHold_of_holdsList l2Pre_atoms s.1, hr, ho⟩

end
end LeanVM.Guest.B1.Sig
