/-
  LeanVM.Guest.B1.Sig.XmssSegWinSpec

  What the path windows' completeness of leanXMSS's check in `main_loop2` establishes, as a
  statement (`LxWindowsC`): proved by `XmssSegPathC`, consumed by the layers' completeness.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegPath
public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.B1.Sig.SeqComplete

/-!
# The path windows' completeness, stated

`LxWindowsC`: a layer's two windows (`lxWindowT (2·layer)` from base `b0` on the node `cur`, then
`lxWindowT (2·layer + 1)` on its output) are numbered below their end, which is past `b0`, and
complete when the leaf index `L`'s shifts and windows are loaded, the powers set and the padding
run and `P` in place: the root is canonical and, on any valuation agreeing below the end, the
siblings the arms of `L`'s windows hint are `sibs` (`lxSibOf`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- Window `w`'s hinted sibling `r` in its dispatch's arm `k`, the window from base `b0`. -/
noncomputable def lxSibOf (σ : Val) (w k b0 r : Nat) : E := lxSibF σ w (lxArmB w 0 k (b0 + 5)) r

/-- **What the path windows' completeness establishes.** -/
def LxWindowsC : Prop :=
  ∀ (C : CallRel) (rd : Reader) (layer : Nat), layer < 2 → ∀ (cur : V) (b0 L : Nat), MemOK rd 256 →
    L < 2 ^ 32 → NBv b0 cur → 103 ≤ b0 →
    b0 ≤ (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
        (lxWindowT (2 * layer) cur b0).2.1).2.1 ∧
    NumBelow (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
        (lxWindowT (2 * layer) cur b0).2.1).2.1
      (Stmt.valsList ((lxWindowT (2 * layer) cur b0).1 ++ (lxWindowT (2 * layer + 1)
        (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1).1)) ∧
    ∀ σ : Val, PadOK σ sLxPad → (∀ v < 4, σ (sHis v) = eOfNat (L >>> (8 * v))) →
    (∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w))) → (∀ s < 13, σ (sPower s) = gen ^ s) →
    ∀ sibs : Nat → E,
    Completes C rd b0 (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
        (lxWindowT (2 * layer) cur b0).2.1).2.1
      ((lxWindowT (2 * layer) cur b0).1 ++ (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
        (lxWindowT (2 * layer) cur b0).2.1).1) σ
      (fun σ' => ∀ σ'', AgreeBelow (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
            (lxWindowT (2 * layer) cur b0).2.1).2.1 σ' σ'' →
          (∀ r < 8, lxSibOf σ'' (2 * layer) (lxWin L (2 * layer)) b0 r = sibs r) ∧
          ∀ r < 8, lxSibOf σ'' (2 * layer + 1) (lxWin L (2 * layer + 1)) (lxWindowT (2 * layer) cur b0).2.1 r =
            sibs (8 + r))

end
end LeanVM.Guest.B1.Sig
