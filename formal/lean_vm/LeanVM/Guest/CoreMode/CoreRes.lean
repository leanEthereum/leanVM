/-
  LeanVM.Guest.CoreMode.CoreRes

  The residuals the core route takes, by family: a heap certificate's statements on core names that
  its honest instances make true (`HonF.res`, discharged in `EndExecCoreRes`).
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.Res.FamDefs

/-!
# Residual families on core names

A heap certificate (`HCert.res`) lists statements on core names (`CRes`) its witnesses use. The core
route takes a function's residuals when each is of a family (`resFam`), a decidable check on the
function's own code whose soundness at its honest instances is proved once, in `EndExecCoreRes`
(`resFam_sound`), from the instance's path:

* `rc`: `e(x) < n` (`.lt (.val x) (.num n)`), the value `x` range checked on every returning path
  against a constant `g^(N - 1)`, `N ≤ n` (`Res.rcBound` of the top-level atoms, `Res.topAtoms`);
* `sel`: the same, `x` a top-level selector of `m ≤ n` arms (`Res.topSels`);
* `under g r`: a residual of a family, the branch conditions `g` aside.

`resOk Cf`: every residual of `Cf`'s heap certificate of a family. `CfOk` asks it, so the core
route's honest valuations (`HonF.res`) make the residuals true.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **A residual of a family**, read off the function's own body: an exponent bound of a value range
checked (`rc`) or a selector (`sel`) on every returning path, or such a residual under branch
conditions. -/
noncomputable def resFam (body : List Stmt) : CRes → Bool
  | .lt (.val x) (.num n) => decide (n < capE) &&
      ((match Res.rcBound (Res.topAtoms body) (V.n x) with
        | some N => decide (N ≤ n)
        | none => false) ||
        (Res.topSels body).any fun p ↦ decide (p.1 = V.n x) && decide (p.2 ≤ n))
  | .under _ r => resFam body r
  | _ => false

/-- **Every residual of the function's heap certificate of a family.** -/
noncomputable def resOk (Cf : CFun) : Bool := Cf.H.res.all (resFam Cf.fn.body)

theorem resOk_nil {Cf : CFun} (h : Cf.H.res = []) : resOk Cf = true := by
  simp [resOk, h]

end

end LeanVM.Guest.CoreMode
