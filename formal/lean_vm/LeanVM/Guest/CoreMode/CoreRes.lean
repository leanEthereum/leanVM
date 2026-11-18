/-
  LeanVM.Guest.CoreMode.CoreRes

  The residuals the core route takes, by family: a heap certificate's statements on core names that
  its honest instances make true (`HonF.res`, discharged in `EndExecCoreRes`).
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.Res.FamDefs
public import LeanVM.Guest.B1.Selectors.ColumnSelector

/-!
# Residual families on core names

A heap certificate (`HCert.res`) lists statements on core names (`CRes`) its witnesses use. The core
route takes a function's residuals when each is of a family (`resFam`), a decidable check on the
function's own code whose soundness at its honest instances is proved once, in `EndExecCoreRes`
(`resFam_inst`):

* `rc`: `e(x) < n` (`.lt (.val x) (.num n)`), the value `x` range checked on every returning path
  against a constant `g^(N - 1)`, `N ≤ n` (`Res.rcBound` of the top-level atoms, `Res.topAtoms`), from
  the instance's path;
* `sel`: the same, `x` a top-level selector of `m ≤ n` arms (`Res.topSels`), from its path;
* `cs`: `column_selector__L{κ}`'s read of its lowest digit's entry lies in the strided table its
  callers write (`csSub κ`), from the offset its callers hand it (the old route's F3 on names);
* `under g r`: a residual of a family, the branch conditions `g` aside.

`resOk Cf`: every residual of `Cf`'s heap certificate of a family. `CfOk` asks it, so the core
route's honest valuations (`HonF.res`) make the residuals true.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`column_selector__L{κ}`'s lowest digit in its strided table** (F3 on names): the cell
`[sel_eq]·[digit₀]·g^off` one of the run `⟨[sel_eq]·g^off, 2^(4-w), 0, 2^w⟩`, `w` the digit's width,
`sel_eq` parameter `1` and the digit value `3`. -/
def csSub (κ : ℕ) : CRes :=
  .sub ⟨[(1, 1), (3, 1)], 64 * (κ / 4) + 16 * (B1.Tables.csW κ 0 - 1)⟩
    ⟨⟨[(1, 1)], 64 * (κ / 4) + 16 * (B1.Tables.csW κ 0 - 1)⟩, 2 ^ (4 - B1.Tables.csW κ 0), .num 0,
      .num (2 ^ B1.Tables.csW κ 0)⟩

/-- **A residual of a family**, read off the function's own code: an exponent bound of a value range
checked (`rc`) or a selector (`sel`) on every returning path, `column_selector`'s lowest digit (`cs`),
or such a residual under branch conditions. -/
noncomputable def resFam (fn : Fn) : CRes → Bool
  | .lt (.val x) (.num n) => decide (n < capE) &&
      ((match Res.rcBound (Res.topAtoms fn.body) (V.n x) with
        | some N => decide (N ≤ n)
        | none => false) ||
        (Res.topSels fn.body).any fun p ↦ decide (p.1 = V.n x) && decide (p.2 ≤ n))
  | .sub c q => (List.range 31).any fun κ ↦ fn.name == B1.Tables.lName "column_selector" κ &&
      decide (CRes.sub c q = csSub κ)
  | .under _ r => resFam fn r
  | _ => false

/-- **Every residual of the function's heap certificate of a family.** -/
noncomputable def resOk (Cf : CFun) : Bool := Cf.H.res.all (resFam Cf.fn)

theorem resOk_nil {Cf : CFun} (h : Cf.H.res = []) : resOk Cf = true := by
  simp [resOk, h]

end

end LeanVM.Guest.CoreMode
