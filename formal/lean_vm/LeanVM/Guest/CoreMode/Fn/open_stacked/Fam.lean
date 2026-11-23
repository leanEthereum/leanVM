/-
  LeanVM.Guest.CoreMode.Fn.open_stacked.Fam

  `open_stacked`'s own residual families (`CoreMode/FnReg.lean`): its rate values' exponent bounds and its read of a
  table at its rate selector.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.Fam.ExpCDefs
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.open_stacked

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Its specializations, one per stacked log-size. -/
def names : List String :=
  [name% «open_stacked__L0»,
    name% «open_stacked__L1»,
    name% «open_stacked__L10»,
    name% «open_stacked__L2»,
    name% «open_stacked__L3»,
    name% «open_stacked__L4»,
    name% «open_stacked__L5»,
    name% «open_stacked__L6»,
    name% «open_stacked__L7»,
    name% «open_stacked__L8»,
    name% «open_stacked__L9»]

/-- **`e(x) < n`, `x` a value its body pins below `n`** (`valExpB`: `level_rate`'s values, copied from a constant in
every arm of their top-level `match`). -/
noncomputable def expFam (fn : Fn) : CRes → Bool
  | .lt (.val x) (.num n) => Nat.blt n capE && valExpB fn.body (.n x) 0 n
  | _ => false

/-- A cell `[B]·[J]·g^o` among the cells `[B]·g^(o + t)`, `t < m`, `J` a top-level selector of `m ≤ 64` arms. -/
noncomputable def selPt (fn : Fn) (B J o : ℕ) (cs : List CCell) : Bool :=
  (Res.topSels fn.body).any fun p ↦ decide (p.1 = V.n J) && Nat.ble p.2 64 &&
    (List.range p.2).all fun t ↦ cs.contains ⟨[(B, 1)], o + t⟩

/-- **A read of a table at its rate selector** (`pos_totals[rate_sel]`): `selPt`, the selector either base. -/
noncomputable def selPts (fn : Fn) : CRes → Bool
  | .subP ⟨[(a, 1), (b, 1)], o⟩ cs => selPt fn a b o cs || selPt fn b a o cs
  | _ => false

/-- **Its families.** -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) :=
  names.map fun k ↦ (k, fun fn r ↦ expFam fn r || selPts fn r)

end

end LeanVM.Guest.CoreMode.Own.open_stacked
