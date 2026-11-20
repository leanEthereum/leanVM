/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Fam

  `verify_sub`'s own residual families (`CoreMode/FnReg.lean`): its exponent family.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`verify_sub`'s values' exponent bounds** `(v, lo, hi)` (`EndExec.VsQ`): the tables' log-heights `dims[1..6]`
(values `86..91`, `566` the keccak table's again), the bus depth `253`, the table sumcheck's depth `562`, the stack's log
`276` and less `20`, `278`. -/
def vsPows : List (ℕ × ℕ × ℕ) :=
  [(86, 0, 30), (87, 0, 30), (88, 0, 30), (89, 0, 30), (90, 0, 30), (91, 9, 24), (566, 9, 24), (253, 20, 33),
    (562, 9, 33), (276, 20, 30), (278, 0, 10)]

/-- `verify_sub`'s products naming one of its values: `278 = 276·277`. -/
def vsMuls : List ((ℕ × ℕ) × ℕ) := [((276, 277), 278)]

/-- `verify_sub`'s orders `e(x) ≤ e(y) + c`. -/
def vsLes : List (ℕ × ℕ × ℕ) := [(91, 562, 0), (566, 562, 0), (276, 278, 20)]

/-- `verify_sub`'s cursors in its stream `[25]·[0, 8192)`, each with room for `207` words. -/
def vsCurs : List ℕ := [550, 561, 578]

/-- **An index as `verify_sub`'s value times `g^c`**: the value (a product of `vsMuls` naming it) and `c`. -/
def vsBase : CIdx → Option (ℕ × ℕ)
  | .num _ => none
  | .val x => some (x, 0)
  | .mono c => match c.bases with
    | [(x, 1)] => some (x, c.off)
    | [(a, 1), (b, 1)] => (vsMuls.lookup (a, b)).map fun x ↦ (x, c.off)
    | _ => none

/-- An index's exponent bounds by `vsPows`. -/
def vsIv (i : CIdx) : Option (ℕ × ℕ) :=
  match i with
  | .num n => some (n, n)
  | _ => (vsBase i).bind fun p ↦ (vsPows.lookup p.1).map fun b ↦ (b.1 + p.2, b.2 + p.2)

/-- **An order of `verify_sub`'s exponents** its bounds or orders decide. -/
def vsLt (a b : CIdx) : Bool :=
  match vsIv a, vsIv b with
  | some (_, ha), some (lb, hb) => decide (ha < capE) && decide (hb < capE) && (decide (ha < lb) ||
      match vsBase a, vsBase b with
      | some (x, ca), some (y, cb) => vsLes.any fun l ↦ decide (l.1 = x ∧ l.2.1 = y ∧ ca + l.2.2 < cb)
      | _, _ => false)
  | _, _ => false

/-- **`verify_sub`'s exponent family** (the old route's `Res.vsB` on core names): an order its bounds decide
(`vsLt`), a read `c < 207` words past a cursor inside its stream, either under branch conditions (`EndExec.vsExp_inst`). -/
def vsExp (fn : Fn) : CRes → Bool
  | .lt a b => fn.name == name% «verify_sub» && vsLt a b
  | .sub c q => fn.name == name% «verify_sub» && decide (q = ⟨⟨[(25, 1)], 0⟩, 1, .num 0, .num 8192⟩) &&
      (match c.bases with
        | [(x, 1)] => vsCurs.contains x
        | _ => false) && decide (c.off < 207)
  | .under _ r => vsExp fn r
  | _ => false

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: its exponent family (`vsExp`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «verify_sub», vsExp)]

end

end LeanVM.Guest.CoreMode.Own.verify_sub
