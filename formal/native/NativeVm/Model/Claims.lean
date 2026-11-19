module

public import NativeVm.Model.Layout

/-!
# The claims the phases hand on

The statement's claims carry functions; here each is data and an evaluation:

* `ColumnClaimW` is `ColumnClaim`: a global column, a point over its own variables, a value.
* `StackClaimW` is `StackClaim = (List E → E) × E`, its weight function defunctionalized
  (`StackWeight`): `eq z` is `fun x ↦ eqEval z x` (the stack's out-of-domain claim, `readOod`, and
  a column claim on the stack, `ColumnClaim.onStack`, `z` its `Placement.stackPoint`), and
  `ring p r c` is `ringSwitchClaim`'s weight, `fun x ↦ p.eqAbove x * ringWeight r (x.take
  p.variableCount) c`. `StackWeight.eval` applies it.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- A column claim (`ColumnClaim`). -/
structure ColumnClaimW where
  column : Nat
  point : Array EW
  value : EW
  deriving Inhabited

/-- `ring_weight(r, r_prime, coefficients)`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`. -/
def ringWeight (r rPrime coefficients : Array EW) : EW :=
  (coefficients.foldl (fun (acc : EW × Array EW) c ↦
    let product := (acc.2.zip rPrime).foldl
      (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
    (acc.1 + product, acc.2.map fun value ↦ value * value)) (0, r)).1

/-- A stack claim's weight function, as data. -/
inductive StackWeight where
  /-- `fun x ↦ eqEval z x`. -/
  | eq (z : Array EW)
  /-- `fun x ↦ p.eqAbove x * ringWeight r (x.take p.variableCount) c`. -/
  | ring (p : Placement) (r c : Array EW)
  deriving Inhabited

/-- The weight at a point of the stack. -/
def StackWeight.eval : StackWeight → Array EW → EW
  | .eq z, x => eqEval z x
  | .ring p r c, x => eqAbove p x * ringWeight r (x.extract 0 p.variableCount) c

/-- A claim on the stack (`StackClaim`): its weight and its value. -/
structure StackClaimW where
  weight : StackWeight
  value : EW
  deriving Inhabited

/-- `ColumnClaim.onStack`: the claim as an equality weight on the stack, `none` for a column with
no placement. -/
def ColumnClaimW.onStack (c : ColumnClaimW) (layout : LayoutW) : Option StackClaimW :=
  ((layout.placements[c.column]?).getD none).map fun placement ↦
    ⟨.eq (stackPoint placement c.point layout.stackLog), c.value⟩

end NativeVm.Model
