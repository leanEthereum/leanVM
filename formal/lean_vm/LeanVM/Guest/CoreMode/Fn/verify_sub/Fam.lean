/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Fam

  `verify_sub`'s own residual families (`CoreMode/FnReg.lean`): its exponent family.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`verify_sub`'s values' exponent bounds** `(v, lo, hi)` (`EndExec.VsQ`): the tables' log-heights `dims[1..6]`
(`kb[2..7]`, `tau_keccak_g` the keccak table's again), the bus depth `g_bus_mu`, the table sumcheck's depth `g_zc_n`, the
stack's log `gmv` and less `20`, `size_sel`. -/
def vsPows : List (ℕ × ℕ × ℕ) :=
  [(val% «verify_sub» "kb[2]", 0, 30), (val% «verify_sub» "kb[3]", 0, 30), (val% «verify_sub» "kb[4]", 0, 30),
    (val% «verify_sub» "kb[5]", 0, 30), (val% «verify_sub» "kb[6]", 0, 30), (val% «verify_sub» "kb[7]", 9, 24),
    (val% «verify_sub» "tau_keccak_g", 9, 24), (val% «verify_sub» "g_bus_mu", 20, 33), (val% «verify_sub» "g_zc_n", 9, 33),
    (val% «verify_sub» "gmv", 20, 30), (val% «verify_sub» "size_sel", 0, 10)]

/-- `verify_sub`'s products naming one of its values: `size_sel = gmv·size_sel~0`. -/
def vsMuls : List ((ℕ × ℕ) × ℕ) := [((val% «verify_sub» "gmv", val% «verify_sub» "size_sel~0"), val% «verify_sub» "size_sel")]

/-- `verify_sub`'s orders `e(x) ≤ e(y) + c`. -/
def vsLes : List (ℕ × ℕ × ℕ) :=
  [(val% «verify_sub» "kb[7]", val% «verify_sub» "g_zc_n", 0), (val% «verify_sub» "tau_keccak_g", val% «verify_sub» "g_zc_n", 0),
    (val% «verify_sub» "gmv", val% «verify_sub» "size_sel", 20)]

/-- `verify_sub`'s cursors in its stream `[stream]·[0, 8192)`, each with room for `207` words. -/
def vsCurs : List ℕ := [val% «verify_sub» "cursor@2", val% «verify_sub» "cursor@3", val% «verify_sub» "cursor@4"]

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

/-- **`verify_sub`'s exponent family** (`Res.vsB` on core names): an order its bounds decide
(`vsLt`), a read `c < 207` words past a cursor inside its stream, either under branch conditions (`EndExec.vsExp_inst`). -/
def vsExp (fn : Fn) : CRes → Bool
  | .lt a b => fn.name == name% «verify_sub» && vsLt a b
  | .sub c q => fn.name == name% «verify_sub» && decide (q = ⟨⟨[(val% «verify_sub» "stream", 1)], 0⟩, 1, .num 0, .num 8192⟩) &&
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
