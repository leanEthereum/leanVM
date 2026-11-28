/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.Fam

  `keccak_layer`'s own residual family (`CoreMode/FnReg.lean`): its two dispatches' returned cursors, its point length.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.keccak_layer

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The dispatches' returned cursors**: in `keccak_layer__L{first}`, its values from the pack on offset by
`o = 20·first`, the cursor the dispatch on `step_g` returns (value `o + 790`) is `cursor·step_g^32·g^48` (values `7`,
`9`), and the one the dispatch on `rem_g` returns (`o + 803`) is that times `rem_g^2` (value `10`). -/
def retEqs (o : ℕ) : List CRes :=
  [.eq ⟨[(o + 790, 1)], 0⟩ ⟨[(7, 1), (9, 32)], 48⟩, .eq ⟨[(o + 803, 1)], 0⟩ ⟨[(7, 1), (9, 32), (10, 2)], 48⟩]

/-- **Its point length** `y_g` (value `8`), as its caller computes it (`EndExec.KlQ`): `y_g = step_g^16·rem_g`, and
`e(y_g) < n`, `e(step_g^16) < n`, `32 ≤ n < capE`. -/
def ygFam (r : CRes) : Bool :=
  decide (r = .eq ⟨[(8, 1)], 0⟩ ⟨[(9, 16), (10, 1)], 0⟩) || match r with
    | .lt (.val 8) (.num n) => Nat.ble 32 n && Nat.blt n capE
    | .lt (.mono c) (.num n) => decide (c = ⟨[(9, 16)], 0⟩) && Nat.ble 32 n && Nat.blt n capE
    | _ => false

/-- **Its family**: each specialization's returned cursors (`retEqs`), its point length (`ygFam`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) :=
  [(name% «keccak_layer__L0», fun _ r ↦ decide (r ∈ retEqs 0) || ygFam r),
    (name% «keccak_layer__L1», fun _ r ↦ decide (r ∈ retEqs 20) || ygFam r)]

end

end LeanVM.Guest.CoreMode.Own.keccak_layer
