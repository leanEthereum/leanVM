import LeanVM.Guest.B1.Merkle.CapLinks

/-!
# The link check rejects

`Linked` (`LeanVM.Guest.Ref.Link`) is `false` on a core function and a reference function that
differ: `verify_merkle_cap__L2` against the reference function at another depth, with a read
dropped, with a hash's input cells swapped, with one name for two cells, and with the branch's
blocks exchanged; `verify_merkle_cap__L4` against it without the zero branch's pins.
-/

namespace LeanVMTests.Guest.RefLink

open LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.Ref

/-- `verify_merkle_cap__L2`, the function the mutants are checked against. -/
noncomputable abbrev f := Fn.«verify_merkle_cap__L2».core

example : Linked f (capRef 2) = true := by decide +kernel

example : Linked f (capRef 3) = false := by decide +kernel

/-- The reference function at depth `d` (2 unless given), its commands changed by `g`. -/
def mutant (g : List (Cmd CapName) → List (Cmd CapName)) (d : ℕ := 2) : Func CapName :=
  { capRef d with body := g (capRef d).body }

/-- A name moved by `r` in a term. -/
def renameTm (r : CapName → CapName) : Tm CapName → Tm CapName
  | .v x => .v (r x)
  | .const w => .const w
  | .add a b => .add (renameTm r a) (renameTm r b)
  | .mul a b => .mul (renameTm r a) (renameTm r b)

/-- A command changed where it stands at the top of the body. -/
def mapCmd (g : Cmd CapName → Cmd CapName) : List (Cmd CapName) → List (Cmd CapName) := List.map g

example : Linked f (mutant List.tail) = false := by decide +kernel

example : Linked f (mutant (mapCmd fun
    | .hash2 l0 l1 r0 r1 o0 o1 => .hash2 r0 r1 l0 l1 o0 o1
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (mapCmd fun
    | .load d p off => .load (renameTm (fun x => if x = .runs 1 then .runs 0 else x) d) p off
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (mapCmd fun
    | .ifNz c z n => .ifNz c n z
    | c => c)) = false := by decide +kernel

example : Linked Fn.«verify_merkle_cap__L4».core (mutant (mapCmd fun
    | .ifNz c _ n => .ifNz c [] n
    | c => c) 4) = false := by decide +kernel

end LeanVMTests.Guest.RefLink
