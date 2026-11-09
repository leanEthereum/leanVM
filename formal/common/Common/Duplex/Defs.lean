module

public import Common.Eager
public import Common.Lemmas
public import Common.Keccak
public import Statement.RandomPermutation
public import Common.Duplex.Spec

@[expose] public section

/-!
# A duplex challenge derivation from a seeded state, with branches: definitions

A protocol derives the challenges of a root (`chalP`) by a duplex over a random function `F` on
states: `y₀ = F (first r iv)` from the label's hash `iv = H label`, then the branches
`y_j = F (next j y₀)`, `j = 1 … n - 1`, the challenges being `out y₀, …, out y_(n-1)`. LeanDA's
challenge over Keccak-f[1600] is read off the branches, its grind's nonces
(`membership_challenge` at `../../leanvm-rev`), whose `first`, `next`, `out` read and write lanes
of the state.

The **simulator** (`simImpl`) answers `F` for an adversary from a random oracle `G` of the roots
(through `ga r j`, the challenge `j` of root `r`): a fresh query at the state `first r iv`, or at a
state `next j y` registered after programming the answer `y` with the challenge `(r, 0)`, is
answered `build (G r j, w)` for a fresh `w`, and every other fresh query uniformly. It records a
*collision* (`bad`) when a fresh answer's capacity (`cap`) is one of the capacities seen so far
(the first states' among them) or that of the query, which is what can make the derived
challenges differ from `G`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Common
open Common.Duplex (GSpec hP gaP VSpec toV)

namespace Common.SeedDuplex

theorem ite_pos' {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}

namespace DuplexSpec

variable (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The challenge an answer carries. -/
def out (y : St) : Z := (D.build.symm y).1

end DuplexSpec

section Programs

variable [DecidableEq Msg] [DecidableEq St]

/-- An `F` query. -/
abbrev fQ (x : St) : OracleComp (Rom2 Msg Dg St) St :=
  liftM ((Rom2 Msg Dg St).query (.inr (.inr x)))

variable (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The indices of the branches, `1 … n - 1`. -/
def branchIdx (n : ℕ) : List (Fin n) := (List.finRange n).tail

/-- The challenges of the branches `js` from the first answer `y₀`. -/
def branchesP (y₀ : St) : List (Fin n) → OracleComp (Rom2 Msg Dg St) (List Z)
  | [] => pure []
  | j :: js => do
    let y ← fQ (Dg := Dg) (D.next j y₀)
    let zs ← branchesP y₀ js
    pure (D.out y :: zs)

/-- **The challenges of a root**, by the duplex over `F`. -/
def chalP (r : Root) : OracleComp (Rom2 Msg Dg St) (List Z) := do
  let iv ← hQ (St := St) D.label
  let y₀ ← fQ (Dg := Dg) (D.first r iv)
  let zs ← branchesP D y₀ (branchIdx n)
  pure (D.out y₀ :: zs)

end Programs

/-! ## The simulator -/

end Common.SeedDuplex
