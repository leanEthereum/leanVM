import KeccakGkr.Encode
import KeccakGkr.Rmfe

/-!
# The statement and the claims

The prover has committed a column `Q`: for every step `(i, p)` (an instance `i` of a pack `p`)
and every slot `o`, a 64-bit lane. Slot `slotCube m ℓ` holds lane `ℓ` of the input of segment
`m`, segment `m` being the `D` rounds from round `D m`. The statement (`Statement`, equations
`keccak:eq:statement` and `keccak:eq:chain` of `doc/leanvm`, §`keccak:segments`) is that segment `0`, run from its committed input, ends on
segment `1`'s committed input in every step (`Chain`), and that the main protocol's values `v`
are the multilinear extensions of the output lanes at the step point.

A claim at level `e` (`Claim.Holds`, equation `keccak:eq:claim`) is a weighted sum of the bits of
the states after `e` rounds of each segment. The protocol carries a claim from level `D` down to
level `0`, where the states are committed.
-/

open Polynomial

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2]

/-- A bit, in the field. -/
def ι : ZMod 2 →+* E := ZMod.castHom (dvd_refl 2) E

/-- The committed column: bit `z` of slot `o` in step `(i, p)`. -/
abbrev Column (n : ℕ) := Cube 4 → Cube n → Cube 6 → Slice → ZMod 2

section

variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n)

/-- Segment `m`'s committed input in step `(i, p)`. -/
def segInput (m : Bool) (i : Cube 4) (p : Cube n) : State := fun j => Q i p (slotCube m j.1) j.2

/-- The state after `e` rounds of segment `m` in step `(i, p)`. -/
def segState (m : Bool) (e : ℕ) (i : Cube 4) (p : Cube n) : State :=
  P.rounds (D * m.toNat) e (segInput Q m i p)

/-- The first segment ends on the second's committed input. -/
def Chain : Prop := ∀ i p, segState P D Q false D i p = segInput Q true i p

/-- Lane `ℓ` of a state as a word: bit `z` weighs `x ^ z`. -/
def word (x : E) (s : State) (ℓ : Lane) : E := ∑ z : Slice, ι (s (ℓ, z)) * x ^ z.val

/-- The multilinear extension of a table on steps, at `(rl, rp)`. -/
def mleStep (f : Cube 4 → Cube n → E) (rl : Fin 4 → E) (rp : Fin n → E) : E :=
  ∑ i, ∑ p, eqPoly rl (toPt i) * eqPoly rp (toPt p) * f i p

/-- Lane `ℓ` of the permutation's output, at the step point. -/
def outEval (x : E) (ℓ : Lane) (rl : Fin 4 → E) (rp : Fin n → E) : E :=
  mleStep (fun i p => word x (segState P D Q true D i p) ℓ) rl rp

/-- Equations `keccak:eq:statement` and `keccak:eq:chain`. -/
def Statement (x : E) (rl : Fin 4 → E) (rp : Fin n → E) (v : Lane → E) : Prop :=
  Chain P D Q ∧ ∀ ℓ, v ℓ = outEval P D Q x ℓ rl rp

/-- The committed lane in slot `o` of step `(i, p)`, as a word. -/
def colWord (x : E) (i : Cube 4) (p : Cube n) (o : Cube 6) : E :=
  ∑ z : Slice, ι (Q i p o z) * x ^ z.val

/-- The multilinear extension of the committed column, as words. -/
def colEval (x : E) (rl : Fin 4 → E) (rp : Fin n → E) (ro : Fin 6 → E) : E :=
  ∑ o, eqPoly ro (toPt o) * mleStep (fun i p => colWord Q x i p o) rl rp

/-- The multilinear extension of bit slice `z` of the committed column. -/
def sliceEval (z : Slice) (rl : Fin 4 → E) (rp : Fin n → E) (ro : Fin 6 → E) : E :=
  ∑ o, eqPoly ro (toPt o) * mleStep (fun i p => ι (Q i p o z)) rl rp

end

/-- A claim: a value, instance weights, a point (the pack, then the segment as the last
coordinate) and position weights. -/
structure Claim (E : Type) (n : ℕ) where
  c : E
  μ : Cube 4 → E
  r : Fin (n + 1) → E
  w : Pos → E

section

variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n)

/-- The value a claim at level `e` asserts: equation `keccak:eq:claim`. -/
def claimValue (e : ℕ) (μ : Cube 4 → E) (r : Fin (n + 1) → E) (w : Pos → E) : E :=
  ∑ y : Cube (n + 1), eqPoly r (toPt y) *
    ∑ i, μ i * ∑ j, w j * ι (segState P D Q (y (Fin.last n)) e i (Fin.init y) j)

/-- The claim holds at level `e`. -/
def Claim.Holds (e : ℕ) (cl : Claim E n) : Prop := cl.c = claimValue P D Q e cl.μ cl.r cl.w

end

end KeccakGkr
