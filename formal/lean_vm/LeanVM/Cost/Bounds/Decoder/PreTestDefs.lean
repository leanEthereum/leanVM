module

public import LeanVM.Guest.Fast.PreSig

/-!
# Bound: the precondition's test, its prices as definitions

The closed forms of `Bounds/Decoder/PreTest.lean`, and the shape of an entry of the
preconditions' table they hold at, as definitions of their own: the table's evaluation
(`Bounds/Decoder/PreTableShape.lean`) imports these and the table alone, none of the compiler or
the proofs.

Each price holds at exponents within `7` bits (the frame's offsets, the known words' exponents,
the memory bounds' cell counts: a power `g^o`, `o < 128`, read off the powers table costs `17`;
`psAt W = 5 + 73·W`, a power by squaring, is the entry table's), the price `R` of a memory read (the reader closure) and the price `B` of
one logarithm's bound (`powBelowC` at a bound `n ≤ 34`: the word's lane compared with the lanes
of `g^0, …, g^(n-1)`; `powBelow_cost` gives `B = 706`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Guest.Exec LeanVM.Guest.Fast

@[expose] public section

/-- A power `g^o` by squaring, `o < 2^W` (`powSq_cost`). -/
def psAt (W : ℕ) : ℕ := 5 + 73 * W

/-- The exponent of a known word (`Sym`): `0` for `zero`. -/
def symExp : Sym → ℕ
  | .zero => 0
  | .gp e => e
  | .fpg e => e

/-- The memory cells an entry's memory bounds check: one each. -/
def memCells (t : FnPre) : ℕ := t.mem.length

/-- **An entry's exponents within `W` bits**: the frame's offsets, the known words' exponents and
the memory bounds' cells below `2^W`, the logarithms' bounds at most `34` (`scanBound`: the lanes' scan serves them). -/
def FnPreWithin (W : ℕ) (t : FnPre) : Prop :=
  (∀ p ∈ t.env, p.1 < 2 ^ W ∧ symExp p.2 < 2 ^ W) ∧ (∀ p ∈ t.pre, p.1 < 2 ^ W ∧ p.2 ≤ 34) ∧
    (∀ m ∈ t.mem, m.1 < 2 ^ W ∧ m.2.1 < 2 ^ W ∧ m.2.2 ≤ 34)

/-- **The price of an entry's test** (`fnPreTestC`), its exponents within `7` bits (their powers
read off the powers table, `17` each), a memory read at most `R`, a logarithm's bound at most `B`:
per entry-environment check `R + 153`, per bound `R + B + 83`, per memory bound (one cell)
`2R + B + 181`, and `62`; `3` for an entry without a precondition. -/
def fnPrePrice (R B : ℕ) : Option FnPre → ℕ
  | none => 3
  | some t => (R + 153) * t.env.length + (R + B + 83) * t.pre.length +
      (2 * R + B + 181) * memCells t + 62

/-- **The deployed table's shape**, decided: at most one entry check and bound, at
most `99` bounds and memory bounds, exponents below `2^7`, logarithms' bounds at most `34`. -/
def fnPreShape (t : FnPre) : Bool :=
  decide (t.env.length ≤ 1) && decide (t.pre.length ≤ 1) &&
    decide (t.pre.length + memCells t ≤ 99) &&
    t.env.all (fun p ↦ decide (p.1 < 2 ^ 7) && decide (symExp p.2 < 2 ^ 7)) &&
    t.pre.all (fun p ↦ decide (p.1 < 2 ^ 7) && decide (p.2 ≤ 34)) &&
    t.mem.all (fun m ↦ decide (m.1 < 2 ^ 7) && decide (m.2.1 < 2 ^ 7) && decide (m.2.2 ≤ 34))

/-- Every entry of a table has the deployed shape. -/
def tableShape (T : Array (Option FnPre)) : Bool := T.toList.all fun o ↦ o.all fnPreShape

end

end LeanVM.Cost.Bounds
