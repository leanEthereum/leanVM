module

@[expose] public section

/-!
# The clock circuit's reference

The word-level function the clock circuit of `crates/leanvm_core/src/tables/clock.rs` (§sec:clock of
`doc/leanvm/body/06-bus-interactions.tex`) computes, in the circuit's own conventions. Its input ports are the row's
clock `ts`, whose port has wires at bits 5 to 40 only (so `ts < 2^41` and `2^5 ∣ ts`), and the previous timestamp of
each access, 41 bits each; its output port `step` has 42 bits.

For an access in slot `k` the circuit takes the carry out of bit 39 of `(ts | k) + !prev` over the low 40 bits, set
exactly when `prev mod 2^40 < ts mod 2^40 + k` (`ordered`). The row fails when it is live and some access is out of
order, or it is live and has no access at all (the circuit's conjunction of no carries is zero), or some access's
previous timestamp has the other live bit (`fail`). The step holds the carries of `ts / 2^5 + live` from bit 5, so
that `ts XOR step` is the clock one cycle on, and the verdict at bit 41 (`step`).

Rust's `Clock::step` agrees with `step` whenever the row has an access; on a row with none it does not fail a live
row. Every production slot list is nonempty.
-/

namespace LeanVMCircuits.Clock

/-- The live bit of a timestamp, bit 40. -/
def live (ts : Nat) : Bool := ts.testBit 40

/-- The order check of an access in slot `slot` with previous timestamp `prev`: the carry out of bit 39 of
`(ts | slot) + !prev` over the low 40 bits. -/
def ordered (ts prev slot : Nat) : Bool := decide (prev % 2 ^ 40 < ts % 2 ^ 40 + slot)

/-- An access's previous timestamp has the other live bit. -/
def disagrees (ts prev : Nat) : Bool := prev.testBit 40 != ts.testBit 40

/-- The verdict at bit 41 of the step: a live row with no access or an access out of order, or a previous timestamp
with the other live bit. -/
def fail (slots prev : List Nat) (ts : Nat) : Bool :=
  (live ts && !(!slots.isEmpty && (prev.zip slots).all fun ps => ordered ts ps.1 ps.2)) ||
    prev.any fun p => disagrees ts p

/-- The step port: bits 5 to 40 the carries of `ts / 2^5 + live`, bit 41 the verdict. -/
def step (slots prev : List Nat) (ts : Nat) : Nat :=
  (((ts / 2 ^ 5 + if live ts then 1 else 0) ^^^ (ts / 2 ^ 5)) % 2 ^ 36) * 2 ^ 5 +
    if fail slots prev ts then 2 ^ 41 else 0

/-- What a satisfied clock circuit on `slots` says of its ports, read as integers: the clock has bits 5 to 40 only, one
previous timestamp of 41 bits per slot, and the step is `step`. -/
def Holds (slots prev : List Nat) (ts stepPort : Nat) : Prop :=
  ts < 2 ^ 41 ∧ 2 ^ 5 ∣ ts ∧ prev.length = slots.length ∧ (∀ p ∈ prev, p < 2 ^ 41) ∧
    stepPort = step slots prev ts

end LeanVMCircuits.Clock

