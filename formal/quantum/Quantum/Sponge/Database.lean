module

public import VCVio.Quantum.Oracle.Compressed.Basic

@[expose] public section

/-!
# The Msponge's databases: tails, intermediate pairs, good databases

Section 5.3 of Alagic, Carolan, Majenz and Tokat (ePrint 2025/731). The sponge permutation is
`φ = ω_h ∘ σ_k' ∘ π ∘ σ_k` on `X × Z` (`Quantum.spongePerm`), with `π` a fixed permutation and
`h : Z → X`, `k, k' : X → Z` random functions, whose compressed oracles hold the databases `D.h`,
`D.k`, `D.k'` (VCVio's `Quantum.Database`). In the Msponge each absorbed block replaces the rate,
so one round from capacity `zp` on block `xp` is: add `D.k xp` to the capacity, apply `π` to get the
intermediate pair `(xi, zi)`, add `D.k' xi` to the capacity. `h` only acts on the rate, which the
next block overwrites, so the capacities an adversary can reach do not depend on `D.h`.

* `IsTail π D t z`: the blocks `t` lead from the initial capacity `0` to `z`, every round through
  points of `D.k` and `D.k'`;
* `IP π D`: the intermediate pairs, `π (xp, zp + D.k xp)` for a block `xp` of `D.k` and a capacity
  `zp` with a tail;
* `Good π D`: every capacity has at most one tail, and intermediate pairs have distinct rates.

The paper's `head` of a tail and the outputs a database reaches are defined with the predicates
that use them.
-/

namespace Quantum.Sponge

open Quantum

/-- The databases of the three random functions of the sponge permutation. -/
structure Dbs (X Z : Type) where
  /-- The database of `h : Z → X`, added into the rate after the round. -/
  h : Database Z X
  /-- The database of `k : X → Z`, added into the capacity before `π`. -/
  k : Database X Z
  /-- The database of `k' : X → Z`, added into the capacity after `π`. -/
  k' : Database X Z

variable {X Z : Type} [AddCommGroup Z]

/-- `IsTail π D t z`: absorbing the blocks `t` from capacity `0` reaches capacity `z`, each round
through a point of `D.k` and a point of `D.k'`. -/
inductive IsTail (π : Equiv.Perm (X × Z)) (D : Dbs X Z) : List X → Z → Prop
  /-- The empty tail reaches the initial capacity. -/
  | nil : IsTail π D [] 0
  /-- One more round, on block `xp`, from a capacity `zp` with tail `t`. -/
  | snoc {t : List X} {zp : Z} {xp xi : X} {a zi b : Z} :
      IsTail π D t zp → D.k xp = some a → π (xp, zp + a) = (xi, zi) → D.k' xi = some b →
      IsTail π D (t ++ [xp]) (zi + b)

/-- `z` has a tail: an adversary holding `D` knows blocks that reach capacity `z`. -/
def HasTail (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (z : Z) : Prop :=
  ∃ t, IsTail π D t z

/-- The intermediate pairs: `π (xp, zp + D.k xp)` for `xp` in `D.k` and `zp` with a tail, the
states a round reaches after `π` and before `k'`. -/
def IP (π : Equiv.Perm (X × Z)) (D : Dbs X Z) : Set (X × Z) :=
  {s | ∃ xp zp a, HasTail π D zp ∧ D.k xp = some a ∧ π (xp, zp + a) = s}

/-- A good database (Definition 5.11): every capacity has at most one tail, and distinct
intermediate pairs have distinct rates. -/
def Good (π : Equiv.Perm (X × Z)) (D : Dbs X Z) : Prop :=
  (∀ z t t', IsTail π D t z → IsTail π D t' z → t = t') ∧
    ∀ s ∈ IP π D, ∀ s' ∈ IP π D, s.1 = s'.1 → s = s'

/-- `D` extends `D'` on `k` and `k'`: every point of `D'.k`, `D'.k'` is a point of `D.k`, `D.k'`
with the same value. `h` plays no part in tails or intermediate pairs. -/
def Extends (D D' : Dbs X Z) : Prop :=
  (∀ x a, D'.k x = some a → D.k x = some a) ∧ ∀ x b, D'.k' x = some b → D.k' x = some b

/-! ## The permutation's tail counts -/

variable [Fintype Z] [DecidableEq X]

/-- How many capacities `z` the permutation sends from rate `x1` to rate `x2`:
`|π({x1} × Z) ∩ ({x2} × Z)|`. -/
def rateCount (π : Equiv.Perm (X × Z)) (x1 x2 : X) : ℕ :=
  (Finset.univ.filter fun z : Z ↦ (π (x1, z)).1 = x2).card

/-- How many capacities `w` the points `(x1, w)` and `(x2, w + d)` share their image's rate for. -/
def pairCount (π : Equiv.Perm (X × Z)) (x1 x2 : X) (d : Z) : ℕ :=
  (Finset.univ.filter fun w : Z ↦ (π (x1, w)).1 = (π (x2, w + d)).1).card

/-- A good permutation with bound `G` (Definition 5.8, with the pair condition the bad events of a
single query also need): no rate-to-rate count and no shared-rate count of two distinct point
families exceeds `G`. -/
structure PermGood (π : Equiv.Perm (X × Z)) (G : ℕ) : Prop where
  rate : ∀ x1 x2, rateCount π x1 x2 ≤ G
  pair : ∀ x1 x2 d, (x1, d) ≠ (x2, 0) → pairCount π x1 x2 d ≤ G

end Quantum.Sponge

end
