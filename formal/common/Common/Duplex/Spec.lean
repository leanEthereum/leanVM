module

public import Common.Sponge
public import Common.SimDefs
public import Statement.RandomPermutation

@[expose] public section

/-!
# A duplex challenge derivation from a seeded state, with branches: the derivation and its simulator

The duplex of `Common.Duplex` (`Common.SimDefs`) shares the answer `y₀` of the label's state among
the roots, a root absorbed after it. This one starts each root's derivation at a state of its own,
`first r iv` from the label's hash `iv`, and branches from its answer: `y₀ = F (first r iv)`, then
`y_j = F (next j y₀)` for `j = 1 … n - 1`, each branch's state written over the rate of `y₀` and
keeping its capacity. LeanDA derives its challenge so (`membership_challenge`,
`verifier/src/da.rs:20-34` at `../../leanvm-rev`: the transcript seeded with the label's hash and
the root, then a grind whose nonce `j - 1` is absorbed into a copy of the seeded sponge, branch
`j`). The first states share the capacity of `init iv`. The simulator recognises a root's first
state from the label's hash (`dec iv x`), which it records when the label is hashed, and the
branches of a root once it has programmed the root's first answer.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common
open Common.Duplex (GSpec hP gaP)

namespace Common.SeedDuplex

/-- **A duplex challenge derivation** with `n` challenges: the label, a state of the first
states' capacity (`init`), the first state of a root's derivation from the label's hash
(`first`), the state of branch `j` from the first answer (`next j`), the answers as a challenge
and the rest (`build`), the capacity of the rest (`capW`), and the recognition of the first
states (`dec`). -/
structure DuplexSpec (Msg Dg St Root Z W Cp : Type) (n : ℕ) where
  /-- The label whose hash seeds the derivations. -/
  label : Msg
  /-- A state with the capacity of the first states, from the label's hash. -/
  init : Dg → St
  /-- The first state of a root's derivation, from the label's hash. -/
  first : Root → Dg → St
  /-- The state of branch `j` (`0 < j`) from the first answer. -/
  next : Fin n → St → St
  /-- An answer from its challenge and its rest. -/
  build : Z × W ≃ St
  /-- The capacity of a rest. -/
  capW : W → Cp
  /-- The root whose derivation a state starts, from the label's hash, if any. -/
  dec : Dg → St → Option Root
  dec_iff : ∀ d x r, dec d x = some r ↔ first r d = x
  /-- There is at least one challenge. -/
  n_pos : 0 < n
  /-- The first states have the capacity of `init`. -/
  cap_first : ∀ r d, capW (build.symm (first r d)).2 = capW (build.symm (init d)).2
  /-- A branch keeps the first answer's capacity. -/
  cap_next : ∀ j y, capW (build.symm (next j y)).2 = capW (build.symm y).2
  /-- Different branches of one answer have different states. -/
  next_inj : ∀ j j' y, j.val ≠ 0 → j'.val ≠ 0 → next j y = next j' y → j = j'

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}

namespace DuplexSpec

variable (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The capacity of a state. -/
def cap (x : St) : Cp := D.capW (D.build.symm x).2

end DuplexSpec

/-- The two-oracle random-oracle model: coins, `H` and `F`. -/
abbrev Rom2 (Msg Dg St : Type) := unifSpec + hfSpec Msg Dg St

section Programs

variable [DecidableEq Msg] [DecidableEq St]

/-- An `H` query. -/
abbrev hQ (m : Msg) : OracleComp (Rom2 Msg Dg St) Dg :=
  liftM ((Rom2 Msg Dg St).query (.inr (.inl m)))

variable (D : DuplexSpec Msg Dg St Root Z W Cp n)

end Programs

/-- The simulator's state: the answered states with their answers and the challenge they were
programmed with, newest first; the registered branches; the state `init`
of the label's hash and the hash, once known; the collision flag. -/
structure SimSt (Dg St Root : Type) (n : ℕ) where
  log : List (St × St × Option (Root × Fin n))
  lab : List (St × (Root × Fin n))
  x0 : Option St
  iv : Option Dg
  bad : Bool

/-- The initial simulator state. -/
def SimSt.init : SimSt Dg St Root n := ⟨[], [], none, none, false⟩

section Sim

variable [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The recorded answer at a state. -/
def SimSt.answer (s : SimSt Dg St Root n) (x : St) : Option St :=
  (s.log.find? (·.1 = x)).map (·.2.1)

/-- The challenges used for programming. -/
def SimSt.used (s : SimSt Dg St Root n) : List (Root × Fin n) := s.log.filterMap (·.2.2)

/-- The registered challenge of a branch state. -/
def SimSt.labOf (s : SimSt Dg St Root n) (x : St) : Option (Root × Fin n) :=
  (s.lab.find? (·.1 = x)).map (·.2)

/-- **The challenge a fresh state would be programmed with**: `(r, 0)` at `first r iv`; else its
registered one. -/
def efflab (s : SimSt Dg St Root n) (x : St) : Option (Root × Fin n) :=
  match s.iv with
    | some d => match D.dec d x with
      | some r => some (r, ⟨0, D.n_pos⟩)
      | none => s.labOf x
    | none => s.labOf x

/-- The capacities seen: of the answered states, of their answers, and of the first
states. -/
def forb (s : SimSt Dg St Root n) : Finset Cp :=
  (s.log.map (D.cap ·.1) ++ s.log.map (D.cap ·.2.1) ++ s.x0.toList.map D.cap).toFinset

/-- The branches of the root `r` from its first answer `y`, each with its challenge. -/
def children (r : Root) (y : St) : List (St × (Root × Fin n)) :=
  ((List.finRange n).filter fun j ↦ j.val ≠ 0).map fun j ↦ (D.next j y, (r, j))

/-- The state after answering the fresh state `x` with `y`, programmed with `lbl`: programming a
root's first answer registers its branches. -/
def SimSt.record (s : SimSt Dg St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    SimSt Dg St Root n where
  log := (x, y, lbl) :: s.log
  lab := match lbl with
    | some (r, j) => if j.val = 0 then children D r y ++ s.lab else s.lab
    | none => s.lab
  x0 := s.x0
  iv := s.iv
  bad := s.bad || decide (D.cap y ∈ insert (D.cap x) (forb D s))

variable {ι' : Type} {hs' : OracleSpec ι'} [SampleableType St] [SampleableType W]
  (hQ' : Msg → OracleComp (unifSpec + hs') Dg) (ga : Root → Fin n → OracleComp (unifSpec + hs') Z)

/-- The answer and challenge of a fresh state. -/
noncomputable def freshAns (s : SimSt Dg St Root n) (x : St) :
    OracleComp (unifSpec + hs') (St × Option (Root × Fin n)) :=
  match efflab D s x with
  | some (r, j) =>
    if (r, j) ∈ s.used then (·, none) <$> (liftM ($ᵗ St) : OracleComp (unifSpec + hs') St)
    else do
      let z ← ga r j
      let w ← (liftM ($ᵗ W) : OracleComp (unifSpec + hs') W)
      pure (D.build (z, w), some (r, j))
  | none => (·, none) <$> (liftM ($ᵗ St) : OracleComp (unifSpec + hs') St)

/-- **The simulator** of `F`, forwarding coins and `H` (and recording the label's hash and `init`
of it when the label is hashed). -/
noncomputable def simImpl [DecidableEq Msg] :
    QueryImpl (Rom2 Msg Dg St) (StateT (SimSt Dg St Root n) (OracleComp (unifSpec + hs')))
  | .inl k => liftM (liftM (unifSpec.query k : ProbComp (Fin (k + 1))) :
      OracleComp (unifSpec + hs') (Fin (k + 1)))
  | .inr (.inl m) => StateT.mk fun s ↦ do
      let d ← hQ' m
      pure (d, if m = D.label then { s with x0 := some (D.init d), iv := some d } else s)
  | .inr (.inr x) => StateT.mk fun s ↦
      match s.answer x with
      | some y => pure (y, s)
      | none => do
        let a ← freshAns D ga s x
        pure (a.1, s.record D x a.1 a.2)

end Sim

end Common.SeedDuplex

end
