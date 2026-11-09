module

public import Common.Sponge
public import Statement.RandomPermutation

@[expose] public section

/-!
# The simulators of the two-oracle random-oracle model

The two-oracle simulator (`simulator2`) and the simulated adversary (`advS2`), the duplex and its
simulator (`Duplex.DuplexSpec`, `Duplex.simImpl`), the challenges as a random oracle (`Duplex.GSpec`)
and as one random oracle of vectors (`Duplex.toV`): the definitions of the proofs' random-oracle
models, moved here from `Statement/RandomPermutation.lean` since no end statement names them.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- The answer of the two-oracle simulator at a fresh rooted node `x` with path `β`: when `β`
pads a message `m`, `H m` completed by uniform bits; otherwise `F x`. -/
noncomputable def rootedAnswer2 (β : List (Dg × E)) (x : SpState Dg E C) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) (SpState Dg E C) :=
  match P.unpad β with
  | some m => do
    let d ← hQuery (E := E) (C := C) m
    let ec ← (liftM ($ᵗ (E × C)) : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
    pure ((d, ec.1), ec.2)
  | none => fQuery (Dg := Dg) x

/-- **The two-oracle simulator**: answers `π` and `π⁻¹` with oracle access to `H` and `F`. -/
noncomputable def simulator2 : QueryImpl (permutationOracleSpec (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .forward x => StateT.mk fun σ ↦
      match forwardLookup σ.edges x with
      | some y => pure (y, σ)
      | none =>
        match chainOf σ.chains x with
        | some (s, β) => do
          let y ← rootedAnswer2 P (β ++ [blockTo s x]) x
          pure (y, ⟨(x, y) :: σ.edges, (y, β ++ [blockTo s x]) :: σ.chains⟩)
        | none => do
          let y ← fQuery (Dg := Dg) x
          pure (y, ⟨(x, y) :: σ.edges, σ.chains⟩)
  | .inverse y => StateT.mk fun σ ↦
      match inverseLookup σ.edges y with
      | some x => pure (x, σ)
      | none => do
        let x ← (liftM ($ᵗ (SpState Dg E C)) :
          OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
        pure (x, ⟨(x, y) :: σ.edges, σ.chains⟩)

end Setting

section Setting2

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- The adversary's oracles in the two-oracle ROM: coins, `H`, and `π`, `π⁻¹` answered by the
simulator `simulator2` (which queries `H` and `F`). -/
noncomputable def advImpl2 : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
  | .inr (.inl m) => liftM (hQuery (Msg := Msg) (Dg := Dg) (E := E) (C := C) m)
  | .inr (.inr q) => simulator2 P q

/-- **The ROM adversary of an RPM adversary** in the two-oracle model. -/
noncomputable def advS2 {α : Type} (A : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) α :=
  (simulateQ (advImpl2 P) A).run' (SimState.init iv)

end Setting2

end Common

/-! ## Named by LeanDA's code-binding bound: the duplex and its simulator -/

section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common.Duplex

/-- **A duplex challenge derivation** with `n` challenges: the label and the initial state, the
absorption of a root (`first`), the step (`next`), the answers as a challenge and the rest
(`build`), the capacity of the rest (`capW`), and the recognition of absorbed roots (`dec`). -/
structure DuplexSpec (Msg Dg St Root Z W Cp : Type) (n : ℕ) where
  /-- The label whose hash seeds the initial state. -/
  label : Msg
  /-- The initial state from the label's hash. -/
  init : Dg → St
  /-- The state absorbing a root after the answer `y₀`. -/
  first : Root → St → St
  /-- The state after an answer, absorbing nothing. -/
  next : St → St
  /-- An answer from its challenge and its rest. -/
  build : Z × W ≃ St
  /-- The capacity of a rest. -/
  capW : W → Cp
  /-- The root a state absorbs after `y₀`, if any. -/
  dec : St → St → Option Root
  dec_iff : ∀ y x r, dec y x = some r ↔ first r y = x
  /-- There is at least one challenge. -/
  n_pos : 0 < n
  /-- Absorbing a root keeps the capacity. -/
  cap_first : ∀ r y, capW (build.symm (first r y)).2 = capW (build.symm y).2
  /-- A step keeps the capacity. -/
  cap_next : ∀ y, capW (build.symm (next y)).2 = capW (build.symm y).2

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
programmed with, newest first; the registered steps of the challenge chains; the initial state
and its answer once known; the collision flag. -/
structure SimSt (St Root : Type) (n : ℕ) where
  log : List (St × St × Option (Root × Fin n))
  lab : List (St × (Root × Fin n))
  x0 : Option St
  y0 : Option St
  bad : Bool

/-- The initial simulator state. -/
def SimSt.init : SimSt St Root n := ⟨[], [], none, none, false⟩

section Sim

variable [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The recorded answer at a state. -/
def SimSt.answer (s : SimSt St Root n) (x : St) : Option St :=
  (s.log.find? (·.1 = x)).map (·.2.1)

/-- The challenges used for programming. -/
def SimSt.used (s : SimSt St Root n) : List (Root × Fin n) := s.log.filterMap (·.2.2)

/-- The registered challenge of a chain state. -/
def SimSt.labOf (s : SimSt St Root n) (x : St) : Option (Root × Fin n) :=
  (s.lab.find? (·.1 = x)).map (·.2)

/-- **The challenge a fresh state would be programmed with**: none at the initial state; `(r, 0)`
at `first r y₀`; else its registered one. -/
def efflab (s : SimSt St Root n) (x : St) : Option (Root × Fin n) :=
  if s.x0 = some x then none
  else match s.y0 with
    | some v => match D.dec v x with
      | some r => some (r, ⟨0, D.n_pos⟩)
      | none => s.labOf x
    | none => s.labOf x

/-- The capacities seen: of the answered states, of their answers, and of the initial state. -/
def forb (s : SimSt St Root n) : Finset Cp :=
  (s.log.map (D.cap ·.1) ++ s.log.map (D.cap ·.2.1) ++ s.x0.toList.map D.cap).toFinset

/-- The state after answering the fresh state `x` with `y`, programmed with `lbl`. -/
def SimSt.record (s : SimSt St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    SimSt St Root n where
  log := (x, y, lbl) :: s.log
  lab := match lbl with
    | some (r, j) =>
      if h : j.val + 1 < n then
        if s.labOf (D.next y) = none then (D.next y, (r, ⟨j.val + 1, h⟩)) :: s.lab else s.lab
      else s.lab
    | none => s.lab
  x0 := s.x0
  y0 := if s.x0 = some x then some y else s.y0
  bad := s.bad || decide (D.cap y ∈ insert (D.cap x) (forb D s))

variable {ι' : Type} {hs' : OracleSpec ι'} [SampleableType St] [SampleableType W]
  (hQ' : Msg → OracleComp (unifSpec + hs') Dg) (ga : Root → Fin n → OracleComp (unifSpec + hs') Z)

/-- The answer and challenge of a fresh state. -/
noncomputable def freshAns (s : SimSt St Root n) (x : St) :
    OracleComp (unifSpec + hs') (St × Option (Root × Fin n)) :=
  match efflab D s x with
  | some (r, j) =>
    if (r, j) ∈ s.used then (·, none) <$> (liftM ($ᵗ St) : OracleComp (unifSpec + hs') St)
    else do
      let z ← ga r j
      let w ← (liftM ($ᵗ W) : OracleComp (unifSpec + hs') W)
      pure (D.build (z, w), some (r, j))
  | none => (·, none) <$> (liftM ($ᵗ St) : OracleComp (unifSpec + hs') St)

/-- **The simulator** of `F`, forwarding coins and `H` (and recording the initial state when the
label is hashed). -/
noncomputable def simImpl [DecidableEq Msg] :
    QueryImpl (Rom2 Msg Dg St) (StateT (SimSt St Root n) (OracleComp (unifSpec + hs')))
  | .inl k => liftM (liftM (unifSpec.query k : ProbComp (Fin (k + 1))) :
      OracleComp (unifSpec + hs') (Fin (k + 1)))
  | .inr (.inl m) => StateT.mk fun s ↦ do
      let d ← hQ' m
      pure (d, if m = D.label then { s with x0 := some (D.init d) } else s)
  | .inr (.inr x) => StateT.mk fun s ↦
      match s.answer x with
      | some y => pure (y, s)
      | none => do
        let a ← freshAns D ga s x
        pure (a.1, s.record D x a.1 a.2)

end Sim

end Common.Duplex

end

/-! ## Named by LeanDA's code-binding bound: the challenges as a random oracle -/

section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common.Duplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The oracles of the simulated world: coins, `H`, and the challenges `G` on `(r, j)`. -/
abbrev GSpec (Msg Dg Root Z : Type) (n : ℕ) := roSpec Msg Dg + (Root × Fin n →ₒ Z)

/-- `H` in the simulated world. -/
abbrev hP (m : Msg) : OracleComp (unifSpec + GSpec Msg Dg Root Z n) Dg :=
  liftM ((unifSpec + GSpec Msg Dg Root Z n).query (.inr (.inl m)))

/-- A challenge in the simulated world. -/
abbrev gaP (r : Root) (j : Fin n) : OracleComp (unifSpec + GSpec Msg Dg Root Z n) Z :=
  liftM ((unifSpec + GSpec Msg Dg Root Z n).query (.inr (.inr (r, j))))

end Common.Duplex

end

/-! ## Named by LeanDA's code-binding bound: the challenges as one random oracle of vectors -/

section

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open scoped ENNReal

namespace Common

section Swap

variable {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂] {hs₁ : OracleSpec.{0, 0} ι₁}
  {hs₂ : OracleSpec.{0, 0} ι₂} [∀ t : hs₁.Domain, SampleableType (hs₁.Range t)]
  [∀ t : hs₂.Domain, SampleableType (hs₂.Range t)]

/-- The oracles of a sum, in the other order. -/
def swapImpl : QueryImpl (unifSpec + (hs₁ + hs₂)) (OracleComp (unifSpec + (hs₂ + hs₁)))
  | .inl k => liftM ((unifSpec + (hs₂ + hs₁)).query (.inl k))
  | .inr (.inl t) => liftM ((unifSpec + (hs₂ + hs₁)).query (.inr (.inr t)))
  | .inr (.inr t) => liftM ((unifSpec + (hs₂ + hs₁)).query (.inr (.inl t)))

end Swap

end Common

namespace Common.Duplex

variable {Msg Dg Root Z : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq Root] [SampleableType Dg] [SampleableType Z]
  [Fintype Z] [Fintype Root] [Nonempty Z]

/-- `H`, and the challenges as one random oracle of vectors. -/
abbrev VSpec (Msg Dg Root Z : Type) (n : ℕ) := roSpec Msg Dg + (Root →ₒ (Fin n → Z))

/-- The challenge `(r, j)` read as component `j` of the vector of `r`. -/
def toV : QueryImpl (unifSpec + GSpec Msg Dg Root Z n) (OracleComp (unifSpec + VSpec Msg Dg Root Z n))
  | .inl k => liftM ((unifSpec + VSpec Msg Dg Root Z n).query (.inl k))
  | .inr (.inl m) => liftM ((unifSpec + VSpec Msg Dg Root Z n).query (.inr (.inl m)))
  | .inr (.inr rj) =>
      (fun v ↦ v rj.2) <$> liftM ((unifSpec + VSpec Msg Dg Root Z n).query (.inr (.inr rj.1)))

end Common.Duplex

end
