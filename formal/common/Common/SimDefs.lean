module

public import Common.Sponge
public import Statement.RandomPermutation

@[expose] public section

/-!
# The simulators of the two-oracle random-oracle model

The two-oracle simulator (`simulator2`), the simulated adversary (`advS2`), and the challenges as a
random oracle (`Duplex.GSpec`).
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

/-! ## The challenges as a random oracle -/

namespace Common.Duplex

open OracleComp OracleSpec

variable {Msg Dg Root Z : Type} {n : ℕ}

/-- The oracles of the simulated world: coins, `H`, and the challenges `G` on `(r, j)`. -/
abbrev GSpec (Msg Dg Root Z : Type) (n : ℕ) := roSpec Msg Dg + (Root × Fin n →ₒ Z)

/-- `H` in the simulated world. -/
abbrev hP (m : Msg) : OracleComp (unifSpec + GSpec Msg Dg Root Z n) Dg :=
  liftM ((unifSpec + GSpec Msg Dg Root Z n).query (.inr (.inl m)))

/-- A challenge in the simulated world. -/
abbrev gaP (r : Root) (j : Fin n) : OracleComp (unifSpec + GSpec Msg Dg Root Z n) Z :=
  liftM ((unifSpec + GSpec Msg Dg Root Z n).query (.inr (.inr (r, j))))

end Common.Duplex
