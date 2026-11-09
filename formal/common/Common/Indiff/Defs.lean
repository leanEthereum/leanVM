module

public import Common.Sponge
public import Common.RomComm
public import Statement.RandomPermutation

@[expose] public section

/-!
# Indifferentiability: the two worlds and the simulator

The setting is the abstract sponge of `Common.Sponge` over states `(Dg × E) × C` (rate `Dg × E`,
digest `Dg`, capacity `C`), a padding `P` of messages `Msg` into rate blocks, and an initial state
`iv`.

A *distinguisher* is an oracle computation `D : OracleComp (dSpec Msg Dg St) α` with three kinds
of query (`dSpec`): uniform coins, the hash `H m`, and the permutation `π x`, `π⁻¹ y`.

* **The real world** (`realGame`): `π` is the lazily sampled random permutation `lazyRandomPermutation`, and
  `H` is the sponge over it (`spongeWith P iv π`), sharing its state.
* **The ideal world** (`idealGame`): `H` is a lazily sampled random oracle `Msg → Dg`
  (`romImpl`), and `π`, `π⁻¹` are answered by the simulator `simulator P`, which queries the
  random oracle.

## The simulator

The simulator (Bertoni, Daemen, Peeters, Van Assche, EUROCRYPT 2008, Section 4) keeps the
edges `(x, y)` it has answered (`SimState.edges`) and the *rooted* states with their paths
(`SimState.chains`): the initial state `iv` with the empty path, and every answer `y` to a
forward query at a rooted node, with the node's path. A state `x` is a rooted node when its
capacity equals the capacity of some rooted state `s` with path `β`; its path is then
`β ++ [B]` with `B = blockTo s x` the block taking `s` to `x` (`chainOf`). A fresh forward query
at a rooted node whose path is the padding of a message `m` is answered with the random oracle's
`H m` as digest, completed by uniform bits (`rootedAnswer`); any other fresh query, forward or
inverse, is answered uniformly. Answers are recorded and repeated queries answered from the
records, in both directions.
-/

open OracleComp OracleSpec

namespace Common

/-- The cost of a distinguisher query: a hash query costs the number of blocks of its padded
message (the permutation calls the sponge makes), a permutation query costs one, a coin costs
nothing. -/
def queryCost {Msg Dg Blk St : Type} (P : Padding Msg Blk) :
    (dSpec Msg Dg St).Domain → ℕ
  | .inl _ => 0
  | .inr (.inl m) => (P.pad m).length
  | .inr (.inr _) => 1

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]

/-! ## The real world -/

/-! ## The simulator and the ideal world -/

/-- The answer of the simulator at a fresh rooted node with path `β`: when `β` pads a message `m`,
the random oracle's digest `H m` completed by uniform bits; otherwise a uniform state. -/
noncomputable def rootedAnswer (P : Padding Msg (Dg × E)) [P.Lawful] (β : List (Dg × E)) :
    OracleComp (unifSpec + roSpec Msg Dg) (SpState Dg E C) :=
  match P.unpad β with
  | some m => do
    let d ← ((roSpec Msg Dg).query m : OracleComp (unifSpec + roSpec Msg Dg) Dg)
    let ec ← (liftM ($ᵗ (E × C)) : OracleComp (unifSpec + roSpec Msg Dg) (E × C))
    pure ((d, ec.1), ec.2)
  | none => liftM ($ᵗ (SpState Dg E C))

/-- **The simulator** (Bertoni et al., EUROCRYPT 2008): answers `π` and `π⁻¹` with oracle access
to the random oracle `H`. -/
noncomputable def simulator (P : Padding Msg (Dg × E)) [P.Lawful] :
    QueryImpl (permutationOracleSpec (SpState Dg E C))
      (StateT (SimState Dg E C) (OracleComp (unifSpec + roSpec Msg Dg)))
  | .forward x => StateT.mk fun σ ↦
      match forwardLookup σ.edges x with
      | some y => pure (y, σ)
      | none =>
        match chainOf σ.chains x with
        | some (s, β) => do
          let y ← rootedAnswer P (β ++ [blockTo s x])
          pure (y, ⟨(x, y) :: σ.edges, (y, β ++ [blockTo s x]) :: σ.chains⟩)
        | none => do
          let y ← (liftM ($ᵗ (SpState Dg E C)) : OracleComp (unifSpec + roSpec Msg Dg) _)
          pure (y, ⟨(x, y) :: σ.edges, σ.chains⟩)
  | .inverse y => StateT.mk fun σ ↦
      match inverseLookup σ.edges y with
      | some x => pure (x, σ)
      | none => do
        let x ← (liftM ($ᵗ (SpState Dg E C)) : OracleComp (unifSpec + roSpec Msg Dg) _)
        pure (x, ⟨(x, y) :: σ.edges, σ.chains⟩)

/-- The ideal world: coins forwarded, `H` the random oracle, `π` and `π⁻¹` the simulator. -/
noncomputable def idealImpl (P : Padding Msg (Dg × E)) [P.Lawful] :
    QueryImpl (dSpec Msg Dg (SpState Dg E C))
      (StateT (SimState Dg E C) (OracleComp (unifSpec + roSpec Msg Dg)))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + roSpec Msg Dg) _)
  | .inr (.inl m) => liftM ((roSpec Msg Dg).query m : OracleComp (unifSpec + roSpec Msg Dg) Dg)
  | .inr (.inr q) => simulator P q

/-- **The ideal world** run of a distinguisher: the simulator from its initial state, the random
oracle from the empty cache. -/
noncomputable def idealGame (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C) {α : Type}
    (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) : ProbComp α :=
  (simulateQ (roSpec Msg Dg).romImpl ((simulateQ (idealImpl P) D).run' (SimState.init iv))).run' ∅

end Setting

end Common
