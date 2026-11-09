module

public import Common.Defs

@[expose] public section

/-!
# Games with direct calls of the permutation

The two-oracle form of a game (an honest part with the hash `H`, the adversary with `H`, `π` and
`π⁻¹`, an honest part with `H` and direct calls `F` of the permutation, `rpmGame2`) and its real
world (`realGame2`: `F` answered by `π`): the form the two-oracle transfer
(`Common.keccak256_transfer2`) takes, moved here from `Statement/RandomPermutation.lean` since no
end statement names them (LeanDA's games are stated with `π` queries, `Statement/LeanDa.lean`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

/-- A query of `hs` among coins and `hs`. -/
abbrev hq {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
    [∀ t : hs.Domain, SampleableType (hs.Range t)] (t : ι) : OracleComp (unifSpec + hs) (hs.Range t) :=
  hs.query t

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpState Dg E C)

/-! ## The verifier's oracles: the hash and direct calls of the permutation -/

/-- A direct call `F` of the permutation: states to states. -/
abbrev fSpec (St : Type) : OracleSpec St := St →ₒ St

/-- The verifier's oracles: the hash `H` and the direct calls `F`. -/
abbrev hfSpec (Msg Dg St : Type) := roSpec Msg Dg + fSpec St

/-- A game's oracles: coins, `H`, `π` and `π⁻¹`, and the verifier's direct calls `F`. -/
abbrev dSpec2 (Msg Dg St : Type) := unifSpec + (roSpec Msg Dg + (permutationOracleSpec St + fSpec St))

/-- The game's direct calls become permutation queries. -/
def toOne : QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
    (OracleComp (dSpec Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr (.inl m) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inl m)))
  | .inr (.inr (.inl q)) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inr q)))
  | .inr (.inr (.inr x)) => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inr (.forward x))))

/-- **The real world** of a game: `H` the sponge over the lazily sampled random permutation, and
`F` the permutation itself. -/
noncomputable def realGame2 {α : Type} (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) :
    ProbComp α :=
  realGame P iv (simulateQ (toOne (E := E) (C := C)) D)

/-- An `H` query. -/
abbrev hQuery (m : Msg) : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) Dg :=
  hq (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl m)

/-- An `F` query: a direct call of the permutation. -/
abbrev fQuery (x : SpState Dg E C) :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) (SpState Dg E C) :=
  hq (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x)

/-! ## A game with an adversary and the verifier's direct calls -/

/-- An honest computation with coins and `H` as a game computation. -/
def hEmbed2 : QueryImpl (unifSpec + roSpec Msg Dg)
    (OracleComp (dSpec2 Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr m => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inl m)))

/-- An honest computation with coins, `H` and `F` as a game computation. -/
def hfEmbed : QueryImpl (unifSpec + hfSpec Msg Dg (SpState Dg E C))
    (OracleComp (dSpec2 Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr (.inl m) => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inl m)))
  | .inr (.inr x) => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inr (.inr x))))

/-- An RPM adversary (coins, `H`, `π`, `π⁻¹`) as a game computation. -/
def advEmbed : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (OracleComp (dSpec2 Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr (.inl m) => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inl m)))
  | .inr (.inr q) => liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inr (.inl q))))

/-- **A game**: an honest part with `H`, the adversary with `H`, `π`, `π⁻¹`, an honest part with
`H` and `F`. -/
def rpmGame2 {β γ δ : Type} (pre : OracleComp (unifSpec + roSpec Msg Dg) β)
    (A : β → OracleComp (dSpec Msg Dg (SpState Dg E C)) γ)
    (post : β → γ → OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) δ) :
    OracleComp (dSpec2 Msg Dg (SpState Dg E C)) δ :=
  simulateQ (hEmbed2 (E := E) (C := C)) pre >>= fun x ↦
    simulateQ (advEmbed (Msg := Msg)) (A x) >>= fun a ↦ simulateQ (hfEmbed (Msg := Msg)) (post x a)

end Common
