module

public import Quantum.StdModel.Props.Basic

@[expose] public section

/-!
# ITSR: interleaved target-subset resilience of the message hash (design D6)

The message hash `G(R, M)` is the set of cells selected by the digests of the hash inputs
`inputs R M` (for leanSPHINCS: the two MGF1 calls of `H_msg` on `R ‖ PK.seed ‖ PK.root ‖ M`,
mapped to the FORS instance and one leaf per tree). The classical query `M` is answered with a
fresh uniform `R` and the set `G(R, M)`. The adversary wins with `(R*, M*)` that is no queried pair
and whose set is contained in the union of the answered sets.

This is ITSR of Bernstein, Hulsing, Kolbl, Niederhagen, Rijneveld, Schwabe (CCS 2019, Def. 18),
with the adversary given superposition access to the world's hash. The public key prefix is part
of the message type: the instance fixes it or lets the adversary choose it per query, the latter
being at least as strong for the adversary since covering sets of different prefixes are pooled.
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Props

open HashSig

/-- **A message-to-subset map**: the hash inputs of `(R, M)` and the cells selected by their
digests. -/
structure MsgMap (Rnd Msg Cell : Type) where
  /-- The hashed inputs. -/
  inputs : Rnd → Msg → List HashInput
  /-- The cells selected by the digests. -/
  cells : List HashOutput → Finset Cell

variable {Rnd Msg Cell : Type} (W : OracleWorld)

/-- **The selected set `G(R, M)`**, computed through the world. -/
noncomputable def MsgMap.select (G : MsgMap Rnd Msg Cell) (r : Rnd) (m : Msg) :
    OracleComp W.Oracles (Finset Cell) :=
  G.cells <$> (G.inputs r m).mapM W.hash

/-- The union of the answered sets of a transcript. -/
def coveredCells [DecidableEq Cell] (log : QueryLog (Msg →ₒ Rnd × Finset Cell)) :
    Finset Cell :=
  (log.map fun e ↦ e.2.2).foldr (· ∪ ·) ∅

/-- **The ITSR challenger**: the query `M` is answered with a fresh uniform `R` and `G(R, M)`; the
forgery `(R*, M*)` wins when it is no queried pair and `G(R*, M*)` is covered. -/
noncomputable def itsr [SampleableType Rnd] [DecidableEq Cell] (G : MsgMap Rnd Msg Cell) :
    Experiment W (Msg →ₒ Rnd × Finset Cell) Unit (Rnd × Msg) where
  State := Unit
  setup := pure ()
  pub _ := ()
  answer _ m := do
    let r ← sample W Rnd
    let s ← G.select W r m
    pure (r, s)
  judge _ log out := do
    let s ← G.select W out.1 out.2
    pure (holds (out ∉ log.map (fun e ↦ (e.2.1, e.1)) ∧ s ⊆ coveredCells log))

/-- **ITSR success probability** at the table `tab`. -/
noncomputable abbrev itsrSucc [SampleableType Rnd] [DecidableEq Cell] (G : MsgMap Rnd Msg Cell)
    (tab : W.Tab) (A : Adversary W (Msg →ₒ Rnd × Finset Cell) Unit (Rnd × Msg)) : ENNReal :=
  (itsr W G).succAt tab A

end Quantum.StdModel.Props

end
