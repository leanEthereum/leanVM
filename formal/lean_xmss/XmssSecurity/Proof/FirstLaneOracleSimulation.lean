module

public import XmssSecurity.Scheme

@[expose] public section

/-!
# The first-lane oracle

`World` is the oracle of the first-lane experiment: uniform samples, encoding queries and encoding
signing attempts at a leaf index (answered by hash outputs), probes of a table entry against a
target digest, and reveals of a table entry. Its hazards are the encoding queries and the probes
(`IsHazardQuery`), and `liftProbComp` lifts a probabilistic computation through its uniform queries.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

inductive Query (Index : Type) where
  | uniform (n : Nat)
  | encodingQuery (leafIndex : LeafIndex)
  | encodingSignAttempt (leafIndex : LeafIndex)
  | probe (index : Index) (target : Digest)
  | reveal (index : Index)

@[reducible]
def World (Index : Type) : OracleSpec (Query Index) :=
  OracleSpec.ofFn fun
  | .uniform n => Fin (n + 1)
  | .encodingQuery _ => HashOutput
  | .encodingSignAttempt _ => HashOutput
  | .probe _ _ => Unit
  | .reveal _ => Digest

def uniformQuery (n : Nat) : OracleComp (World Index) (Fin (n + 1)) :=
  liftM ((World Index).query (.uniform n))

def encodingQuery (leafIndex : LeafIndex) :
    OracleComp (World Index) HashOutput :=
  liftM ((World Index).query (.encodingQuery leafIndex))

def encodingSignAttemptQuery (leafIndex : LeafIndex) :
    OracleComp (World Index) HashOutput :=
  liftM ((World Index).query (.encodingSignAttempt leafIndex))

def probeQuery (index : Index) (target : Digest) :
    OracleComp (World Index) Unit :=
  liftM ((World Index).query (.probe index target))

def revealQuery (index : Index) : OracleComp (World Index) Digest :=
  liftM ((World Index).query (.reveal index))

def uniformForwardImpl : QueryImpl unifSpec (OracleComp (World Index)) :=
  fun n => uniformQuery n

def liftProbComp {α : Type _} (computation : ProbComp α) : OracleComp (World Index) α :=
  simulateQ uniformForwardImpl computation

def IsHazardQuery : (World Index).Domain → Prop
  | .encodingQuery _ => True
  | .probe _ _ => True
  | _ => False

noncomputable instance : DecidablePred (IsHazardQuery (Index := Index)) :=
  Classical.decPred _

end XmssSecurity.FirstLaneOracleSimulation
