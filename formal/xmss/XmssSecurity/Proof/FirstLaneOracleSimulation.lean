import XmssSecurity.Proof.IdealStatement

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

inductive Query (Index : Type) where
  | uniform (n : Nat)
  | encodingQuery (epoch : Epoch)
  | encodingSignAttempt (epoch : Epoch)
  | probe (index : Index) (target : Digest)
  | reveal (index : Index)
deriving DecidableEq

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

def encodingQuery (epoch : Epoch) :
    OracleComp (World Index) HashOutput :=
  liftM ((World Index).query (.encodingQuery epoch))

def encodingSignAttemptQuery (epoch : Epoch) :
    OracleComp (World Index) HashOutput :=
  liftM ((World Index).query (.encodingSignAttempt epoch))

def probeQuery (index : Index) (target : Digest) :
    OracleComp (World Index) Unit :=
  liftM ((World Index).query (.probe index target))

def revealQuery (index : Index) : OracleComp (World Index) Digest :=
  liftM ((World Index).query (.reveal index))

def uniformForwardImpl : QueryImpl unifSpec (OracleComp (World Index)) :=
  fun n => uniformQuery n

def liftProbComp (computation : ProbComp α) : OracleComp (World Index) α :=
  simulateQ uniformForwardImpl computation

def IsSpecialQuery : (World Index).Domain → Prop
  | .uniform _ => False
  | _ => True

def IsHazardQuery : (World Index).Domain → Prop
  | .encodingQuery _ => True
  | .probe _ _ => True
  | _ => False

noncomputable instance (input : Query Index) :
    Fintype ((World Index).Range input) := by
  cases input <;> infer_instance

noncomputable instance (input : Query Index) :
    Inhabited ((World Index).Range input) := by
  cases input <;> infer_instance

noncomputable instance : DecidablePred (IsSpecialQuery (Index := Index)) :=
  Classical.decPred _

noncomputable instance : DecidablePred (IsHazardQuery (Index := Index)) :=
  Classical.decPred _

noncomputable instance : IsUniformSpec (World Index) :=
  IsUniformSpec.ofFintypeInhabited _

end XmssSecurity.FirstLaneOracleSimulation
