import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Chains.PartialChainEndpoint
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]

theorem completeFunction_empty :
    completeFunction (fun (_ : State) => none) = PMF.uniformOfFintype (State → State) :=
  FinitePmfProduct.uniform

theorem completeTables_empty {n : Nat} :
    completeTables (fun (_ : Fin n) (_ : State) => none) = PMF.uniformOfFintype (Fin n → State → State) := by
  simp only [completeTables, completeFunction_empty, FinitePmfProduct.uniform]

def record {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State) :
    Fin n → State → Option State :=
  Function.update observed query.1 (Function.update (observed query.1) query.2 (some answer))

theorem completeFunction_record (observed : State → Option State) (input answer : State) :
    completeFunction (Function.update observed input (some answer)) =
      FinitePmfProduct.law (Function.update (fun row => rowLaw (observed row)) input (PMF.pure answer)) := by
  unfold completeFunction
  congr 1
  funext row
  by_cases hrow : row = input
  · simp only [hrow, Function.update_self, rowLaw]
  · simp only [Function.update_of_ne hrow]

theorem completeFunction_observe_mass (observed : State → Option State) (input answer : State) (table : State → State) :
    rowLaw (observed input) answer * completeFunction (Function.update observed input (some answer)) table =
      if table input = answer then completeFunction observed table else 0 := by
  rw [completeFunction_record]
  exact FinitePmfProduct.observe_mass (fun row => rowLaw (observed row)) input answer table

theorem completeTables_record {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (answer : State) :
    completeTables (record observed query answer) =
      FinitePmfProduct.law (Function.update (fun step => completeFunction (observed step)) query.1
        (completeFunction (Function.update (observed query.1) query.2 (some answer)))) := by
  unfold completeTables record
  congr 1
  funext step
  by_cases hstep : step = query.1
  · simp only [hstep, Function.update_self]
  · simp only [Function.update_of_ne hstep]

theorem completeTables_observe_mass {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (answer : State) (tables : Fin n → State → State) :
    rowLaw (observed query.1 query.2) answer * completeTables (record observed query answer) tables =
      if tables query.1 query.2 = answer then completeTables observed tables else 0 := by
  rw [completeTables_record, FinitePmfProduct.update_apply, ← mul_assoc,
    completeFunction_observe_mass, ite_mul, zero_mul]
  by_cases hanswer : tables query.1 query.2 = answer
  · rw [if_pos hanswer, if_pos hanswer, completeTables, FinitePmfProduct.apply]
    exact Finset.mul_prod_erase Finset.univ (fun step => completeFunction (observed step) (tables step))
      (Finset.mem_univ query.1)
  · rw [if_neg hanswer, if_neg hanswer]

theorem completeTables_bind_observe {n : Nat} {Result : Type} (observed : Fin n → State → Option State)
    (query : Fin n × State) (next : State → (Fin n → State → State) → PMF Result) :
    (completeTables observed).bind (fun tables => next (tables query.1 query.2) tables) =
      (rowLaw (observed query.1 query.2)).bind (fun answer =>
        (completeTables (record observed query answer)).bind (next answer)) := by
  classical
  apply PMF.ext
  intro output
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← mul_assoc, completeTables_observe_mass,
    ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp

end SphincsSecurity.Concrete.PartialChainEndpoint
