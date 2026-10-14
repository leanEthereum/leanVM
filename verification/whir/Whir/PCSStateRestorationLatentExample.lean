import Whir.PCSStateRestorationLatent

/-! Kernel-sized actual adaptive ROM example. The adversary queries the child
before its parent; final verification queries the parent and repeats the child.
The child's literal before-state depends on the undisclosed parent answer. -/
namespace Whir.PCSStateRestoration.Latent.Example
open TypedOracleCompiler TypedFiatShamirGame

set_option autoImplicit false

abbrev Answer (_ : Bool) := Bool

/-- false is the parent key; true is the child key. -/
def model : NodeModel Bool Answer Bool where
  reconstruct key rest := match key with
    | false => false
    | true => rest ⟨false,by decide⟩
  before publicData key := key && publicData
  after publicData key answer := if key then publicData || answer else answer

def adversary : Sampling Bool Answer Bool 1 :=
  .draw true (fun child => .ret child)

def verifier (_ : Bool) : Sampling Bool Answer (Bool × Bool) 2 :=
  .draw false (fun parent => .draw true (fun child => .ret (parent,child)))

def source : Sampling Bool Answer (Bool × Bool) 3 := Sampling.bind adversary verifier

def table : Table Bool Answer := fun key => key

theorem actual_request_trace :
    (Sampling.execute table source).2 = [⟨true,true⟩,⟨false,false⟩,⟨true,true⟩] := by rfl

theorem actual_result : (Sampling.execute table source).1 = (false,true) := by rfl

theorem actual_memo_trace :
    (Sampling.execute table (RawOracleCoupling.memo source (fun _ => none))).2 =
      [⟨true,true⟩,⟨false,false⟩] := by rfl

theorem actual_memo_result :
    (Sampling.execute table (RawOracleCoupling.memo source (fun _ => none))).1.1 = (false,true) := by rfl

/-- Both executions expose the child first with identical empty preceding view,
but its latent public state differs because the parent's answer differs. -/
theorem capture_is_genuinely_latent :
    firstDisclosure true source (fun _ => false) = some [] ∧
    firstDisclosure true source (fun key => !key) = some [] ∧
    publicNode model true (fun _ => false) = false ∧
    publicNode model true (fun key => !key) = true := by decide

private theorem bool_true_probability :
    Soundness.uniformProb (Finset.univ.filter fun answer : Bool => answer = true) = (1 : ℚ)/2 := by
  have filtered : (Finset.univ.filter fun answer : Bool => answer = true) = {true} := by
    ext answer
    cases answer <;> simp
  rw [Soundness.uniformProb,filtered]
  norm_num

theorem conditional_hazard : ConditionalHazard model ((1 : ℚ)/2) := by
  intro key rest safe
  cases key with
  | false => simpa [model] using le_of_eq bool_true_probability
  | true =>
    have parentZero : rest ⟨false,by decide⟩ = false := by simpa [model] using safe
    simpa [model,parentZero] using le_of_eq bool_true_probability

def Failure (oracle : Table Bool Answer) : Prop := oracle false || oracle true = true

instance : DecidablePred Failure := by
  intro oracle
  unfold Failure
  infer_instance

/-- The literal final path is parent then child although the query order is
child, parent, child. Its repeated child is the same globally memoized answer. -/
theorem accepted_path (oracle : Table Bool Answer) (failed : Failure oracle) :
    StatePath model oracle (Sampling.execute oracle source).2 false true := by
  have requestTrace : (Sampling.execute oracle source).2 =
      [⟨true,oracle true⟩,⟨false,oracle false⟩,⟨true,oracle true⟩] := by rfl
  rw [requestTrace]
  have finalState : after model true oracle = true := by simpa [after,publicNode,model,erase,Failure] using failed
  have childPath : StatePath model oracle
      [⟨true,oracle true⟩,⟨false,oracle false⟩,⟨true,oracle true⟩] (before model true oracle) true := by
    apply StatePath.step true (by simp)
    rw [finalState]
    exact StatePath.nil true
  exact StatePath.step false (by simp) childPath

/-- The generic latent theorem applies to this unrestricted child-before-parent
program. The expression is its query bound, not a claimed security level. -/
theorem probability_bound : Soundness.uniformProb (Finset.univ.filter Failure) ≤
    (1 : ℚ)*(1/2) + (2 : ℚ)*(1/2) := by
  have bound := adversary_verifier_failure_probability model 1 2 adversary verifier (1/2)
    (by positivity) conditional_hazard Failure accepted_path
  have sameFilter :
      @Finset.filter (Table Bool Answer) Failure (fun oracle => Classical.propDecidable (Failure oracle)) Finset.univ =
        Finset.univ.filter Failure := by
    ext oracle
    simp
  rw [sameFilter] at bound
  simpa using bound

#eval (Sampling.execute table source).1
#eval (Sampling.execute table source).2.map (fun entry => (entry.1,entry.2))
#eval (Sampling.execute table (RawOracleCoupling.memo source (fun _ => none))).2.map
  (fun entry => (entry.1,entry.2))

#print axioms actual_memo_trace
#print axioms capture_is_genuinely_latent
#print axioms conditional_hazard
#print axioms accepted_path
#print axioms probability_bound
end Whir.PCSStateRestoration.Latent.Example
