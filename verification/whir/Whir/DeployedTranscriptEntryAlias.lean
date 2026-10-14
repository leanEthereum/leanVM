import Whir.DeployedTranscriptCoupling

/-! HISTORICAL pre-#552 constructor alias and exact finite probability gap.
It rules out independent constructor-tagged keys for that historical source,
not for the current merged #552 mode. The historical context-key game correctly
identifies the alias; no whole-message RO or current DMV conclusion follows. -/
namespace Whir.DeployedTranscriptEntryAlias
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open DeployedTranscript

/-- Both inputs are legal source constructors; no chaining state is injected. -/
def aliasLabel (iv publicInput : Digest32) : List Byte :=
  List.ofFn (ByteCodec.pairBytes (iv,publicInput))

theorem constructors_alias (C : PrimitiveOracle) (iv publicInput : Digest32) :
    fromLabel C (aliasLabel iv publicInput) = new C iv publicInput := by
  have padded_pair : padded (aliasLabel iv publicInput).toArray =
      ByteCodec.pairBytes (iv,publicInput) := by
    funext i
    simp only [padded,aliasLabel,List.getElem?_toArray,List.getElem?_ofFn,i.isLt,
      ↓reduceDIte,Option.getD_some]
  have length_label : (aliasLabel iv publicInput).length = 64 := List.length_ofFn
  have chunks_label : PublicMerkleLog.chunks (aliasLabel iv publicInput) =
      [aliasLabel iv publicInput] := by
    rw [PublicMerkleLog.chunks]
    simp only [length_label,Nat.le_refl,↓reduceIte]
  simp only [fromLabel,new,PublicMerkleLog.hash,chunks_label,PublicMerkleLog.run,
    Option.getD_some,PublicMerkleLog.node,length_label,Nat.zero_add,padded_pair,seedNode]

/-- Four actual source calls, including both (identical) seed occurrences and
both squeeze occurrences; the cached primitive input does not waive source cost. -/
def realExperiment (iv publicInput : Digest32) (C : PrimitiveOracle) : Scalar24 × Scalar24 :=
  ((DeployedTranscript.sample C (new C iv publicInput)).2,
    (DeployedTranscript.sample C (fromLabel C (aliasLabel iv publicInput))).2)

def equalityObserver (view : Scalar24 × Scalar24) : Bool := decide (view.1 = view.2)

theorem realExperiment_equal (iv publicInput : Digest32) (C : PrimitiveOracle) :
    equalityObserver (realExperiment iv publicInput C) = true := by
  simp [equalityObserver,realExperiment,constructors_alias]

/-- The alternative ideal gives distinct keys to the two constructor histories.
Its table is literally sampled uniformly; no soundness premise is involved. -/
def separatedIdealExperiment (ro : Bool → Scalar24) : Scalar24 × Scalar24 :=
  (ro false,ro true)

noncomputable def realProbability (iv publicInput : Digest32) : ℚ :=
  distinguishProbability (realExperiment iv publicInput) equalityObserver

noncomputable def separatedIdealProbability : ℚ :=
  distinguishProbability separatedIdealExperiment equalityObserver

theorem real_probability_one (iv publicInput : Digest32) :
    realProbability iv publicInput = 1 := by
  classical
  unfold realProbability
  rw [distinguish_average (inferInstance : Fintype PrimitiveOracle)]
  simp only [realExperiment_equal,ite_true]
  exact average_const _

theorem separated_ideal_probability : separatedIdealProbability = 1 / (2^192 : ℚ) := by
  classical
  unfold separatedIdealProbability
  rw [distinguish_average (inferInstance : Fintype (Bool → Scalar24))]
  have indicator (coin : Bool → Scalar24) :
      (if equalityObserver (separatedIdealExperiment coin) then (1:ℚ) else 0) =
        (if coin false = coin true then (1:ℚ) else 0) := by
    by_cases h : coin false = coin true <;>
      simp [equalityObserver,separatedIdealExperiment,h]
  simp_rw [indicator]
  rw [fresh_coordinate false (fun (rest : {b : Bool // b ≠ false} → Scalar24) d =>
    if d = rest ⟨true,by decide⟩ then (1:ℚ) else 0)]
  have uniform (value : Scalar24) :
      average (fun d : Scalar24 => if d = value then (1:ℚ) else 0) =
        1 / (2^192 : ℚ) := by
    simp [average]
    norm_num
  simp only [uniform,average_const]

/-- Exact finite distinguishing gap caused by separating actual aliases.
Canonical original-context/source-byte keys are necessary for a small-loss claim. -/
theorem separated_constructor_gap (iv publicInput : Digest32) :
    |realProbability iv publicInput - separatedIdealProbability| =
      1 - 1 / (2^192 : ℚ) := by
  rw [real_probability_one,separated_ideal_probability]
  rw [abs_of_nonneg]
  norm_num

#print axioms constructors_alias
#print axioms separated_ideal_probability
#print axioms separated_constructor_gap
end Whir.DeployedTranscriptEntryAlias
