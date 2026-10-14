import Whir.DeployedTranscript
import Whir.PublicMerkleProbability

/-! HISTORICAL public finite-compression factorization for the pre-#552
context-key game. The ideal key is the full-CV/pending compression input, not
a semantic message history. This is NOT a full-message RO indifferentiability
claim and does NOT instantiate the current merged #552 mode. Public primitive
access, all output bits, ratchets, and adaptive computations are retained. -/
namespace Whir.DeployedTranscriptCoupling
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicCompressionProgram TypedOracleCompiler DeployedTranscript
open scoped BigOperators

abbrev Tail8 := Fin 8 → Byte
abbrev ChallengeOracle := Node → Scalar24
abbrev TailOracle := Node → Tail8

/-- The unexposed fourth word; it remains part of every public primitive answer
and every readonly source context after sampling. -/
def tail (digest : Digest32) : Tail8 := fun i => digest ⟨i.val+24,by omega⟩

def assemble (low : Scalar24) (high : Tail8) : Digest32 := fun i =>
  if h : i.val < 24 then low ⟨i.val,h⟩ else high ⟨i.val-24,by omega⟩

@[simp] theorem challenge_assemble (low : Scalar24) (high : Tail8) :
    challenge (assemble low high) = low := by
  funext i
  simp [challenge,assemble,i.isLt]

@[simp] theorem tail_assemble (low : Scalar24) (high : Tail8) :
    tail (assemble low high) = high := by
  funext i
  simp [tail,assemble,show ¬i.val+24 < 24 by omega]

@[simp] theorem assemble_split (digest : Digest32) :
    assemble (challenge digest) (tail digest) = digest := by
  funext i
  unfold assemble
  split
  · rfl
  · simp only [tail]
    congr 1
    apply Fin.ext
    dsimp
    omega

def digestEquiv : Digest32 ≃ Scalar24 × Tail8 where
  toFun digest := (challenge digest,tail digest)
  invFun pair := assemble pair.1 pair.2
  left_inv := assemble_split
  right_inv pair := by rcases pair with ⟨low,high⟩; simp

/-- The actual context-key simulator: one RO lookup and one memoized random
64-bit extension per public primitive input. No observer class is restricted. -/
def publicOracle (ro : ChallengeOracle) (seed : TailOracle) : PrimitiveOracle :=
  fun input => assemble (ro input) (seed input)

/-- Every public primitive input is retained, including arbitrary chosen CVs
and inputs outside the source's step grammar. -/
def simulatorAnswer (seed : TailOracle) (input : Node) :
    Sampling Node (fun _ => Scalar24) Digest32 1 :=
  .draw input (fun answer => .ret (assemble answer (seed input)))

theorem simulatorAnswer_eval (ro : ChallengeOracle) (seed : TailOracle) (input : Node) :
    Sampling.eval ro (simulatorAnswer seed input) = publicOracle ro seed input := rfl

/-- Actual ideal source sample: the construction directly requests its RO
coordinate, retains the random fourth word, and ratchets the full chaining CV. -/
def idealSample (ro : ChallengeOracle) (seed : TailOracle) (context : Context) :
    Context × Scalar24 :=
  let input := stepNode context.cv context.pending .squeeze
  (emptyContext (assemble (ro input) (seed input)),ro input)

theorem idealSample_source (ro : ChallengeOracle) (seed : TailOracle) (context : Context) :
    idealSample ro seed context = DeployedTranscript.sample (publicOracle ro seed) context := by
  simp [idealSample,DeployedTranscript.sample,DeployedTranscript.step,publicOracle]

/-- A bijection between the ACTUAL uniformly sampled 256-bit compression table
and the independent 192-bit context-key RO plus memoized 64-bit simulator seed. -/
def tableEquiv : PrimitiveOracle ≃ ChallengeOracle × TailOracle where
  toFun C := (fun n => challenge (C n),fun n => tail (C n))
  invFun pair := publicOracle pair.1 pair.2
  left_inv C := by funext n; exact assemble_split (C n)
  right_inv pair := by
    apply Prod.ext
    · funext n
      exact challenge_assemble (pair.1 n) (pair.2 n)
    · funext n
      exact tail_assemble (pair.1 n) (pair.2 n)

@[simp] theorem tableEquiv_inverse (coins : ChallengeOracle × TailOracle) :
    tableEquiv.symm coins = publicOracle coins.1 coins.2 := rfl

/-- Exact finite probabilities for arbitrary adaptive chosen-CV computations,
including source calls lowered by DeployedTranscript's checked equations.
The payoff may examine the complete public view and final readonly contexts. -/
theorem public_table_expectation [Fintype PrimitiveOracle]
    [Fintype ChallengeOracle] [Fintype TailOracle] (payoff : PrimitiveOracle → ℚ) :
    average payoff = average (fun coins : ChallengeOracle × TailOracle =>
      payoff (publicOracle coins.1 coins.2)) := by
  have h := RawOracleCoupling.average_equiv tableEquiv
    (fun coins : ChallengeOracle × TailOracle => payoff (tableEquiv.symm coins))
  simpa only [Equiv.symm_apply_apply,tableEquiv_inverse] using h

noncomputable def realProbability {R : Type} {Q : Nat}
    (program : Computation R Q) (D : R → Bool) : ℚ :=
  distinguishProbability (fun C : PrimitiveOracle => Sampling.eval C program) D

noncomputable def idealProbability {R : Type} {Q : Nat}
    (program : Computation R Q) (D : R → Bool) : ℚ :=
  distinguishProbability (fun coins : ChallengeOracle × TailOracle =>
    Sampling.eval (publicOracle coins.1 coins.2) program) D

/-- Zero loss in this precise context-key game, with no soundness premise,
no excluded observer, no assumed collision certificate, and no fixed-BLAKE
replacement. It does not promote context keys to full semantic histories. -/
theorem actual_context_game_coupling {R : Type} {Q : Nat}
    (program : Computation R Q) (D : R → Bool) :
    realProbability program D = idealProbability program D := by
  unfold realProbability idealProbability
  rw [distinguish_average (inferInstance : Fintype PrimitiveOracle),
    distinguish_average (inferInstance : Fintype (ChallengeOracle × TailOracle))]
  exact public_table_expectation _

/-- Uniform source challenges have 192 bits, not 256. -/
theorem challenge_card : Fintype.card Scalar24 = 2^192 := by
  norm_num [Scalar24,Byte,Fintype.card_fun]

/-- The independent simulator extension has exactly 64 bits. -/
theorem tail_card : Fintype.card Tail8 = 2^64 := by
  norm_num [Tail8,Byte,Fintype.card_fun]

#print axioms public_table_expectation
#print axioms idealSample_source
#print axioms actual_context_game_coupling
end Whir.DeployedTranscriptCoupling
