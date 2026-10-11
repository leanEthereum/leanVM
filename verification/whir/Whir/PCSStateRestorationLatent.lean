import Whir.PCSStateRestorationLatentProbability

/-! Latent-context state restoration. The reconstruction is a pure function of
all table coordinates except the queried one, not an operational certificate
oracle. It releases no ancestor answer, adds no query, and changes no program.
Actual-source adapters must implement that reconstruction and prove its literal
state correspondence; these obligations are not asserted by this module. -/
namespace Whir.PCSStateRestoration.Latent
open TypedOracleCompiler TypedFiatShamirGame
open FiatShamirGame (average)

set_option autoImplicit false
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

universe u v w z
variable {Key : Type u} {Answer : Key → Type v} {Public : Type w}

/-- A literal full-table source reconstruction factors through the erased key
only if replacing that answer leaves it unchanged. This is a causality law,
not a final bad-probability premise. -/
def ErasureIndependent [DecidableEq Key] (sourceSnapshot : Key → Table Key Answer → Public) : Prop :=
  ∀ key table answer, sourceSnapshot key (Function.update table key answer) = sourceSnapshot key table

section Reconstruction
variable [DecidableEq Key]

def fill (key : Key) (rest : Erased Answer key) (answer : Answer key) : Table Key Answer :=
  (Equiv.piSplitAt key Answer).symm (answer,rest)

@[simp] theorem fill_erase (key : Key) (table : Table Key Answer) (answer : Answer key) :
    fill key (erase key table) answer = Function.update table key answer := by
  funext other
  by_cases same : other = key
  · subst other; simp [fill,Equiv.piSplitAt]
  · simp [fill,erase,Equiv.piSplitAt,same]

/-- Construct an erased-key reconstruction from an actual full-table function.
The fixed reference answer is mathematical coordinate filling, not a simulated
RO reply or an additional query. Its choice is immaterial under independence. -/
def erasedReconstruction (sourceSnapshot : Key → Table Key Answer → Public)
    (reference : (key : Key) → Answer key) (key : Key) (rest : Erased Answer key) : Public :=
  sourceSnapshot key (fill key rest (reference key))

theorem erased_reconstruction_eq_source (sourceSnapshot : Key → Table Key Answer → Public)
    (reference : (key : Key) → Answer key) (independent : ErasureIndependent sourceSnapshot)
    (key : Key) (table : Table Key Answer) :
    erasedReconstruction sourceSnapshot reference key (erase key table) = sourceSnapshot key table := by
  rw [erasedReconstruction,fill_erase]
  exact independent key table (reference key)

end Reconstruction

/-- Pure latent public-node computation plus literal before/after state maps.
`reconstruct` has no access to the current answer by its domain, and is never
called by the operational Sampling computation. -/
structure NodeModel (Key : Type u) (Answer : Key → Type v) (Public : Type w) where
  reconstruct : (key : Key) → Erased Answer key → Public
  before : Public → Key → Bool
  after : Public → (key : Key) → Answer key → Bool

def publicNode (model : NodeModel Key Answer Public) (key : Key) (table : Table Key Answer) : Public :=
  model.reconstruct key (erase key table)

def before (model : NodeModel Key Answer Public) (key : Key) (table : Table Key Answer) : Bool :=
  model.before (publicNode model key table) key

def after (model : NodeModel Key Answer Public) (key : Key) (table : Table Key Answer) : Bool :=
  model.after (publicNode model key table) key (table key)

def Transition (model : NodeModel Key Answer Public) (key : Key) (table : Table Key Answer) : Prop :=
  before model key table = false ∧ after model key table = true

/-- Source-round path through actual exposed key/value pairs. Its order can be
unrelated to query order, and its reconstructed ancestor draws can be latent at
the time of a child-prefix query. The path still links literal state values. -/
inductive StatePath (model : NodeModel Key Answer Public) (table : Table Key Answer)
    (exposed : List (Sigma Answer)) : Bool → Bool → Prop where
  | nil (state : Bool) : StatePath model table exposed state state
  | step (key : Key) {final : Bool} (recorded : (⟨key,table key⟩ : Sigma Answer) ∈ exposed)
      (rest : StatePath model table exposed (after model key table) final) :
      StatePath model table exposed (before model key table) final

theorem path_has_transition (model : NodeModel Key Answer Public) (table : Table Key Answer)
    (exposed : List (Sigma Answer)) (start finish : Bool) :
    StatePath model table exposed start finish → start = false → finish = true →
      ∃ entry ∈ exposed, Transition model entry.1 table := by
  intro path
  induction path with
  | nil state =>
    intro initialState finalState
    have impossible : false = true := initialState.symm.trans finalState
    cases impossible
  | step key member rest ih =>
    intro initialState finalState
    cases returned : after model key table with
    | false => exact ih returned finalState
    | true => exact ⟨⟨key,table key⟩,member,initialState,returned⟩

section Probability
variable [DecidableEq Key] [Fintype Key]
variable [∀ key, Fintype (Answer key)] [∀ key, Nonempty (Answer key)]

/-- Exact conditional uniform hazard for every erased complete table. The
reconstructed ancestors are fixed, even if they have not been disclosed. -/
def ConditionalHazard (model : NodeModel Key Answer Public) (epsilon : ℚ) : Prop :=
  ∀ key rest, model.before (model.reconstruct key rest) key = false →
    Soundness.uniformProb (Finset.univ.filter fun answer : Answer key =>
      model.after (model.reconstruct key rest) key answer = true) ≤ epsilon

omit [Fintype Key] [∀ key, Nonempty (Answer key)] in
theorem latent_fiber_bound (model : NodeModel Key Answer Public) (epsilon : ℚ)
    (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard model epsilon) :
    FiberBound (Transition model) epsilon := by
  classical
  intro key table
  have fixed (answer : Answer key) : publicNode model key (Function.update table key answer) = publicNode model key table := by
    simp [publicNode]
  simp only [Transition,before,after,fixed,Function.update_self]
  cases state : model.before (publicNode model key table) key with
  | false =>
    simpa only [publicNode,average,Soundness.uniformProb,Finset.card_filter,Nat.cast_sum,
      Nat.cast_ite,Nat.cast_one,Nat.cast_zero,true_and] using hazard key (erase key table) state
  | true => simpa [average] using nonnegative

/-- Accepted extraction-failure paths from initial zero imply an observed
transition. No chronological causality restriction is imposed on queries. -/
theorem accepted_path_failure_probability {R : Type z} (model : NodeModel Key Answer Public)
    (Q k : Nat) (source : Sampling Key Answer R (Q+k))
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard model epsilon)
    (failure : Table Key Answer → Prop)
    (acceptedPath : ∀ table, failure table → StatePath model table (Sampling.execute table source).2 false true) :
    Soundness.uniformProb (Finset.univ.filter failure) ≤ ((Q+k : Nat) : ℚ)*epsilon := by
  apply covered_failure_probability (Transition model) epsilon nonnegative
    (latent_fiber_bound model epsilon nonnegative hazard) source failure
  intro table failed
  exact path_has_transition model table _ false true (acceptedPath table failed) rfl rfl

/-- Q adversarial requests followed by k verifier lookups. The continuations,
all keys and repetitions are retained, with no ancestor-warming transformation. -/
theorem adversary_verifier_failure_probability {R S : Type z} (model : NodeModel Key Answer Public)
    (Q k : Nat) (adversary : Sampling Key Answer R Q) (verifier : R → Sampling Key Answer S k)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard model epsilon)
    (failure : Table Key Answer → Prop)
    (acceptedPath : ∀ table, failure table →
      StatePath model table (Sampling.execute table (Sampling.bind adversary verifier)).2 false true) :
    Soundness.uniformProb (Finset.univ.filter failure) ≤ (Q : ℚ)*epsilon + (k : ℚ)*epsilon := by
  have bound := accepted_path_failure_probability model Q k (Sampling.bind adversary verifier)
    epsilon nonnegative hazard failure acceptedPath
  simpa only [Nat.cast_add,add_mul] using bound

end Probability

/-- Actual operation accounting: repeats stay in the request trace, while the
memo interpreter allocates distinct fresh keys and excludes the fixed prefix. -/
theorem exposure_accounting [DecidableEq Key] {R : Type z} {n : Nat}
    (source : Sampling Key Answer R n) (cache : Cache Key Answer)
    (trace : List (Sigma Answer)) (result : R × Cache Key Answer)
    (run : Sampling.Runs (RawOracleCoupling.memo source cache) trace result) :
    trace.length ≤ n ∧ (trace.map Sigma.fst).Nodup ∧ ∀ entry ∈ trace, cache entry.1 = none := by
  obtain ⟨fresh,distinct⟩ := PCSStateRestoration.memo_runs_distinct source cache trace result run
  exact ⟨run.length_le,distinct,fresh⟩

#print axioms erased_reconstruction_eq_source
#print axioms path_has_transition
#print axioms latent_fiber_bound
#print axioms accepted_path_failure_probability
#print axioms adversary_verifier_failure_probability
end Whir.PCSStateRestoration.Latent
