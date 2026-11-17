module

public import Statement.LeanVm

@[expose] public section

/-!
# Simulation layers as one, and a permutation sampled with coins

The composed system runs two independent lazily sampled permutations: in the knowledge-soundness
world the proof system's `π` is the model's and the signature scheme's `π_h` is sampled inside
the computation with coins; in the forgery world the roles are swapped. Both are read here as one
stateful simulation over coins, whose state holds both permutations' edges.

* `run_nest`: a stateful layer whose runs are answered by a second stateful layer is one stateful
  layer on the pair of states (`nest`), as `Common.SufCma.MultiKey.flatten` for two random
  oracles.
* `run_writerAsState`, `run_eq_writerAsState`: a writer layer (the forgery game's logged signing
  oracle) is a stateful layer appending to its state (`writerAsState`).
* `run_simulateQ_coins`, `run_liftM_of_coins`, `run_lazy_liftM`: a coin computation run by a
  layer that answers coins by coins keeps its distribution and leaves the state alone.
* `run_loggedOracles`: the transcript `loggedOracles` writes, read through `permutationQueries`
  (its coins dropped), is the state of the lazy permutation that records its queries
  (`recordingPermutation`).
-/

open OracleComp OracleSpec
open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

namespace Common.Compose

/-! ## Two stateful layers as one -/

section Nest

variable {ι ι' ι'' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}
  {spec'' : OracleSpec.{0, 0} ι''} {σ τ α : Type}

/-- **Two stateful layers as one**: a query answered by `inner`, whose run is answered by
`outer`, on the pair of their states. -/
def nest (inner : QueryImpl spec (StateT σ (OracleComp spec')))
    (outer : QueryImpl spec' (StateT τ (OracleComp spec''))) :
    QueryImpl spec (StateT (σ × τ) (OracleComp spec'')) :=
  fun t ↦ StateT.mk fun s ↦
    (fun z ↦ (z.1.1, (z.1.2, z.2))) <$> (simulateQ outer ((inner t).run s.1)).run s.2

/-- **The nested run is the run of the nested layer**, its states rearranged. -/
theorem run_nest (inner : QueryImpl spec (StateT σ (OracleComp spec')))
    (outer : QueryImpl spec' (StateT τ (OracleComp spec''))) (X : OracleComp spec α) (s : σ)
    (u : τ) :
    (simulateQ outer ((simulateQ inner X).run s)).run u =
      (fun z ↦ ((z.1, z.2.1), z.2.2)) <$> (simulateQ (nest inner outer) X).run (s, u) := by
  induction X using OracleComp.inductionOn generalizing s u with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind, nest, StateT.run_mk, bind_map_left]
    exact bind_congr fun z ↦ ih z.1.1 z.1.2 z.2

end Nest

/-! ## A writer layer as a stateful one -/

section Writer

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'} {L α : Type}
  [EmptyCollection L] [Append L] [LawfulAppend L]

/-- **A writer layer as a stateful one**: each step appends what it writes to the state. -/
def writerAsState (g : QueryImpl spec (WriterT L (OracleComp spec'))) :
    QueryImpl spec (StateT L (OracleComp spec')) :=
  fun t ↦ StateT.mk fun l ↦ (fun z ↦ (z.1, l ++ z.2)) <$> (g t).run

/-- The writer's run, its log appended to `l`, is the stateful run from `l`. -/
theorem run_writerAsState (g : QueryImpl spec (WriterT L (OracleComp spec')))
    (X : OracleComp spec α) (l : L) :
    (fun z ↦ (z.1, l ++ z.2)) <$> (simulateQ g X).run =
      (simulateQ (writerAsState g) X).run l := by
  induction X using OracleComp.inductionOn generalizing l with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, WriterT.run_bind', map_bind, writerAsState, StateT.run_mk,
      bind_map_left]
    refine bind_congr fun z ↦ ?_
    rw [← ih, Functor.map_map]
    congr 1
    funext w
    simp [LawfulAppend.append_assoc]

/-- The writer's run is the stateful run from the empty log. -/
theorem run_eq_writerAsState (g : QueryImpl spec (WriterT L (OracleComp spec')))
    (X : OracleComp spec α) : (simulateQ g X).run = (simulateQ (writerAsState g) X).run ∅ := by
  rw [← run_writerAsState]
  simp

end Writer

/-! ## Coins through a stateful layer -/

section Coins

variable {σ α : Type}

/-- **A layer that answers coins by coins keeps a coin computation**, and its state. -/
theorem run_simulateQ_coins (impl : QueryImpl unifSpec (StateT σ ProbComp))
    (h : ∀ n s, (impl n).run s = (·, s) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
    (p : ProbComp α) (s : σ) : (simulateQ impl p).run s = (·, s) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, h, bind_map_left, map_bind]
    exact bind_congr fun u ↦ ih u

/-- **A coin computation in the model, run by a layer that answers coins by coins**, keeps its
distribution and the layer's state. -/
theorem run_liftM_of_coins (impl : QueryImpl RandomPermutationOracles (StateT σ ProbComp))
    (h : ∀ n s, (impl (.inl n)).run s =
      (·, s) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
    (p : ProbComp α) (s : σ) :
    (simulateQ impl (liftM p : OracleComp RandomPermutationOracles α)).run s = (·, s) <$> p := by
  change (simulateQ impl (simulateQ (fun n ↦ liftM (unifSpec.query n)) p)).run s = _
  rw [← QueryImpl.simulateQ_compose]
  refine run_simulateQ_coins _ (fun n s ↦ ?_) p s
  change (simulateQ impl (liftM (RandomPermutationOracles.query (.inl n)))).run s = _
  rw [simulateQ_spec_query]
  exact h n s

/-- **A coin computation in the model, run against the lazy permutation**, keeps its
distribution and the permutation's edges. -/
theorem run_lazy_liftM (p : ProbComp α) (E : PermutationEdges KeccakState) :
    (simulateQ lazyRandomPermutationOracles (liftM p : OracleComp RandomPermutationOracles α)).run
      E = (·, E) <$> p :=
  run_liftM_of_coins _ (fun _ _ ↦ rfl) p E

end Coins

/-! ## The transcript's permutation queries -/

/-- **The lazy permutation that records its queries**: coins forwarded; a query of `π` or `π⁻¹`
answered by `lazyRandomPermutation`, and appended with its answer to the record. -/
noncomputable def recordingPermutation :
    QueryImpl RandomPermutationOracles
      (StateT (List (PermutationQuery KeccakState × KeccakState) × PermutationEdges KeccakState)
        ProbComp)
  | .inl n => StateT.lift (liftM (unifSpec.query n))
  | .inr q => StateT.mk fun s ↦
      (fun z ↦ (z.1, (s.1 ++ [(q, z.1)], z.2))) <$> (lazyRandomPermutation q).run s.2

/-- **The logged run against the lazy permutation, its transcript read through its permutation
queries, is the recording permutation's run.** -/
theorem run_loggedOracles {α : Type} (X : OracleComp RandomPermutationOracles α)
    (t : OracleQueryLog) (E : PermutationEdges KeccakState) :
    (fun z ↦ (z.1.1, (LeanVM.permutationQueries z.1.2, z.2))) <$>
        (simulateQ lazyRandomPermutationOracles ((simulateQ loggedOracles X).run t)).run E =
      (simulateQ recordingPermutation X).run (LeanVM.permutationQueries t, E) := by
  rw [run_nest, Functor.map_map]
  refine map_run_simulateQ_eq_of_query_map_eq_inv' (nest loggedOracles
    lazyRandomPermutationOracles) recordingPermutation (fun _ ↦ True)
    (fun s ↦ (LeanVM.permutationQueries s.1, s.2)) (fun _ _ _ _ _ ↦ trivial) (fun q s _ ↦ ?_)
    X (t, E) trivial
  rcases q with n | q <;>
    simp [nest, loggedOracles, recordingPermutation, lazyRandomPermutationOracles,
      LeanVM.permutationQueries]

end Common.Compose
