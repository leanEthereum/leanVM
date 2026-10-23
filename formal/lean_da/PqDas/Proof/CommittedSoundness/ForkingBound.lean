/-
# Forking analysis of the committed soundness game

The quantitative heart of the code-binding proof: applying the replay forking
lemma to the wrapped committed soundness game (`CommittedSoundness.runTrace`) yields two
winning traces answering the *same* commitment with challenges resampled at the
fork point. Two cases:

* the two recorded vectors *differ*: both commit to the shared commitment, so
  the explicit reduction `forkCollisionReduction` wins the collision game of
  the vector commitment;
* the two recorded vectors are *equal*: the (non-codeword) vector of the first
  run was already determined before the fork point, so the second run's
  resampled challenge is a fresh uniform draw against a fixed non-codeword, and
  the code checker's soundness bounds this case by `δ`.

Aggregating over the commitment key with the marginalized Cauchy-Schwarz step
gives the headline bound `niCommittedSoundness_forking_bound`:

  `acc * (acc / (Q + 1) - |L|⁻¹) ≤ Pr[collision] + δ`,

where `acc` is the winning probability of the non-interactive committed
soundness game and `Q` bounds the adversary's random-oracle queries.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import PqDas.Proof.CommittedSoundness.Bridge
import VCVio.EvalDist.Inequalities
import PqDas.Proof.CommittedSoundness.Coupling
import PqDas.Proof.CommittedSoundness.Lockstep
import PqDas.VcvioExtras

open OracleComp OracleSpec ENNReal

open scoped PFunctor

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

section forking

variable [DecidableEq ComVC] [SampleableType L] [Fintype L] [Inhabited L]
  [Fintype Γ] [DecidableEq Λ] [DecidableEq L] [Inhabited Λ]

variable (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
  (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (Q : ℕ)

/-- Wrapped-spec fork-and-extract computation: replay-fork the wrapped
committed soundness game at the fork point and output the two recorded
vectors. If the fork fails, output an (equal, hence losing) dummy pair. -/
noncomputable def forkVecPair (ckVC : CkVC) :
    OracleComp (wrappedSpec L) ((Fin n → Λ) × (Fin n → Λ)) :=
  contextFork (runTrace C vc chk A ckVC)
    (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
    (Sum.inr ()) (forkPoint Q) >>= fun
      | some (x₁, x₂) => pure (x₁.vec, x₂.vec)
      | none => pure (fun _ => default, fun _ => default)

/-- The collision reduction (an explicit algorithm): run the wrapped
fork-and-extract computation, interpreting its uniform queries and its counted
challenge oracle by plain uniform sampling. -/
noncomputable def forkCollisionReduction :
    VectorCommitment.CollisionAdv Λ n CkVC := fun ckVC =>
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      uniformSampleImpl (spec := ((Unit →ₒ L) : OracleSpec Unit)))
    (forkVecPair C vc chk A Q ckVC)

/-! ### Bridging the two semantics

The collision game interprets the reduction over `ProbComp`, while the forking
analysis works with the wrapped-spec computation under uniform semantics. Both
oracle components of the simulation sample uniformly, so `evalDist` (hence
every event probability) is preserved. -/

omit [DecidableEq L] in
private lemma evalDistEq_simulateQ_unifImpl {α : Type}
    (oa : OracleComp (wrappedSpec L) α) :
    simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      uniformSampleImpl (spec := ((Unit →ₒ L) : OracleSpec Unit))) oa =ᵈ oa := by
  let : MeasurableSpace α := ⊤
  refine EvalDistEq.of_evalDist_eq (evalDist_simulateQ_eq_of_forall _ (fun t => ?_) oa)
  rw [OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn]
  rcases t with m | u
  · simp only [QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply]
    exact evalDist_liftM_query_uniform (spec := unifSpec) m
  · let : MeasurableSpace L := ⊤
    simp only [QueryImpl.add_apply_inr, uniformSampleImpl_apply]
    exact SampleableType.evalDist_uniformSample

omit [DecidableEq L] in
private lemma prEvent_simulateQ_unifImpl {α : Type}
    (oa : OracleComp (wrappedSpec L) α) (p : α → Prop) :
    Pr{let x ← (simulateQ (QueryImpl.ofLift unifSpec ProbComp +
      uniformSampleImpl (spec := ((Unit →ₒ L) : OracleSpec Unit))) oa)}[p x] = Pr{let x ← oa}[p x] :=
  (evalDistEq_simulateQ_unifImpl oa).prEvent_eq p

/-! ### Support facts for traces read off execution paths -/

omit [SampleableType L] [Fintype L] [Inhabited L] [DecidableEq L] in
/-- The output of any well-typed execution path of `main` is in `main`'s support. -/
private lemma output_path_mem_support {α : Type}
    (main : OracleComp (wrappedSpec L) α) (path : PFunctor.FreeM.Path main) :
    PFunctor.FreeM.output main path ∈ support main := by
  have h : PFunctor.FreeM.output main path ∈
      support (PFunctor.FreeM.output main <$> replayFirstPath main) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ (mem_support_replayFirstPath main path)
  simpa only [map_output_replayFirstPath] using h

omit [SampleableType L] [Fintype L] [Inhabited L] [DecidableEq L] [Inhabited Λ] in
/-- Winning traces on the support of `runTrace` satisfy the three win
conditions of the committed soundness game. -/
private lemma winOn_facts_of_win {ckVC : CkVC} {trace : Trace Λ n ComVC L}
    (htrace : trace ∈ support (runTrace C vc chk A ckVC))
    (hwin : trace.win = true) :
    trace.vec ∉ C.code ∧ chk.check trace.chal trace.vec = true ∧
      vc.commit ckVC trace.vec = trace.com := by
  unfold runTrace at htrace
  rw [support_bind] at htrace
  simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at htrace
  obtain ⟨⟨out, st⟩, _, rfl⟩ := htrace
  simp only [winOn, Bool.and_eq_true, decide_eq_true_eq] at hwin
  exact ⟨hwin.1.1, hwin.1.2, hwin.2⟩

omit [SampleableType L] [Fintype L] [Inhabited L] [Inhabited Λ] in
/-- **Key semantic fact**: for any completion of an occurrence of the counted
challenge oracle at position `s`, if the completed run's fork point is `s`,
then the completed trace's challenge *is* the answer of that completion (the
resampled answer, for the fork's second branch). Chains the cache/outer-log
lockstep through the first-miss position of the output commitment. -/
private lemma chal_eq_answer_of_completion {ckVC : CkVC} {s : Fin (Q + 1)}
    (occ : PFunctor.FreeM.Cursor.Occurrence
      (P := (wrappedSpec L).toPFunctor) (Sum.inr ())
      (runTrace C vc chk A ckVC) (↑s : ℕ))
    (cmp : occ.Completion)
    (hcf : forkPoint Q
      (PFunctor.FreeM.output (runTrace C vc chk A ckVC) cmp.path) = some s) :
    (PFunctor.FreeM.output (runTrace C vc chk A ckVC) cmp.path).chal =
      cmp.answer := by
  classical
  let main := runTrace C vc chk A ckVC
  let x₂ : Trace Λ n ComVC L := PFunctor.FreeM.output main cmp.path
  let log₂ : QueryLog (wrappedSpec L) := PFunctor.FreeM.Path.trace main cmp.path
  have hmem : (x₂, log₂) ∈ support (replayFirstRun main) := by
    simpa [replayPathResult, pathLogResult, x₂, log₂] using
      replayPathResult_mem_support_replayFirstRun main cmp.path
        (mem_support_replayFirstPath main cmp.path)
  have hsupp : x₂ ∈ support main := output_path_mem_support main cmp.path
  have hcache : x₂.roCache x₂.com = some x₂.chal :=
    (trace_com_mem_queryLog C vc chk A ckVC hsupp).2
  have htgt : x₂.queryLog[(↑s : ℕ)]? = some x₂.com :=
    forkPoint_getElem?_eq_some_com hcf
  obtain ⟨hslt, htgt_eq⟩ := List.getElem?_eq_some_iff.1 htgt
  obtain ⟨ω, hcacheω, hlogω⟩ :=
    runTrace_cache_outer_lockstep C vc chk A ckVC hmem (↑s : ℕ) hslt
  rw [htgt_eq] at hcacheω
  have hans : QueryLog.getQueryValue? log₂ (Sum.inr ()) (↑s : ℕ) =
      some cmp.answer :=
    getQueryValue?_completion_path_eq_answer occ cmp
  have hω : ω = cmp.answer := Option.some.inj (hlogω.symm.trans hans)
  have hchal : x₂.chal = ω := Option.some.inj (hcache.symm.trans hcacheω)
  exact hchal.trans hω

omit [DecidableEq ComVC] [DecidableEq L] [Inhabited Λ] in
/-- The code checker accepts a fixed trace's non-codeword vector on one fresh
uniform challenge with probability at most `δ` (and if the vector is a
codeword, the guarded event is impossible). -/
private lemma prEvent_check_query_le {δ : ℝ≥0∞} (hSound : chk.Sound C δ)
    (x : Trace Λ n ComVC L) :
    Pr{let a ← (query (Sum.inr ()) : OracleComp (wrappedSpec L)
        ((wrappedSpec L).Range (Sum.inr ())))}[x.vec ∉ C.code ∧ chk.check a x.vec = true] ≤ δ := by
  classical
  by_cases hin : x.vec ∈ C.code
  · exact le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _
      fun a _ h => h.1 hin)) zero_le
  · have h1 : Pr{let a ← (query (Sum.inr ()) : OracleComp (wrappedSpec L)
          ((wrappedSpec L).Range (Sum.inr ())))}[x.vec ∉ C.code ∧ chk.check a x.vec = true] =
        Pr{let l ← ($ᵗ L : ProbComp L)}[chk.check l x.vec = true] := by
      simp only [hin, not_false_eq_true, true_and]
      rw [prEvent_query_eq_card_div (spec := wrappedSpec L), SampleableType.prEvent_uniformSample]
      rfl
    have h2 : Pr{let l ← ($ᵗ L : ProbComp L)}[chk.check l x.vec = true] =
        Pr{let y ← (fun l => chk.check l x.vec) <$> ($ᵗ L : ProbComp L)}[y = true] := by
      rw [prEvent_map]
    rw [h1, h2]
    exact hSound x.vec hin

/-- The dynamic contextual fork, unfolded to a first execution path bound to
a `classifyForkView`-classified fresh completion of the located occurrence.
Local copy of VCVio's (private) `contextFork_eq_contextForkByClassify`
composed with `filterMapLocateAndForkBy`'s elimination rule. -/
private lemma contextFork_eq_filterMap {ι : Type} {spec : OracleSpec ι}
    [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)] {α : Type} (main : OracleComp spec α) (qb : ι → ℕ)
    (i : ι) (cf : α → Option (Fin (qb i + 1))) :
    contextFork main qb i cf =
      PFunctor.FreeM.Cursor.filterMapLocateAndForkBy (P := spec.toPFunctor)
        i main cf Fin.val (classifyForkView main qb i cf) := by
  unfold contextFork contextForkWitness
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy]
  unfold PFunctor.FreeM.Cursor.filterMapLocateAndForkBy
  rw [← PFunctor.FreeM.comp_map,
    PFunctor.FreeM.Cursor.map_locateAndForkBy,
    PFunctor.FreeM.Cursor.map_locateAndForkBy]
  apply congrArg (PFunctor.FreeM.bind (PFunctor.FreeM.withPath main))
  funext path
  rcases hcf : cf (PFunctor.FreeM.output main path) with _ | s
  · rfl
  · rcases hlocate : PFunctor.FreeM.Cursor.locateAt?
        (P := spec.toPFunctor) i main path s with _ | located
    · simp [hlocate]
    · simp only [hlocate]
      apply congrArg (fun f => PFunctor.FreeM.map f located.fork)
      funext view
      simp only [Function.comp_apply, Option.join, Option.map]
      unfold acceptContextForkWitness classifyForkView
      split <;> split <;> simp_all
      grind

/-- Per-path continuation of the unfolded contextual fork: locate the selected
occurrence, complete it once more, and classify the resulting fork view. -/
private noncomputable def forkLeaf (ckVC : CkVC)
    (path : PFunctor.FreeM.Path (runTrace C vc chk A ckVC)) :
    OracleComp (wrappedSpec L) (Option (Trace Λ n ComVC L × Trace Λ n ComVC L)) :=
  match forkPoint Q
      (PFunctor.FreeM.output (runTrace C vc chk A ckVC) path) with
  | none => pure none
  | some s =>
    match PFunctor.FreeM.Cursor.locateAt? (P := (wrappedSpec L).toPFunctor)
        (Sum.inr ()) (runTrace C vc chk A ckVC) path (↑s : ℕ) with
    | none => pure none
    | some located =>
        (fun second => classifyForkView (runTrace C vc chk A ckVC)
          (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
          (Sum.inr ()) (forkPoint Q) s
          { occurrence := located.occurrence,
            first := located.completion,
            second := second }) <$>
          OracleComp.Cursor.completeOccurrence located.occurrence

omit [SampleableType L] [Fintype L] [Inhabited L] [Inhabited Λ] in
private lemma contextFork_eq_bind_forkLeaf (ckVC : CkVC) :
    contextFork (runTrace C vc chk A ckVC)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
      (Sum.inr ()) (forkPoint Q) =
    PFunctor.FreeM.withPath (runTrace C vc chk A ckVC) >>=
      forkLeaf C vc chk A Q ckVC := by
  rw [contextFork_eq_filterMap,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkBy_eq_bind_complete]
  refine congrArg (PFunctor.FreeM.bind
    (PFunctor.FreeM.withPath (runTrace C vc chk A ckVC))) (funext fun path => ?_)
  unfold forkLeaf
  rcases hs : forkPoint Q
      (PFunctor.FreeM.output (runTrace C vc chk A ckVC) path) with _ | s
  · simp only []
  · simp only []
    rcases hloc : PFunctor.FreeM.Cursor.locateAt? (P := (wrappedSpec L).toPFunctor)
        (Sum.inr ()) (runTrace C vc chk A ckVC) path (↑s : ℕ) with _ | located
    · simp only []
    · simp only []
      rfl

omit [Inhabited Λ] in
/-- Per-path bound for the same-vector case: on any first-run path, the fork
completes with a classified pair of *equal* vectors with probability at most
`δ`. The first trace's non-codeword vector is fixed by the path; the second
completion's win check evaluates the checker on its freshly resampled focused
answer. -/
private lemma prEvent_sameVec_forkLeaf_le {δ : ℝ≥0∞}
    (hSound : chk.Sound C δ) (ckVC : CkVC)
    (path : PFunctor.FreeM.Path (runTrace C vc chk A ckVC)) :
    Pr{let r ← forkLeaf C vc chk A Q ckVC path}[∃ x₁ x₂, r = some (x₁, x₂) ∧ x₁.vec = x₂.vec] ≤ δ := by
  classical
  unfold forkLeaf
  rcases hcfp : forkPoint Q
      (PFunctor.FreeM.output (runTrace C vc chk A ckVC) path) with _ | s
  · simp only []
    rw [prEvent_pure]
    simp
  rcases hloc : PFunctor.FreeM.Cursor.locateAt? (P := (wrappedSpec L).toPFunctor)
      (Sum.inr ()) (runTrace C vc chk A ckVC) path (↑s : ℕ) with _ | located
  · simp only [hloc]
    rw [prEvent_pure]
    simp
  simp only [hloc]
  rw [prEvent_map]
  -- Compare against the focused-answer soundness bound on the located fork.
  have hfork := OracleComp.prEvent_focusPredicate_ofFreeM_fork_le
    (spec := wrappedSpec L) (main := runTrace C vc chk A ckVC)
    (i := Sum.inr ()) (n := (↑s : ℕ)) (path := path) located (fun _ => True)
    (fun x ans => x.vec ∉ C.code ∧ chk.check ans x.vec = true)
    (δ := δ) (fun x => prEvent_check_query_le C chk hSound x)
  rw [PFunctor.FreeM.Cursor.Located.fork_eq_map_complete, ofFreeM_map, prEvent_map] at hfork
  refine le_trans (prEvent_mono _ _ _ fun second hEsec => ?_) hfork
  -- Pointwise implication on the second completion.
  simp only [classifyForkView] at hEsec
  split_ifs at hEsec with hans hcfs
  · obtain ⟨x₁, x₂, heq, -⟩ := hEsec
    simp at heq
  swap
  · obtain ⟨x₁, x₂, heq, -⟩ := hEsec
    simp at heq
  -- Successful classification with equal vectors.
  obtain ⟨x₁, x₂, heq, hveq⟩ := hEsec
  rw [Option.some.injEq, Prod.mk.injEq] at heq
  obtain ⟨hx₁, hx₂⟩ := heq
  subst hx₁
  subst hx₂
  obtain ⟨hcf₁, hcf₂⟩ := hcfs
  have hfacts₁ := winOn_facts_of_win C vc chk A
    (output_path_mem_support _ _) (win_of_forkPoint_eq_some hcf₁)
  have hfacts₂ := winOn_facts_of_win C vc chk A
    (output_path_mem_support _ _) (win_of_forkPoint_eq_some hcf₂)
  have hchal : (PFunctor.FreeM.output (runTrace C vc chk A ckVC)
      (PFunctor.FreeM.Cursor.ForkView.secondPath
        { occurrence := located.occurrence, first := located.completion,
          second := second })).chal = second.answer :=
    chal_eq_answer_of_completion C vc chk A Q located.occurrence second hcf₂
  refine ⟨⟨hfacts₁.1, ?_⟩, trivial⟩
  show chk.check second.answer
      (PFunctor.FreeM.output (runTrace C vc chk A ckVC)
        (PFunctor.FreeM.Cursor.ForkView.firstPath
          { occurrence := located.occurrence, first := located.completion,
            second := second })).vec = true
  rw [hveq, ← hchal]
  exact hfacts₂.2.1

omit [Inhabited Λ] in
/-- **Same-vector case of the fork.** A successful contextual fork whose two
recorded vectors coincide has probability at most `δ`. -/
private lemma prEvent_sameVec_contextFork_le {δ : ℝ≥0∞}
    (hSound : chk.Sound C δ) (ckVC : CkVC) :
    Pr{let r ← (contextFork (runTrace C vc chk A ckVC)
        (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
        (Sum.inr ()) (forkPoint Q))}[∃ x₁ x₂, r = some (x₁, x₂) ∧ x₁.vec = x₂.vec] ≤ δ := by
  classical
  rw [contextFork_eq_bind_forkLeaf, OracleComp.prEvent_bind_eq_tsum]
  calc ∑' path, Pr{let x ← (PFunctor.FreeM.withPath (runTrace C vc chk A ckVC) :
          OracleComp (wrappedSpec L) _)}[x = path] *
        Pr{let r ← forkLeaf C vc chk A Q ckVC path}[∃ x₁ x₂, r = some (x₁, x₂) ∧ x₁.vec = x₂.vec]
      ≤ ∑' path, Pr{let x ← (PFunctor.FreeM.withPath (runTrace C vc chk A ckVC) :
          OracleComp (wrappedSpec L) _)}[x = path] * δ :=
        ENNReal.tsum_le_tsum fun path => mul_le_mul' le_rfl
          (prEvent_sameVec_forkLeaf_le C vc chk A Q hSound ckVC path)
    _ = (∑' path, Pr{let x ← (PFunctor.FreeM.withPath (runTrace C vc chk A ckVC) :
          OracleComp (wrappedSpec L) _)}[x = path]) * δ := ENNReal.tsum_mul_right
    _ ≤ 1 * δ := mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl
    _ = δ := one_mul δ

omit [SampleableType L] in
/-- **Different-vector case of the fork**: a successful contextual fork whose
two recorded vectors differ wins the collision check for the (deterministic)
commit, since both winning traces commit their vectors to the shared
commitment. -/
private lemma prEvent_diffVec_le_forkVecPair (ckVC : CkVC) :
    Pr{let r ← (contextFork (runTrace C vc chk A ckVC)
        (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
        (Sum.inr ()) (forkPoint Q))}[∃ x₁ x₂, r = some (x₁, x₂) ∧ x₁.vec ≠ x₂.vec] ≤
    Pr{let x ← (forkVecPair C vc chk A Q ckVC >>= fun vv =>
      pure (decide (vv.1 ≠ vv.2) &&
        decide (vc.commit ckVC vv.1 = vc.commit ckVC vv.2)))}[x = true] := by
  classical
  unfold forkVecPair
  rw [bind_assoc, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun r => ?_
  by_cases hE : ∃ x₁ x₂, r = some (x₁, x₂) ∧ x₁.vec ≠ x₂.vec
  swap
  · rw [ite_eq_right hE]
    exact zero_le
  rw [ite_eq_left hE]
  obtain ⟨x₁, x₂, hreq, hne⟩ := hE
  subst hreq
  by_cases hsupp : some (x₁, x₂) ∈ support (contextFork (runTrace C vc chk A ckVC)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
      (Sum.inr ()) (forkPoint Q))
  swap
  · rw [(prEvent_eq_zero_of_not_mem_support _) hsupp, zero_mul]
  -- Extract the fork facts from the support membership.
  obtain ⟨path, s, located, second, hpath, hcf₁, hsecond, hansne, hcf₂, hx₁, hx₂⟩ :=
    contextFork_success (runTrace C vc chk A ckVC)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
      (Sum.inr ()) (forkPoint Q) hsupp
  have hcf₁' : forkPoint Q x₁ = some s := by rw [hx₁]; exact hcf₁
  have hcf₂' : forkPoint Q x₂ = some s := by rw [hx₂]; exact hcf₂
  have hsupp₁ : x₁ ∈ support (runTrace C vc chk A ckVC) := by
    rw [hx₁]; exact output_path_mem_support _ _
  have hsupp₂ : x₂ ∈ support (runTrace C vc chk A ckVC) := by
    rw [hx₂]; exact output_path_mem_support _ _
  have hfacts₁ := winOn_facts_of_win C vc chk A hsupp₁
    (win_of_forkPoint_eq_some hcf₁')
  have hfacts₂ := winOn_facts_of_win C vc chk A hsupp₂
    (win_of_forkPoint_eq_some hcf₂')
  have hcom : x₁.com = x₂.com :=
    (runTrace_com_eq_of_mem_contextFork C vc chk A Q ckVC x₁ x₂ s hsupp
      hcf₁' hcf₂').1
  have hcommit : vc.commit ckVC x₁.vec = vc.commit ckVC x₂.vec := by
    rw [hfacts₁.2.2, hfacts₂.2.2, hcom]
  -- On the live fork event, the extraction returns a winning collision.
  have h1 : Pr{let b ← ((pure (x₁.vec, x₂.vec) : OracleComp (wrappedSpec L) _) >>= fun vv =>
        pure (decide (vv.1 ≠ vv.2) &&
          decide (vc.commit ckVC vv.1 = vc.commit ckVC vv.2)))}[b = true] = 1 := by
    rw [pure_bind, prEvent_pure]
    simp [hne, hcommit]
  exact le_trans (le_of_eq (mul_one _).symm)
    (mul_le_mul' le_rfl (le_of_eq h1.symm))

/-- Per-key forking bound: at a fixed commitment key, the fork-success
probability of the wrapped game satisfies the replay-forking bound against the
collision extraction, up to the checker soundness `δ`. -/
private lemma perKey_forking_bound {δ : ℝ≥0∞} (hSound : chk.Sound C δ)
    (ckVC : CkVC) :
    Pr{let t ← runTrace C vc chk A ckVC}[(forkPoint Q t).isSome] *
      (Pr{let t ← runTrace C vc chk A ckVC}[(forkPoint Q t).isSome] /
          ((Q : ℝ≥0∞) + 1) - (Fintype.card L : ℝ≥0∞)⁻¹) ≤
    Pr{let x ← (forkVecPair C vc chk A Q ckVC >>= fun vv =>
      pure (decide (vv.1 ≠ vv.2) &&
        decide (vc.commit ckVC vv.1 = vc.commit ckVC vv.2)))}[x = true] + δ := by
  classical
  have hacc_sum : Pr{let t ← runTrace C vc chk A ckVC}[(forkPoint Q t).isSome] =
      ∑ s, Pr{let t ← runTrace C vc chk A ckVC}[forkPoint Q t = some s] :=
    prEvent_isSome_eq_sum _ _
  have hH : (Fintype.card ((wrappedSpec L).Range (Sum.inr ())) : ℝ≥0∞)⁻¹ =
      (Fintype.card L : ℝ≥0∞)⁻¹ := rfl
  have ha := le_prEvent_isSome_contextFork (main := runTrace C vc chk A ckVC)
    (qb := fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
    (i := Sum.inr ()) (cf := forkPoint Q)
    (CfReachable.toPathCfReachable
      (runTrace_forkPoint_CfReachable C vc chk A Q ckVC))
  refine le_trans (?_ : _ ≤ Pr{let r ← (contextFork (runTrace C vc chk A ckVC)
        (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
        (Sum.inr ()) (forkPoint Q))}[r.isSome]) ?_
  · rw [hacc_sum]
    simpa only [show (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q)
        (Sum.inr ()) = Q from rfl, hH, Nat.cast_add, Nat.cast_one] using ha
  refine le_trans (prEvent_mono _ _ (fun r : Option (Trace Λ n ComVC L × Trace Λ n ComVC L) =>
      (∃ x₁ x₂, r = some (x₁, x₂) ∧ x₁.vec ≠ x₂.vec) ∨
      (∃ x₁ x₂, r = some (x₁, x₂) ∧ x₁.vec = x₂.vec)) ?_) ?_
  · rintro (_ | ⟨x₁, x₂⟩) hsome
    · simp at hsome
    · by_cases hv : x₁.vec = x₂.vec
      · exact Or.inr ⟨x₁, x₂, rfl, hv⟩
      · exact Or.inl ⟨x₁, x₂, rfl, hv⟩
  refine le_trans (prEvent_or_le _ _ _) ?_
  exact add_le_add (prEvent_diffVec_le_forkVecPair C vc chk A Q ckVC)
    (prEvent_sameVec_contextFork_le C vc chk A Q hSound ckVC)

/-- **Headline forking bound for the committed soundness game.** If the code
checker is `δ`-sound and the adversary makes at most `Q` random-oracle
queries, then the winning probability `acc` of the non-interactive committed
soundness game satisfies

  `acc * (acc / (Q + 1) - |L|⁻¹) ≤ Pr[collision] + δ`

against the explicit collision reduction `forkCollisionReduction`. -/
theorem niCommittedSoundness_forking_bound {δ : ℝ≥0∞}
    (hSound : chk.Sound C δ) (hA : ∀ ckVC, HashQueryBound (A ckVC) Q) :
    niCommittedSoundnessExp C vc chk A {true} *
      (niCommittedSoundnessExp C vc chk A {true} / (Q + 1) -
        (Fintype.card L : ℝ≥0∞)⁻¹) ≤
      Pr{let x ← vc.collisionExp (forkCollisionReduction C vc chk A Q)}[x = true] + δ := by
  classical
  set acc : CkVC → ℝ≥0∞ := fun ckVC =>
    Pr{let t ← runTrace C vc chk A ckVC}[(forkPoint Q t).isSome] with hacc
  set B : CkVC → ℝ≥0∞ := fun ckVC =>
    Pr{let x ← (forkVecPair C vc chk A Q ckVC >>= fun vv =>
      pure (decide (vv.1 ≠ vv.2) &&
        decide (vc.commit ckVC vv.1 = vc.commit ckVC vv.2)))}[x = true] with hB
  have hLHS : niCommittedSoundnessExp C vc chk A {true} =
      ∑' ckVC, Pr{let x ← vc.setup}[x = ckVC] * acc ckVC := by
    rw [niCommittedSoundnessExp_true_eq_tsum]
    exact tsum_congr fun ckVC => congrArg _ (prEvent_congr_of_support _ _ _
      (fun t ht => win_iff_forkPoint_isSome C vc chk ckVC (hA ckVC) ht))
  have hRHS : Pr{let x ← vc.collisionExp (forkCollisionReduction C vc chk A Q)}[x = true] =
      ∑' ckVC, Pr{let x ← vc.setup}[x = ckVC] * B ckVC := by
    unfold VectorCommitment.collisionExp
    rw [OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun ckVC => congrArg _ ?_
    show Pr{let x ← (forkCollisionReduction C vc chk A Q ckVC >>= fun vv =>
      pure (decide (vv.1 ≠ vv.2) &&
        decide (vc.commit ckVC vv.1 = vc.commit ckVC vv.2)))}[x = true] = B ckVC
    have hsim : (forkCollisionReduction C vc chk A Q ckVC >>= fun vv =>
        pure (decide (vv.1 ≠ vv.2) &&
          decide (vc.commit ckVC vv.1 = vc.commit ckVC vv.2))) =
        simulateQ (QueryImpl.ofLift unifSpec ProbComp +
          uniformSampleImpl (spec := ((Unit →ₒ L) : OracleSpec Unit)))
          (forkVecPair C vc chk A Q ckVC >>= fun vv =>
            pure (decide (vv.1 ≠ vv.2) &&
              decide (vc.commit ckVC vv.1 = vc.commit ckVC vv.2))) := by
      rw [simulateQ_bind]
      simp only [simulateQ_pure]
      rfl
    rw [hsim, prEvent_simulateQ_unifImpl]
  have hper : ∀ ckVC, acc ckVC * (acc ckVC / ((Q : ℝ≥0∞) + 1) -
      (Fintype.card L : ℝ≥0∞)⁻¹) ≤ B ckVC + δ := fun ckVC =>
    perKey_forking_bound C vc chk A Q hSound ckVC
  rw [hLHS, hRHS]
  let : MeasurableSpace CkVC := ⊤
  have hjensen := OracleComp.EvalDist.marginalized_jensen_forking_bound_of_discrete
    vc.setup acc (fun ckVC => B ckVC + δ) ((Q : ℝ≥0∞) + 1)
    ((Fintype.card L : ℝ≥0∞)⁻¹) (fun _ => prEvent_le_one _) hper
  rw [lintegral_evalDist_eq_tsum, lintegral_evalDist_eq_tsum] at hjensen
  refine le_trans hjensen ?_
  calc ∑' ckVC, Pr{let x ← vc.setup}[x = ckVC] * (B ckVC + δ)
      = (∑' ckVC, Pr{let x ← vc.setup}[x = ckVC] * B ckVC) +
        ∑' ckVC, Pr{let x ← vc.setup}[x = ckVC] * δ := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add]
    _ ≤ (∑' ckVC, Pr{let x ← vc.setup}[x = ckVC] * B ckVC) + δ := by
        refine add_le_add le_rfl ?_
        rw [ENNReal.tsum_mul_right]
        exact le_trans (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl) (one_mul δ).le

end forking

end CommittedSoundness

end PqDas
