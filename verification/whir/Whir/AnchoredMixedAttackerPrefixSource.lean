import Whir.AnchoredMixedAttackerPrefix

/-! Quiet source join for the unchanged PublicCompressionCouplingMixed.compile.
Cache-hit ordinary observations need not be draws. Their omission preserves
set membership, not literal log order. Outside OutputCollision in the SAME
complete actual ordinary trace, digest-selected preimages and freeze.raw are
extensional in this membership set. All cache/prefix invariants below are
derived from the actual simulator lowering; no frozenRootEq is a premise.
Construction answers never supply ordinary compression records. -/
namespace Whir.AnchoredMixedAttackerPrefixSource
open Concrete FiatShamirGame DuplexModeGame TypedOracleCompiler
open AnchoredMixedAttackerPrefix AnchoredHeaderRoots
open PublicMerkleLog MerkleTransport.Commitments MerkleQueryLogExtraction

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Literal zero-role compression records only; no construction output key
is admitted merely because it appears in a public observation. -/
def ordinaryLog (log : DuplexPublicSimulator.PublicLog) : PublicMerkleLog.PublicLog :=
  log.filter (fun e => DuplexFraming.tag e.1 = 0)

theorem ordinaryLog_authentic (seed : PrimitiveOracle) (log : DuplexPublicSimulator.PublicLog)
    (auth : PCSBCSMerkleSeedProjection.OrdinaryAuthentic seed log) :
    AuthenticLog seed (ordinaryLog log) := by
  intro n d member
  obtain ⟨present,ordinary⟩ := List.mem_filter.mp member
  exact auth n d present (by simpa using ordinary)

theorem quiet_mono (left right : PublicLog) (included : ∀ e ∈ left, e ∈ right)
    (quiet : ¬ OutputCollision right) : ¬ OutputCollision left := by
  rintro ⟨a,b,d,ha,hb,different⟩
  exact quiet ⟨a,b,d,included _ ha,included _ hb,different⟩

/-- This internal extensionality lemma makes its collision guard explicit.
The public source theorem below derives both authenticity and membership. -/
theorem quiet_index (seed : PrimitiveOracle) (left right : PublicLog)
    (leftAuth : AuthenticLog seed left) (rightAuth : AuthenticLog seed right)
    (same : ∀ e, e ∈ left ↔ e ∈ right) (quiet : ¬ OutputCollision right) (d : Digest32) :
    (build (records left))[key d]? = (build (records right))[key d]? := by
  have leftQuiet := quiet_mono left right (fun e member => (same e).mp member) quiet
  have lr := PublicMerkleBinding.records_persist seed left right leftAuth rightAuth
    (fun e member => (same e).mp member) quiet
  have rl := PublicMerkleBinding.records_persist seed right left rightAuth leftAuth
    (fun e member => (same e).mpr member) leftQuiet
  have leftUnique := fun bad => leftQuiet (PublicMerkleBinding.reconstructed_collision seed left leftAuth bad)
  have rightUnique := fun bad => quiet (PublicMerkleBinding.reconstructed_collision seed right rightAuth bad)
  cases l : (build (records left))[key d]? with
  | some bytes =>
    have member := lr _ (build_mem l)
    exact (selected_unique (PublicMerkleLog.hash seed) (records right)
      (records_authentic seed right rightAuth) rightUnique member).symm
  | none =>
    cases r : (build (records right))[key d]? with
    | none => rfl
    | some bytes =>
      have member := rl _ (build_mem r)
      have found := selected_unique (PublicMerkleLog.hash seed) (records left)
        (records_authentic seed left leftAuth) leftUnique member
      rw [l] at found
      contradiction

theorem extract_lookup_ext (codec : Codec) (left right : Index)
    (same : ∀ d, left[key d]? = right[key d]?) (height : Nat) (root : Digest32) :
    extract codec left height root = extract codec right height root := by
  induction height generalizing root with
  | zero => simp only [extract,same]
  | succ height ih => simp only [extract,same,ih]

theorem quiet_freeze_raw (seed : PrimitiveOracle) (left right : PublicLog)
    (leftAuth : AuthenticLog seed left) (rightAuth : AuthenticLog seed right)
    (same : ∀ e, e ∈ left ↔ e ∈ right) (quiet : ¬ OutputCollision right)
    (root : Digest32) (shape : PCSBCSMerkleRootCache.Shape) :
    (PCSBCSMerkleRootCache.freeze left root shape).raw =
      (PCSBCSMerkleRootCache.freeze right root shape).raw := by
  have tree := extract_lookup_ext canonicalCodec (build (records left)) (build (records right))
    (quiet_index seed left right leftAuth rightAuth same quiet) shape.height root
  have cells : PCSBCSMerkleLeafImages.sourceCells left root shape.height shape.leafWords shape.occupied =
      PCSBCSMerkleLeafImages.sourceCells right root shape.height shape.leafWords shape.occupied := by
    simp only [PCSBCSMerkleLeafImages.sourceCells,PCSBCSMerkleLeafImages.extractCells_eq_emit]
    rw [tree]
  change PCSBCSMerkleLeafImages.compactTable
      (PCSBCSMerkleLeafImages.sourceCells left root shape.height shape.leafWords shape.occupied) =
    PCSBCSMerkleLeafImages.compactTable
      (PCSBCSMerkleLeafImages.sourceCells right root shape.height shape.leafWords shape.occupied)
  rw [cells]

structure PrefixInvariant (seed : PrimitiveOracle)
    (log : DuplexPublicSimulator.PublicLog) (past : AnchoredMixedAttackerPrefix.History Q) : Prop where
  ordinary : PCSBCSMerkleSeedProjection.OrdinaryAuthentic seed log
  authentic : AuthenticLog seed (ordinaryPrefix past)
  members : ∀ e, e ∈ ordinaryPrefix past ↔ e ∈ ordinaryLog log

theorem ordinary_lookup_consistent (seed : PrimitiveOracle)
    (log : DuplexPublicSimulator.PublicLog) (past : AnchoredMixedAttackerPrefix.History Q)
    (invariant : PrefixInvariant seed log past) (input : DuplexFraming.Node)
    (ordinary : DuplexFraming.tag input = 0) :
    PublicMerkleLog.lookup (ordinaryPrefix past) input = DuplexPublicSimulator.lookup log input := by
  cases hit : DuplexPublicSimulator.lookup log input with
  | some answer =>
    have present := DuplexPublicSimulator.lookup_mem hit
    have member := (invariant.members (input,answer)).mpr
      (List.mem_filter.mpr ⟨present,by simpa using ordinary⟩)
    have correct := invariant.ordinary input answer present ordinary
    simpa [correct] using PublicMerkleLog.lookup_authentic_member seed _ invariant.authentic member
  | none =>
    cases old : PublicMerkleLog.lookup (ordinaryPrefix past) input with
    | none => rfl
    | some answer =>
      have present := (List.mem_filter.mp
        ((invariant.members _).mp (PublicMerkleLog.lookup_mem old))).1
      obtain ⟨answer,found⟩ := DuplexPublicSimulator.lookup_exists present
      rw [hit] at found
      contradiction

def traceHistory (past : AnchoredMixedAttackerPrefix.History Q)
    (events : List (Sigma (fun _ : PublicCompressionCouplingMixed.Key Q => Digest32))) :=
  events.foldl (fun prior e => (e.1,e.2)::prior) past

theorem traceHistory_append (past : AnchoredMixedAttackerPrefix.History Q)
    (left right : List (Sigma (fun _ : PublicCompressionCouplingMixed.Key Q => Digest32))) :
    traceHistory past (left++right) = traceHistory (traceHistory past left) right := by
  simp only [traceHistory,List.foldl_append]

theorem traceHistory_cons (past : AnchoredMixedAttackerPrefix.History Q)
    (event : Sigma (fun _ : PublicCompressionCouplingMixed.Key Q => Digest32)) (events) :
    traceHistory past (event::events) = traceHistory ((event.1,event.2)::past) events := rfl

theorem execute_map_trace (table : PublicCompressionCouplingMixed.Key Q → Digest32)
    (f : R → S) (source : PublicCompressionCouplingMixed.Computation Q R n) :
    (Sampling.execute table (PublicCompressionCouplingMixed.Computation.map f source)).2 =
      (Sampling.execute table source).2 := by
  induction source with
  | ret result => rfl
  | draw key next ih => simp only [PublicCompressionCouplingMixed.Computation.map,Sampling.execute,ih]

/-- Operational reference only: these are exactly the already completed draws
of primitiveCalls. Neither the attacker nor preparation receives the seed. -/
def primitiveHistory (Q : Nat) (seed : DuplexPublicSimulator.Seed) (ro : RawKey Q → Digest32)
    (log : DuplexPublicSimulator.PublicLog) (past : AnchoredMixedAttackerPrefix.History Q)
    (input : DuplexFraming.Node) : AnchoredMixedAttackerPrefix.History Q :=
  match DuplexPublicSimulator.lookup log input with
  | some _ => past
  | none => match DuplexPublicSimulator.privateKey Q log input with
    | some raw => (.inr raw,ro raw)::past
    | none => (.inl input,seed input)::past

theorem primitiveHistory_actual (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (log : DuplexPublicSimulator.PublicLog)
    (past : AnchoredMixedAttackerPrefix.History Q) (input : DuplexFraming.Node) :
    primitiveHistory Q seed ro log past input = traceHistory past
      (Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.primitiveCalls Q log input)).2 := by
  cases hit : DuplexPublicSimulator.lookup log input with
  | some answer => simp [primitiveHistory,PublicCompressionCouplingMixed.primitiveCalls,hit,
      Sampling.execute,traceHistory]
  | none =>
    cases key : DuplexPublicSimulator.privateKey Q log input <;>
      simp [primitiveHistory,PublicCompressionCouplingMixed.primitiveCalls,hit,key,
        Sampling.execute,traceHistory,PublicCompressionCouplingMixed.oracle]

theorem primitive_log (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (log : DuplexPublicSimulator.PublicLog)
    (input : DuplexFraming.Node) :
    let reply := Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.primitiveCalls Q log input)
    reply.1 = DuplexPublicSimulator.observe log input reply.2 := by
  cases hit : DuplexPublicSimulator.lookup log input with
  | some answer => simp [PublicCompressionCouplingMixed.primitiveCalls,hit,Sampling.eval]
  | none =>
    cases key : DuplexPublicSimulator.privateKey Q log input <;>
      simp [PublicCompressionCouplingMixed.primitiveCalls,hit,key,Sampling.eval]

/-- Exact accumulated raw/primitive draw history of the unchanged lowering.
This reference evaluator is not an attacker or preparation argument. -/
def finishHistory (Q : Nat) (iv : Digest32) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (log : DuplexPublicSimulator.PublicLog)
    (past : AnchoredMixedAttackerPrefix.History Q) :
    (program : Program R) → (remaining : Nat) → remaining ≤ Q → Counts remaining program →
      AnchoredMixedAttackerPrefix.History Q
  | .done _, _, _, _ => past
  | .ask (.primitive _ input) next, remaining, cap, counted =>
    let reply := Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
      (PublicCompressionCouplingMixed.primitiveCalls Q log input)
    finishHistory Q iv seed ro reply.1 (primitiveHistory Q seed ro log past input)
      (next reply.2) (remaining-1) (by omega) (counted.2 _)
  | .ask (.construction coordinate _) next, remaining, cap, counted =>
    let raw := constructionKey Q iv coordinate (counted.1.trans cap)
    finishHistory Q iv seed ro log ((.inr raw,ro raw)::past)
      (next (ro raw)) (remaining-DuplexFraming.pathCost coordinate) (by omega) (counted.2 _)

theorem finishHistory_actual (Q : Nat) (iv : Digest32) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (log : DuplexPublicSimulator.PublicLog)
    (past : AnchoredMixedAttackerPrefix.History Q) (program : Program R)
    (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining program) :
    finishHistory Q iv seed ro log past program remaining cap counted =
      traceHistory past (Sampling.execute (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile Q iv log program remaining cap counted)).2 := by
  induction program generalizing log past remaining with
  | done => rfl
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [finishHistory,PublicCompressionCouplingMixed.compile,Sampling.execute_pad,
        Sampling.execute_bind,execute_map_trace,traceHistory_append]
      rw [← primitiveHistory_actual]
      exact ih _ _ _ _ _ _
    | construction coordinate valid =>
      simp only [finishHistory,PublicCompressionCouplingMixed.compile,Sampling.execute_pad,
        Sampling.execute,execute_map_trace,PublicCompressionCouplingMixed.oracle,traceHistory_cons]
      exact ih _ _ _ _ _ _

theorem initial_invariant (seed : PrimitiveOracle) :
    PrefixInvariant seed [] ([] : AnchoredMixedAttackerPrefix.History Q) := by
  constructor <;> simp [PCSBCSMerkleSeedProjection.OrdinaryAuthentic,AuthenticLog,
    ordinaryPrefix,ordinaryLog]

theorem primitive_invariant (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (log : DuplexPublicSimulator.PublicLog)
    (past : AnchoredMixedAttackerPrefix.History Q) (input : DuplexFraming.Node)
    (invariant : PrefixInvariant seed log past) :
    PrefixInvariant seed
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.primitiveCalls Q log input)).1
      (primitiveHistory Q seed ro log past input) := by
  refine ⟨(PCSBCSMerkleSeedProjection.primitiveCalls_preserves Q seed ro log invariant.ordinary input).1,?_,?_⟩
  · cases hit : DuplexPublicSimulator.lookup log input with
    | some answer => simpa [primitiveHistory,hit] using invariant.authentic
    | none =>
      cases key : DuplexPublicSimulator.privateKey Q log input with
      | some raw => simpa [primitiveHistory,hit,key] using invariant.authentic
      | none =>
        intro n d member
        simp only [primitiveHistory,hit,key,ordinaryPrefix,List.filterMap_cons] at member
        by_cases ordinary : DuplexFraming.tag input = 0
        · simp only [ordinary,↓reduceIte,List.mem_cons,Prod.mk.injEq] at member
          rcases member with ⟨rfl,rfl⟩ | prior
          · rfl
          · exact invariant.authentic n d prior
        · simp only [ordinary,↓reduceIte] at member
          exact invariant.authentic n d member
  · intro e
    cases hit : DuplexPublicSimulator.lookup log input with
    | some answer =>
      have present := DuplexPublicSimulator.lookup_mem hit
      by_cases ordinary : DuplexFraming.tag input = 0
      · have old : (input,answer) ∈ ordinaryPrefix past :=
          (invariant.members _).mpr (List.mem_filter.mpr ⟨present,by simpa using ordinary⟩)
        have members : e ∈ ordinaryPrefix past ↔ e ∈ log ∧ DuplexFraming.tag e.1 = 0 := by
          simpa [ordinaryLog] using invariant.members e
        simp [primitiveHistory,hit,PublicCompressionCouplingMixed.primitiveCalls,Sampling.eval,
          ordinaryLog,DuplexPublicSimulator.observe,ordinary]
        exact ⟨fun member => Or.inr (members.mp member),
          fun member => member.elim (fun same => by simpa [same] using old) members.mpr⟩
      · simpa [primitiveHistory,hit,PublicCompressionCouplingMixed.primitiveCalls,Sampling.eval,
          ordinaryLog,DuplexPublicSimulator.observe,ordinary] using invariant.members e
    | none =>
      by_cases ordinary : DuplexFraming.tag input = 0
      · have key := PCSBCSMixedOrdinaryMerkle.ordinary_privateKey_none Q log input ordinary
        simpa [primitiveHistory,hit,key,PublicCompressionCouplingMixed.primitiveCalls,Sampling.eval,
          PublicCompressionCouplingMixed.oracle,ordinaryPrefix,ordinaryLog,
          DuplexPublicSimulator.observe,ordinary] using or_congr Iff.rfl (invariant.members e)
      · cases key : DuplexPublicSimulator.privateKey Q log input <;>
          simpa [primitiveHistory,hit,key,PublicCompressionCouplingMixed.primitiveCalls,Sampling.eval,
            PublicCompressionCouplingMixed.oracle,ordinaryPrefix,ordinaryLog,
            DuplexPublicSimulator.observe,ordinary] using invariant.members e

theorem raw_invariant (seed : PrimitiveOracle) (log : DuplexPublicSimulator.PublicLog)
    (past : AnchoredMixedAttackerPrefix.History Q) (raw : RawKey Q) (answer : Digest32)
    (invariant : PrefixInvariant seed log past) :
    PrefixInvariant seed log ((.inr raw,answer)::past) := by
  exact ⟨invariant.ordinary,by simpa using invariant.authentic,
    fun e => by simpa using invariant.members e⟩

/-- At first registration, the quiet full ordinary observation log and the
strict completed-draw log produce identical root tables. Authenticity and
set matching are fields of the DERIVED cache invariant, not caller promises. -/
theorem first_freeze_full_log (registry : Public) (seed : PrimitiveOracle)
    (log : DuplexPublicSimulator.PublicLog) (past : AnchoredMixedAttackerPrefix.History Q)
    (invariant : PrefixInvariant seed log past) (full : PublicLog)
    (included : ∀ e ∈ ordinaryLog log, e ∈ full) (quiet : ¬ OutputCollision full)
    (header : Header) (absent : (replay registry past).roots[
      PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? = none) :
    (frozenHeader registry past header).raw =
      (PCSBCSMerkleRootCache.freeze (ordinaryLog log) header.root (rootShape header)).raw := by
  rw [frozenHeader_first registry past header absent]
  exact quiet_freeze_raw seed _ _ invariant.authentic (ordinaryLog_authentic seed log invariant.ordinary)
    invariant.members (quiet_mono _ full included quiet) _ _

/-- This is an operational prequery invariant for the ACTUAL source lowering.
At constructions the raw key is the literal constructionKey, and preparation
is checked before recurring on the answer; no before-point certificate occurs
among the hypotheses of initial_source_prefixes below. -/
def SourcePrefixes (registry : Public) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (full : PublicLog)
    (log : DuplexPublicSimulator.PublicLog) (past : AnchoredMixedAttackerPrefix.History Q) :
    (program : Program R) → (remaining : Nat) → remaining ≤ Q → Counts remaining program → Prop
  | .done _, _, _, _ => PrefixInvariant seed log past
  | .ask (.primitive _ input) next, remaining, cap, counted =>
    PrefixInvariant seed log past ∧
      (∀ header, (replay registry past).roots[
        PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? = none →
        (frozenHeader registry past header).raw =
          (PCSBCSMerkleRootCache.freeze (ordinaryLog log) header.root (rootShape header)).raw) ∧
      let reply := Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.primitiveCalls Q log input)
      SourcePrefixes registry seed ro full reply.1 (primitiveHistory Q seed ro log past input)
        (next reply.2) (remaining-1) (by omega) (counted.2 _)
  | .ask (.construction coordinate _) next, remaining, cap, counted =>
    PrefixInvariant seed log past ∧
      (∀ header, (replay registry past).roots[
        PCSBCSMerkleRootCache.cacheKey header.root (rootShape header)]? = none →
        (frozenHeader registry past header).raw =
          (PCSBCSMerkleRootCache.freeze (ordinaryLog log) header.root (rootShape header)).raw) ∧
      let raw := constructionKey Q registry.iv coordinate (counted.1.trans cap)
      SourcePrefixes registry seed ro full log ((.inr raw,ro raw)::past)
        (next (ro raw)) (remaining-DuplexFraming.pathCost coordinate) (by omega) (counted.2 _)

theorem ordinaryObservations_tail (observation : Observation) (seen : List Observation) :
    ∀ e ∈ PCSBCSMerkleSeedProjection.ordinaryObservations seen,
      e ∈ PCSBCSMerkleSeedProjection.ordinaryObservations (observation::seen) := by
  intro e member
  obtain ⟨o,present,parsed⟩ := List.mem_filterMap.mp member
  exact List.mem_filterMap.mpr ⟨o,List.mem_cons_of_mem _ present,parsed⟩

theorem source_prefixes (registry : Public) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (full : PublicLog)
    (log : DuplexPublicSimulator.PublicLog) (past : AnchoredMixedAttackerPrefix.History Q)
    (program : Program R) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining program) (invariant : PrefixInvariant seed log past)
    (included : ∀ e ∈ ordinaryLog log, e ∈ full)
    (future : ∀ e ∈ PCSBCSMerkleSeedProjection.ordinaryObservations
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile Q registry.iv log program remaining cap counted)).observations,
      e ∈ full) (quiet : ¬ OutputCollision full) :
    SourcePrefixes registry seed ro full log past program remaining cap counted := by
  induction program generalizing log past remaining with
  | done => exact invariant
  | ask query next ih =>
    have freeze := fun header absent =>
      first_freeze_full_log registry seed log past invariant full included quiet header absent
    cases query with
    | primitive purpose input =>
      refine ⟨invariant,freeze,?_⟩
      let reply := Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.primitiveCalls Q log input)
      have after := primitive_invariant Q seed ro log past input invariant
      simp only [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval_bind,
        PublicCompressionCouplingMixed.Computation.eval_map,DuplexRawProgram.observe] at future
      apply ih reply.2 reply.1 (primitiveHistory Q seed ro log past input)
        (remaining-1) (by omega) (counted.2 _) after
      · intro e member
        obtain ⟨present,ordinary⟩ := List.mem_filter.mp member
        rw [primitive_log Q seed ro log input] at present
        rcases List.mem_cons.mp present with same | prior
        · subst e
          apply future
          have ordinaryTag : DuplexFraming.tag input = 0 := by simpa using ordinary
          simp [PCSBCSMerkleSeedProjection.ordinaryObservations,ordinaryTag]
        · exact included e (List.mem_filter.mpr ⟨prior,ordinary⟩)
      · intro e member
        exact future e (ordinaryObservations_tail _ _ e member)
    | construction coordinate valid =>
      refine ⟨invariant,freeze,?_⟩
      simp only [PublicCompressionCouplingMixed.compile,Sampling.eval_pad,Sampling.eval,
        PublicCompressionCouplingMixed.oracle,PublicCompressionCouplingMixed.Computation.eval_map,
        DuplexRawProgram.observe] at future
      apply ih _ log _ _ _ _ (raw_invariant seed log past _ _ invariant) included
      intro e member
      exact future e (ordinaryObservations_tail _ _ e member)

/-- SAME complete source trace, with no extra source/header policy hypothesis.
The only guard is the existing paid ordinary output-collision alarm being quiet.
Every first root table equals extraction from its actual earlier full ordinary
observation prefix, including cache hits, BEFORE its current point reply. -/
theorem initial_source_prefixes (registry : Public) (seed : DuplexPublicSimulator.Seed)
    (ro : RawKey Q → Digest32) (program : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining program) :
    let full := PCSBCSMerkleSeedProjection.ordinaryObservations
      (Sampling.eval (PublicCompressionCouplingMixed.oracle seed ro)
        (PublicCompressionCouplingMixed.compile Q registry.iv [] program remaining cap counted)).observations
    ¬ OutputCollision full →
      SourcePrefixes registry seed ro full [] [] program remaining cap counted := by
  intro full quiet
  exact source_prefixes registry seed ro full [] [] program remaining cap counted
    (initial_invariant seed) (by simp [ordinaryLog]) (fun _ member => member) quiet

#print axioms quiet_index
#print axioms quiet_freeze_raw
#print axioms primitiveHistory_actual
#print axioms primitive_invariant
#print axioms ordinary_lookup_consistent
#print axioms finishHistory_actual
#print axioms first_freeze_full_log
#print axioms source_prefixes
#print axioms initial_source_prefixes

end Whir.AnchoredMixedAttackerPrefixSource
