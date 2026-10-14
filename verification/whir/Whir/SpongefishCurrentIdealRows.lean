import Whir.SpongefishCurrentGoodEvent
import Whir.SpongefishCurrentOpeningExperiment
import Whir.SpongefishCurrentOpeningPackets
import Whir.PCSBCSCapturedNativePhaseQuery
import Whir.PCSBCSRestorationLiteralPath
import Whir.PCSRoundByRoundPublicEndpoint

/-! Ideal-world opened rows of the current #607 opening walk. On every table of a packet partition, the full source view's returned walk is the pure evaluation of the opening walk with the view's public seed, and every hashed opening input has its primitive plan among the view's observations. The opening of level `i` sits at reply position `position (.query i)`, reads the walk root `roots[i]` and the tape's query sample. Against the first-mention capture of that root (taken as a hypothesis), the quiet event binds the opened rows to the decoded frozen oracle; together with the native equations of the good event this is an accepted causal experiment, and extraction failure on the frozen Root0 image makes the literal final public state true. -/
namespace Whir.SpongefishCurrentIdealRows
open Concrete Protocol CausalGame FiatShamirGame DuplexModeGame DuplexFraming SpongefishPCSRoundFrames
open SpongefishCurrentOpeningAcceptance SpongefishCurrentOpeningProgram PrunedMerkleProgram
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache TypedOracleCompiler
set_option autoImplicit false

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

/-! ## Primitive answers of an ideal source view -/

/-- Every primitive observation of a source view, on an arbitrary partition table, is answered by the view's public seed. -/
theorem source_seed {Q : Nat} {Packet : Type} {Block : Packet → Type}
    (part : RawOracleCoupling.Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
    {R : Type} (iv : Digest32) (program : Program R) (counted : Counts Q program)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) (purpose : Purpose) (n : Node)
    (a : Digest32)
    (member : (⟨.primitive purpose n,a⟩ : Observation) ∈
      (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program counted)).observations) :
    PCSBCSPublicPrimitiveOpening.publicSeed
      (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program counted)) n = a := by
  unfold PCSBCSPublicPrimitiveOpening.publicSeed
  rw [SpongefishCurrentOpeningPackets.eval_source] at member ⊢
  exact PCSBCSObservedPrimitiveExtension.extension_of_mem _
    (DuplexPublicSimulator.finalLog_functional (SpongefishCurrentOpeningPackets.roOf part table) iv
      ⟨SpongefishCurrentOpeningPackets.seedOf part table,[]⟩ program Q (Nat.le_refl Q) counted (by
        intro _ _ _ absent
        cases absent))
    (PCSBCSObservedPrimitiveExtension.primitive_in_finalLog [] _ purpose n a member)

/-- A source view is a run of its program. -/
theorem source_runs {Q : Nat} {Packet : Type} {Block : Packet → Type}
    (part : RawOracleCoupling.Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
    {R : Type} (iv : Digest32) (program : Program R) (counted : Counts Q program)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) :
    PublicMerkleProgram.Runs program
      (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program counted)).observations
      (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program counted)).result := by
  rw [SpongefishCurrentOpeningPackets.eval_source]
  exact PublicMerkleProgram.runIdeal_runs _ _ _ _ _ _ _ _

/-! ## Consistent hash-program runs -/

/-- A run of a lowered hash program whose primitive answers agree with `C` is the pure evaluation with `hash C`, and its trace contains the real primitive plan of every whole-hash call. -/
theorem consistent_eval {R : Type} (C : PrimitiveOracle) (h : HashProgram R)
    (trace : List Observation) (result : R) (run : PublicMerkleProgram.Runs h.lower trace result)
    (answers : ∀ purpose n a, (⟨.primitive purpose n,a⟩ : Observation) ∈ trace → C n = a) :
    HashProgram.eval (PublicMerkleLog.hash C) h = result ∧
    ∀ bytes ∈ HashProgram.calls (PublicMerkleLog.hash C) h, ∀ e ∈ PublicMerkleLog.plan C bytes,
      (⟨.primitive .verification e.1,e.2⟩ : Observation) ∈ trace := by
  have verification := ((HashProgram.lower_runs_iff h trace result).mp run).verification
  obtain ⟨real,observed⟩ := run.real_result_trace C DuplexRefinement.zeroDigest (by
    intro o member
    obtain ⟨n,query⟩ := verification o member
    obtain ⟨q,a⟩ := o
    dsimp only at query ⊢
    subst query
    exact (answers .verification n a member).symm)
  refine ⟨(HashProgram.lower_real C DuplexRefinement.zeroDigest h).symm.trans real,?_⟩
  intro bytes call e planned
  rw [← observed,HashProgram.real_observations]
  exact List.mem_flatMap.mpr ⟨bytes,call,List.mem_map.mpr ⟨e,planned,rfl⟩⟩

/-- Any run of the full program returning a walk result, with primitive answers consistent with `C`, read the header root and evaluated the opening walk with `hash C` on the opening events; every whole-hash call's real plan is in the trace. -/
theorem full_walk (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (decode : Decoder) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (trace : List Observation)
    (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
    (run : PublicMerkleProgram.Runs (fullProgram iv tag instanceBytes layout before payloadCalls messages
      decode grinding prefixProgram) trace (some (.ok data),some col))
    (answers : ∀ purpose n a, (⟨.primitive purpose n,a⟩ : Observation) ∈ trace → C n = a) :
    ∃ root, headerRoot (rootIndex before) data.events = some root ∧
      HashProgram.eval (PublicMerkleLog.hash C) (walk decode grinding (AnchoredSourceCaller.shape layout).lanes
        root (openingEvents (openingOffset layout before payloadCalls messages) data)) = some col ∧
      ∀ bytes ∈ HashProgram.calls (PublicMerkleLog.hash C) (walk decode grinding
          (AnchoredSourceCaller.shape layout).lanes root
          (openingEvents (openingOffset layout before payloadCalls messages) data)),
        ∀ e ∈ PublicMerkleLog.plan C bytes, (⟨.primitive .verification e.1,e.2⟩ : Observation) ∈ trace := by
  obtain ⟨first,res,after,split,_,phase⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp run
  subst split
  rcases res with _ | (failure | replayed)
  · cases phase
  · cases phase
  · cases hroot : headerRoot (rootIndex before) replayed.events with
    | none =>
      simp only [openingPhase,hroot] at phase
      cases phase
    | some root =>
      simp only [openingPhase,hroot] at phase
      obtain ⟨walkTrace,walked,rest,restEq,walkRun,done⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp phase
      cases done
      have inside : ∀ o ∈ walkTrace, o ∈ first ++ after := by
        intro o member
        rw [restEq]
        exact List.mem_append_right _ (List.mem_append_left _ member)
      obtain ⟨evaluated,planned⟩ := consistent_eval C _ walkTrace _ walkRun
        (fun purpose n a member => answers purpose n a (inside _ member))
      exact ⟨root,hroot,evaluated,fun bytes call e member => inside _ (planned bytes call e member)⟩

/-! ## The ideal full view -/

section Ideal
variable {Q : Nat} {Packet : Type} {Block : Packet → Type}
  (part : RawOracleCoupling.Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
  (iv : Digest32) (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
  (before payloadCalls messages : List Call) (decode : Decoder)
  (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
  (counted : Counts Q (fullProgram (p := p) iv tag instanceBytes layout before payloadCalls messages decode
    grinding prefixProgram))
  (table : (key : part.Key) → part.Answer (D := Digest32) key)

/-- The ideal source view of the full program on a partition table. -/
noncomputable def idealView : View (FullResult p) :=
  Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv
    (fullProgram (p := p) iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram) counted)

/-- Ideal walk semantics: the returned walk is the evaluation of the opening walk on the opening events with the view's public seed, and every whole-hash call of that walk has its real primitive plan among the view's observations. -/
theorem ideal_walk (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
    (result : (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram counted table).result = (some (.ok data),some col)) :
    ∃ root, headerRoot (rootIndex before) data.events = some root ∧
      HashProgram.eval (PublicMerkleLog.hash (PCSBCSPublicPrimitiveOpening.publicSeed
          (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
            prefixProgram counted table)))
        (walk decode grinding (AnchoredSourceCaller.shape layout).lanes root
          (openingEvents (openingOffset layout before payloadCalls messages) data)) = some col ∧
      ∀ bytes ∈ HashProgram.calls (PublicMerkleLog.hash (PCSBCSPublicPrimitiveOpening.publicSeed
          (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
            prefixProgram counted table)))
          (walk decode grinding (AnchoredSourceCaller.shape layout).lanes root
            (openingEvents (openingOffset layout before payloadCalls messages) data)),
        ∀ e ∈ PublicMerkleLog.plan (PCSBCSPublicPrimitiveOpening.publicSeed
            (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
              prefixProgram counted table)) bytes,
          (⟨.primitive .verification e.1,e.2⟩ : Observation) ∈
            (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
              prefixProgram counted table).observations := by
  have run := source_runs part iv _ counted table
  have seeded := source_seed part iv _ counted table
  unfold idealView at result ⊢
  rw [result] at run
  exact full_walk _ iv tag instanceBytes layout before payloadCalls messages decode grinding prefixProgram _
    data col run seeded

end Ideal

/-! ## Opening walk invariants -/

section Walk
variable (H : MerkleTransport.Primitive) (decode : Decoder)
  (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64) (lanes : Nat)

theorem array_prefix {α : Type} (a b : Array α) (n : Nat) (x : α) (h : a[n]? = some x) :
    (a ++ b)[n]? = some x := by
  have lt : n < a.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [Array.getElem?_append_left lt]
  exact h

theorem powWalk_shape (evs evs' : List SourceEvent) (col col' : Collected p) (q : Coord p)
    (ok : powWalk grinding evs col q = some (evs',col')) : ∃ pows, col' = {col with pows := pows} := by
  cases q with
  | query i =>
    simp only [powWalk] at ok
    split at ok
    · cases ok
      exact ⟨col.pows,rfl⟩
    · obtain ⟨⟨bytes,rest⟩,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      obtain ⟨⟨nonce,after⟩,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok
      exact ⟨_,rfl⟩
  | initial => cases ok; exact ⟨col.pows,rfl⟩
  | fold i j => cases ok; exact ⟨col.pows,rfl⟩
  | ood i j => cases ok; exact ⟨col.pows,rfl⟩
  | tail j => cases ok; exact ⟨col.pows,rfl⟩

theorem recordSample_fields (col : Collected p) (q : Coord p) (x : PCSBCSRounds.Raw q) :
    (recordSample col q x).tape = CausalProbability.set q col.tape (StackWHIRReplay.projectSample q x) ∧
    (recordSample col q x).replies = col.replies ∧ (recordSample col q x).roots = col.roots ∧
    (recordSample col q x).openings = col.openings := by
  cases q <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- A visible tail coordinate carries a prover reply. -/
theorem tail_visible (j : Fin ((ParameterBounds.config p).logN - (ParameterBounds.config p).folds.toList.sum))
    (member : (CausalProbability.Coordinate.tail j : Coord p) ∈
      CausalProbability.visibleCoordinates (ParameterBounds.config p)) :
    isVisibleTail j = true := by
  unfold CausalProbability.visibleCoordinates at member
  simp only [List.mem_append,List.mem_singleton,List.mem_flatMap,List.mem_ofFn] at member
  rcases member with (impossible | ⟨i,_,level⟩) | ⟨k,same⟩
  · cases impossible
  · unfold CausalProbability.levelCoordinates at level
    split at level <;> simp at level
  · injection same with same
    subst same
    have bound := k.isLt
    simp only [isVisibleTail,decide_eq_true_eq]
    omega

theorem replyPure_spec (evs evs' : List SourceEvent) (col col' : Collected p) (q : Coord p)
    (ok : replyPure evs col q = some (evs',col')) :
    col'.tape = col.tape ∧ col'.seed = col.seed ∧ col'.openings = col.openings ∧
    (∃ extra, col'.roots = col.roots ++ extra) ∧
    ∃ extra : Array Reply, col'.replies = col.replies ++ extra ∧
      (q ∈ CausalProbability.visibleCoordinates (ParameterBounds.config p) → extra.size = 1) := by
  cases q with
  | initial =>
    simp only [replyPure] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    exact ⟨rfl,rfl,rfl,⟨#[],by simp⟩,⟨_,Array.push_eq_append,fun _ => rfl⟩⟩
  | fold i j =>
    simp only [replyPure] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    split at ok
    · split at ok
      · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok
        exact ⟨rfl,rfl,rfl,⟨_,Array.push_eq_append⟩,⟨_,Array.push_eq_append,fun _ => rfl⟩⟩
      · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok
        exact ⟨rfl,rfl,rfl,⟨#[],by simp⟩,⟨_,Array.push_eq_append,fun _ => rfl⟩⟩
    · cases ok
      exact ⟨rfl,rfl,rfl,⟨#[],by simp⟩,⟨_,Array.push_eq_append,fun _ => rfl⟩⟩
  | ood i j =>
    simp only [replyPure] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok
    exact ⟨rfl,rfl,rfl,⟨#[],by simp⟩,⟨_,Array.push_eq_append,fun _ => rfl⟩⟩
  | query i => cases ok
  | tail j =>
    simp only [replyPure] at ok
    split at ok
    · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok
      exact ⟨rfl,rfl,rfl,⟨#[],by simp⟩,⟨_,Array.push_eq_append,fun _ => rfl⟩⟩
    · rename_i hidden
      cases ok
      exact ⟨rfl,rfl,rfl,⟨#[],by simp⟩,⟨#[],by simp,fun member => absurd (tail_visible j member) hidden⟩⟩

theorem replyQuery_spec (evs evs' : List SourceEvent) (col col' : Collected p)
    (i : Fin (ParameterBounds.config p).folds.size)
    (ok : HashProgram.eval H (replyQuery decode lanes evs col i) = some (evs',col')) :
    col'.tape = col.tape ∧ col'.seed = col.seed ∧ col'.roots = col.roots ∧
    ∃ (o : QueryOpening p) (m : Message E), col'.openings = col.openings ++ [o] ∧
      col'.replies = col.replies.push (.query o.opened.rows m) ∧ o.level = i ∧
      col.roots[i.val]? = some o.root ∧
      HashProgram.eval H (openProgram lanes i o.root o.proof
        (CausalProbability.get (.query i) col.tape)) = some o.opened := by
  cases hh : takeHintBytes evs with
  | none => simp [replyQuery,hh,HashProgram.eval] at ok
  | some hinted =>
    obtain ⟨hint,rest⟩ := hinted
    cases hd : decode (WHIRPhysicalVerifier.queryIndices p i (CausalProbability.get (.query i) col.tape))
        (rowWords lanes i) hint with
    | none => simp [replyQuery,hh,hd,HashProgram.eval] at ok
    | some proof =>
      cases hr : col.roots[i.val]? with
      | none => simp [replyQuery,hh,hd,hr,HashProgram.eval] at ok
      | some root =>
        simp only [replyQuery,hh,hd,hr,HashProgram.eval_map] at ok
        cases ho : HashProgram.eval H (openProgram lanes i root proof
            (CausalProbability.get (.query i) col.tape)) with
        | none => simp [ho] at ok
        | some opened =>
          simp only [ho] at ok
          obtain ⟨read,_,ok⟩ := Option.map_eq_some_iff.mp ok
          cases ok
          exact ⟨rfl,rfl,rfl,⟨i,root,hint,proof,opened⟩,read.1,rfl,rfl,rfl,rfl,ho⟩

/-- One walk step: the stepped coordinate is the only tape change, the seed invariant is kept, roots, openings and replies only grow, a visible coordinate pushes exactly one reply, and a query step pushes its authenticated rows together with one opening at the current root of its level. -/
theorem stepWalk_spec (state final : List SourceEvent × Collected p) (q : Coord p)
    (ok : HashProgram.eval H (stepWalk decode grinding lanes state q) = some final) :
    (∀ r, r ≠ q → CausalProbability.get r final.2.tape = CausalProbability.get r state.2.tape) ∧
    (SpongefishCurrentOpeningExperiment.SeedTape state.2 →
      SpongefishCurrentOpeningExperiment.SeedTape final.2) ∧
    (∃ extra, final.2.roots = state.2.roots ++ extra) ∧
    (∃ extra, final.2.openings = state.2.openings ++ extra) ∧
    (∃ extra : Array Reply, final.2.replies = state.2.replies ++ extra ∧
      (q ∈ CausalProbability.visibleCoordinates (ParameterBounds.config p) → extra.size = 1)) ∧
    (∀ i, q = .query i → ∃ (o : QueryOpening p) (m : Message E),
      final.2.openings = state.2.openings ++ [o] ∧
      final.2.replies = state.2.replies.push (.query o.opened.rows m) ∧ o.level = i ∧
      state.2.roots[i.val]? = some o.root ∧
      HashProgram.eval H (openProgram lanes i o.root o.proof
        (CausalProbability.get (.query i) final.2.tape)) = some o.opened) := by
  obtain ⟨evs0,col0⟩ := state
  obtain ⟨evsF,colF⟩ := final
  cases hp : powWalk grinding evs0 col0 q with
  | none => simp [stepWalk,hp,HashProgram.eval] at ok
  | some powed =>
    obtain ⟨evs,col⟩ := powed
    obtain ⟨pows,colEq⟩ := powWalk_shape grinding _ _ _ _ q hp
    subst colEq
    cases hd : drawWalk evs q with
    | none => simp [stepWalk,hp,hd,HashProgram.eval] at ok
    | some drawn =>
      obtain ⟨rest,x⟩ := drawn
      simp only [stepWalk,hp,hd] at ok
      obtain ⟨tapeEq,repliesEq,rootsEq,openingsEq⟩ := recordSample_fields {col0 with pows := pows} q x
      have seeded := SpongefishCurrentOpeningExperiment.recordSample_seedTape {col0 with pows := pows} q x
      by_cases isQuery : ∃ i, q = .query i
      · obtain ⟨i,rfl⟩ := isQuery
        obtain ⟨tape,seed,roots,o,m,openings,replies,level,rootAt,opened⟩ :=
          replyQuery_spec H decode lanes _ _ _ _ i ok
        dsimp only
        refine ⟨?_,?_,⟨#[],?_⟩,⟨[o],?_⟩,⟨#[.query o.opened.rows m],?_,fun _ => rfl⟩,?_⟩
        · intro r different
          rw [tape,tapeEq]
          exact CausalProbability.get_set_ne _ _ _ _ different
        · intro kept s found
          rw [tape]
          exact seeded kept s (seed ▸ found)
        · rw [roots,rootsEq]
          simp
        · rw [openings,openingsEq]
        · rw [replies,repliesEq,Array.push_eq_append]
        · intro i' same
          cases same
          refine ⟨o,m,?_,?_,level,?_,?_⟩
          · rw [openings,openingsEq]
          · rw [replies,repliesEq]
          · rw [← rootsEq]
            exact rootAt
          · rw [tape]
            exact opened
      · have pure : replyPure rest (recordSample {col0 with pows := pows} q x) q = some (evsF,colF) := by
          cases q with
          | query i => exact (isQuery ⟨i,rfl⟩).elim
          | initial => exact ok
          | fold i j => exact ok
          | ood i j => exact ok
          | tail j => exact ok
        obtain ⟨tape,seed,openings,⟨extraRoots,roots⟩,⟨extra,replies,size⟩⟩ :=
          replyPure_spec _ _ _ _ q pure
        dsimp only
        refine ⟨?_,?_,⟨extraRoots,?_⟩,⟨[],?_⟩,⟨extra,?_,size⟩,fun i same => (isQuery ⟨i,same⟩).elim⟩
        · intro r different
          rw [tape,tapeEq]
          exact CausalProbability.get_set_ne _ _ _ _ different
        · intro kept s found
          rw [tape]
          exact seeded kept s (seed ▸ found)
        · rw [roots,rootsEq]
        · rw [openings,openingsEq]
          simp
        · rw [replies,repliesEq]

theorem walkFrom_append (xs ys : List (Coord p)) (state : List SourceEvent × Collected p) :
    HashProgram.eval H (walkFrom decode grinding lanes (xs ++ ys) state) =
      (HashProgram.eval H (walkFrom decode grinding lanes xs state)).bind
        (fun mid => HashProgram.eval H (walkFrom decode grinding lanes ys mid)) := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,walkFrom,HashProgram.eval_bind]
    cases HashProgram.eval H (stepWalk decode grinding lanes state x) with
    | none => rfl
    | some mid => exact ih mid

theorem walkFrom_spec : ∀ (qs : List (Coord p)) (state final : List SourceEvent × Collected p),
    HashProgram.eval H (walkFrom decode grinding lanes qs state) = some final →
    (∀ r, r ∉ qs → CausalProbability.get r final.2.tape = CausalProbability.get r state.2.tape) ∧
    (SpongefishCurrentOpeningExperiment.SeedTape state.2 →
      SpongefishCurrentOpeningExperiment.SeedTape final.2) ∧
    (∃ extra, final.2.roots = state.2.roots ++ extra) ∧
    (∃ extra, final.2.openings = state.2.openings ++ extra) ∧
    (∃ extra : Array Reply, final.2.replies = state.2.replies ++ extra ∧
      ((∀ q ∈ qs, q ∈ CausalProbability.visibleCoordinates (ParameterBounds.config p)) →
        extra.size = qs.length))
  | [], state, final, ok => by
    simp only [walkFrom,HashProgram.eval,Option.some.injEq] at ok
    subst ok
    exact ⟨fun _ _ => rfl,id,⟨#[],by simp⟩,⟨[],by simp⟩,⟨#[],by simp,fun _ => rfl⟩⟩
  | q :: qs, state, final, ok => by
    simp only [walkFrom,HashProgram.eval_bind] at ok
    cases hs : HashProgram.eval H (stepWalk decode grinding lanes state q) with
    | none => simp [hs,HashProgram.eval] at ok
    | some mid =>
      simp only [hs] at ok
      obtain ⟨tape1,seed1,⟨r1,roots1⟩,⟨o1,openings1⟩,⟨e1,replies1,size1⟩,_⟩ :=
        stepWalk_spec H decode grinding lanes state mid q hs
      obtain ⟨tape2,seed2,⟨r2,roots2⟩,⟨o2,openings2⟩,⟨e2,replies2,size2⟩⟩ := walkFrom_spec qs mid final ok
      refine ⟨?_,fun kept => seed2 (seed1 kept),⟨r1 ++ r2,?_⟩,⟨o1 ++ o2,?_⟩,⟨e1 ++ e2,?_,?_⟩⟩
      · intro r absent
        rw [tape2 r (fun h => absent (List.mem_cons_of_mem _ h)),
          tape1 r (fun h => absent (h ▸ List.mem_cons_self))]
      · rw [roots2,roots1,Array.append_assoc]
      · rw [openings2,openings1,List.append_assoc]
      · rw [replies2,replies1,Array.append_assoc]
      · intro visible
        rw [Array.size_append,size1 (visible q List.mem_cons_self),
          size2 (fun q' h => visible q' (List.mem_cons_of_mem _ h)),List.length_cons]
        omega

/-- Reply position invariant of the opening walk: the query reply of level `i` is the reply at index `position (.query i)`; it carries the rows opened at the walk root of level `i` on the tape's query sample, and the corresponding opening is returned. The walk also keeps the commitment root as `roots[0]` and the seed invariant. -/
theorem walk_spec (root : Digest32) (evs : List SourceEvent) (col : Collected p)
    (ok : HashProgram.eval H (walk decode grinding lanes root evs) = some col) :
    col.roots[0]? = some root ∧ SpongefishCurrentOpeningExperiment.SeedTape col ∧
    ∀ i : Fin (ParameterBounds.config p).folds.size, ∃ (o : QueryOpening p) (m : Message E),
      o ∈ col.openings ∧ o.level = i ∧ col.roots[i.val]? = some o.root ∧
      col.replies[CausalProbability.position (CausalProbability.Coordinate.query i)]? =
        some (.query o.opened.rows m) ∧
      HashProgram.eval H (openProgram lanes i o.root o.proof
        (CausalProbability.get (.query i) col.tape)) = some o.opened := by
  unfold walk at ok
  rw [HashProgram.eval_map] at ok
  obtain ⟨final,walked,same⟩ := Option.map_eq_some_iff.mp ok
  subst same
  obtain ⟨_,seedAll,⟨_,rootsAll⟩,_,_⟩ := walkFrom_spec H decode grinding lanes _ _ final walked
  refine ⟨?_,seedAll (fun s found => by cases found),?_⟩
  · rw [rootsAll]
    exact array_prefix #[root] _ 0 root rfl
  intro i
  let schedule := WHIRHistory.schedule (ParameterBounds.config p)
  let k := CausalProbability.position (CausalProbability.Coordinate.query i : Coord p)
  have visibleQ : (CausalProbability.Coordinate.query i : Coord p) ∈
      CausalProbability.visibleCoordinates (ParameterBounds.config p) :=
    (CausalPrefix.visible_or_last _).resolve_right (by
      rintro ⟨j,same,_⟩
      cases same)
  have kLt : k < (CausalProbability.visibleCoordinates (ParameterBounds.config p)).length :=
    List.idxOf_lt_length_of_mem visibleQ
  have hk : k < schedule.length := by
    change k < (WHIRHistory.schedule (ParameterBounds.config p)).length
    unfold WHIRHistory.schedule
    rw [List.length_append]
    omega
  have atK : schedule[k] = CausalProbability.Coordinate.query i := by
    have found := WHIRHistory.schedule_get_position (CausalProbability.Coordinate.query i : Coord p)
    rw [List.getElem?_eq_getElem hk] at found
    exact Option.some.inj found
  have split : schedule = schedule.take k ++ CausalProbability.Coordinate.query i :: schedule.drop (k+1) := by
    rw [← atK,← List.drop_eq_getElem_cons hk,List.take_append_drop]
  have prefixVisible : ∀ q ∈ schedule.take k,
      q ∈ CausalProbability.visibleCoordinates (ParameterBounds.config p) := by
    intro q member
    change q ∈ (WHIRHistory.schedule (ParameterBounds.config p)).take k at member
    unfold WHIRHistory.schedule at member
    rw [List.take_append_of_le_length (Nat.le_of_lt kLt)] at member
    exact List.mem_of_mem_take member
  have nodup := WHIRHistory.schedule_nodup (ParameterBounds.config p)
  change schedule.Nodup at nodup
  rw [split] at nodup
  have fresh : CausalProbability.Coordinate.query i ∉ schedule.drop (k+1) :=
    (List.nodup_cons.mp (List.Nodup.of_append_right nodup)).1
  change HashProgram.eval H (walkFrom decode grinding lanes schedule _) = some final at walked
  rw [split,walkFrom_append] at walked
  obtain ⟨mid1,first,second⟩ := Option.bind_eq_some_iff.mp walked
  simp only [walkFrom,HashProgram.eval_bind] at second
  cases hs : HashProgram.eval H (stepWalk decode grinding lanes mid1 (CausalProbability.Coordinate.query i)) with
  | none => simp [hs,HashProgram.eval] at second
  | some mid2 =>
    simp only [hs] at second
    obtain ⟨_,_,_,_,⟨e1,replies1,size1⟩⟩ := walkFrom_spec H decode grinding lanes _ _ mid1 first
    obtain ⟨_,_,⟨r2,roots2⟩,_,_,query⟩ := stepWalk_spec H decode grinding lanes mid1 mid2 _ hs
    obtain ⟨o,m,openings2,replies2,level,rootAt,opened⟩ := query i rfl
    obtain ⟨tape3,_,⟨r3,roots3⟩,⟨o3,openings3⟩,⟨e3,replies3,_⟩⟩ :=
      walkFrom_spec H decode grinding lanes _ mid2 final second
    have size : mid1.2.replies.size = k := by
      rw [replies1,Array.size_append,size1 prefixVisible,List.length_take]
      simp only [Collected.start,List.size_toArray,List.length_nil,Nat.zero_add]
      omega
    refine ⟨o,m,?_,level,?_,?_,?_⟩
    · rw [openings3,openings2]
      simp
    · rw [roots3,roots2]
      exact array_prefix _ _ _ _ (array_prefix _ _ _ _ rootAt)
    · rw [replies3,replies2]
      apply array_prefix
      rw [show CausalProbability.position (CausalProbability.Coordinate.query i : Coord p) =
        mid1.2.replies.size from size.symm]
      exact Array.getElem?_push_size
    · rw [tape3 _ fresh]
      exact opened

end Walk

/-! ## Captured roots, their logs and their oracles -/

/-- Reference of the walk root of level `i`: Root0 at level 0, the announced level root otherwise. -/
def rootReference (p : ParameterBounds.Profile) (shape : SpongefishSessionAdapter.Shape) (i : Nat)
    (root : Digest32) : Reference :=
  if i = 0 then SpongefishCurrentPhysicalRootCapture.reference shape root
  else ⟨root,SpongefishCurrentRootPolicy.levelShape p i⟩

theorem openingReference_eq (shape : SpongefishSessionAdapter.Shape) (o : QueryOpening p) :
    SpongefishCurrentGoodEvent.openingReference shape o = rootReference p shape o.level.val o.root := rfl

/-- First-mention captures of the walk roots, recorded by level in `frozens`. -/
def Captured (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
    (shape : SpongefishSessionAdapter.Shape) (headerFrames boundary B : Nat) (iv : Digest32)
    (view : View (FullResult p)) (col : Collected p) (frozens : Nat → Frozen) : Prop :=
  ∀ i root, i < (ParameterBounds.config p).folds.size → col.roots[i]? = some root →
    SpongefishCurrentRootPolicy.publicCapture (B := B) p grinding shape headerFrames boundary iv
      (rootReference p shape i root) view = some (frozens i)

/-- The base oracle: the frozen Root0 image. -/
def rootOracle (frozen0 : Frozen) : BaseOracle := frozen0.raw

/-- The ghost next oracle of level `i`: the decoded frozen capture of the level root. -/
def nextOracle (frozens : Nat → Frozen) (i : Nat) : Oracle :=
  (PCSBCSFrozenOracleRows.frozenOracle i (frozens i)).getD #[]

theorem ordinaryLog_origin {B : Nat} (events : List (SpongefishCurrentPhysicalRootCapture.Event B))
    (n : Node) (a : Digest32) (member : (n,a) ∈ SpongefishCurrentPhysicalRootCapture.ordinaryLog events) :
    (⟨.inl n,a⟩ : SpongefishCurrentPhysicalRootCapture.Event B) ∈ events := by
  have general : ∀ (events : List (SpongefishCurrentPhysicalRootCapture.Event B))
      (prior : DuplexPublicSimulator.PublicLog),
      (n,a) ∈ events.foldl SpongefishCurrentPhysicalRootCapture.ordinaryStep prior →
      (n,a) ∈ prior ∨ (⟨.inl n,a⟩ : SpongefishCurrentPhysicalRootCapture.Event B) ∈ events := by
    intro events
    induction events with
    | nil => exact fun _ member => .inl member
    | cons event rest ih =>
      intro prior member
      rcases ih _ member with old | later
      · obtain ⟨key,answer⟩ := event
        cases key with
        | inl input =>
          simp only [SpongefishCurrentPhysicalRootCapture.ordinaryStep,List.mem_cons] at old
          rcases old with head | older
          · obtain ⟨rfl,rfl⟩ := Prod.mk.inj head
            exact .inr List.mem_cons_self
          · exact .inl older
        | inr key => exact .inl old
      · exact .inr (List.mem_cons_of_mem _ later)
  exact (general events [] member).resolve_left (by simp)

theorem mixedTrace_origin (B : Nat) (iv : Digest32) :
    ∀ (log : DuplexPublicSimulator.PublicLog) (obs : List Observation) (n : Node) (a : Digest32),
      (⟨.inl n,a⟩ : SpongefishCurrentPhysicalRootCapture.Event B) ∈
        PCSBCSNativePublicCapture.mixedTrace B iv log obs →
      ∃ purpose, (⟨.primitive purpose n,a⟩ : Observation) ∈ obs
  | _, [], _, _, member => by cases member
  | log, o :: rest, n, a, member => by
    simp only [PCSBCSNativePublicCapture.mixedTrace,List.mem_append] at member
    rcases member with here | later
    · obtain ⟨query,answer⟩ := o
      cases query with
      | primitive purpose input =>
        simp only [PCSBCSNativePublicCapture.observationDraw] at here
        split at here
        · cases here
        · split at here
          · simp at here
          · simp only [List.mem_singleton,Sigma.mk.injEq,Sum.inl.injEq,heq_eq_eq] at here
            obtain ⟨rfl,rfl⟩ := here
            exact ⟨purpose,List.mem_cons_self⟩
      | construction c valid =>
        simp only [PCSBCSNativePublicCapture.observationDraw] at here
        split at here <;> simp at here
    · obtain ⟨purpose,found⟩ := mixedTrace_origin B iv _ rest n a later
      exact ⟨purpose,List.mem_cons_of_mem _ found⟩

/-- A public first-mention capture is the literal freeze of its ordinary prefix log, and every record of that log is a primitive observation of the view. -/
theorem publicCapture_spec {B : Nat} {R : Type} (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
    (shape : SpongefishSessionAdapter.Shape) (headerFrames boundary : Nat) (iv : Digest32) (ref : Reference)
    (view : View R) (frozen : Frozen)
    (found : SpongefishCurrentRootPolicy.publicCapture (B := B) p grinding shape headerFrames boundary iv ref view =
      some frozen) :
    frozen = freeze frozen.queryPrefix ref.root ref.shape ∧
    ∀ n a, (n,a) ∈ frozen.queryPrefix → ∃ purpose, (⟨.primitive purpose n,a⟩ : Observation) ∈ view.observations := by
  unfold SpongefishCurrentRootPolicy.publicCapture SpongefishCurrentRootPolicy.capture
    SpongefishCurrentRootPolicy.firstPrefix at found
  obtain ⟨before,first,same⟩ := Option.map_eq_some_iff.mp found
  subst same
  refine ⟨rfl,?_⟩
  intro n a member
  exact mixedTrace_origin B iv [] view.observations n a
    (PCSBCSNativePublicCapture.firstPrefix_subset _ _ _ before first _ (ordinaryLog_origin before n a member))

/-- Geometry of the root references: Root0 has the level-0 `openQuery` geometry with the shape's lanes, level roots the full later geometry. -/
theorem rootReference_geometry (shape : SpongefishSessionAdapter.Shape)
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p shape) (i : Nat) (root : Digest32) :
    (rootReference p shape i root).root = root ∧
    (rootReference p shape i root).shape =
      ⟨(ParameterBounds.length (ParameterBounds.config p) i).log2,WHIRPhysicalVerifier.leafWords p i,
        if i = 0 then shape.lanes else WHIRPhysicalVerifier.leafWords p i⟩ := by
  unfold rootReference
  by_cases zero : i = 0
  · subst zero
    simp only [↓reduceIte]
    obtain ⟨height,leaf,occupied⟩ := SpongefishCurrentRootPolicy.root0_geometry p shape supported
    refine ⟨rfl,?_⟩
    change SpongefishCurrentPhysicalRootCapture.physicalShape shape = _
    rw [← height,Nat.log2_two_pow,← leaf,← occupied]
  · simp [zero,SpongefishCurrentRootPolicy.levelShape]

theorem lanes_fit (shape : SpongefishSessionAdapter.Shape)
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p shape) :
    shape.lanes ≤ 2^(ParameterBounds.config p).folds[0]! := by
  have fits := (SpongefishCurrentPhysicalRootCapture.occupied_guard shape supported.valid).2.1
  obtain ⟨_,leaf,occupied⟩ := SpongefishCurrentPhysicalRootCapture.physical_shape shape
  rw [leaf,occupied,supported.batch] at fits
  exact fits

/-- Row binding at one captured root: with an authentic frozen log and a quiet opening, the rows opened by the walk's hash program are the decoded frozen oracle at the query indices. -/
theorem captured_rows (C : PrimitiveOracle) (i : Fin (ParameterBounds.config p).folds.size) (lanes : Nat)
    (fits : lanes ≤ 2^(ParameterBounds.config p).folds[0]!) (ref : Reference) (frozen : Frozen)
    (literal : frozen = freeze frozen.queryPrefix ref.root ref.shape)
    (geometry : ref.shape = ⟨(ParameterBounds.length (ParameterBounds.config p) i.val).log2,
      WHIRPhysicalVerifier.leafWords p i.val,
      if i.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p i.val⟩)
    (auth : PublicMerkleLog.AuthenticLog C frozen.queryPrefix)
    (root : Digest32) (rootEq : ref.root = root) (proof : MerkleTransport.PrunedMerklePaths)
    (x : CausalProbability.Sample (.query i)) (opened : WHIRPhysicalVerifier.Opened)
    (evaluated : HashProgram.eval (PublicMerkleLog.hash C) (openProgram lanes i root proof x) = some opened)
    (quiet : ¬ PublicMerkleBinding.OpenPrimitiveBad C frozen.queryPrefix root opened.paths) :
    ∃ oracle, PCSBCSFrozenOracleRows.frozenOracle i.val frozen = some oracle ∧
      opened.rows = WHIRPhysicalVerifier.atQueries oracle (WHIRPhysicalVerifier.queryIndices p i x) := by
  have accepted : (runReal C DuplexRefinement.zeroDigest
      (WHIRPhysicalVerifier.openQuery p i lanes proof root x)).view.result = some opened := by
    rw [← openProgram_lower,HashProgram.lower_real]
    exact evaluated
  rcases PCSBCSCapturedNativePhaseQuery.openQuery_selectPhase C DuplexRefinement.zeroDigest frozen.queryPrefix
      auth p i lanes fits proof root x opened accepted with ⟨selected,selection,rows,_,_⟩ | bad
  · rw [← rootEq,← geometry,← literal] at selection
    obtain ⟨_,oracle,decoded,size,each⟩ := PCSBCSSourceFrozenAccessor.selectPhase_order _ _ _ _ selection
    refine ⟨oracle,decoded,?_⟩
    rw [← rows]
    apply Array.ext
    · simp [WHIRPhysicalVerifier.atQueries,size]
    · intro j hj hk
      have entry := each ⟨j,by simpa [size] using hj⟩
      simp only [getElem!_pos selected.rows j hj] at entry
      simp [WHIRPhysicalVerifier.atQueries,entry]
  · exact (quiet bad).elim

theorem extensionRow_size (w : Array K) (r : Array E) (h : PCSBCSFrozenOracleRows.extensionRow w = some r) :
    r.size = w.size / 3 := by
  unfold PCSBCSFrozenOracleRows.extensionRow at h
  split at h
  · cases h
    simp
  · cases h

/-- A frozen level capture decodes to a rectangular later oracle. -/
theorem next_valid (log : DuplexPublicSimulator.PublicLog) (root : Digest32) (j : Nat) (nonzero : j ≠ 0) :
    oracleValid ((PCSBCSFrozenOracleRows.frozenOracle j
        (freeze log root (SpongefishCurrentRootPolicy.levelShape p j))).getD #[])
      (ParameterBounds.length (ParameterBounds.config p) j) (2^(ParameterBounds.config p).folds[j]!) = true := by
  have words : (SpongefishCurrentRootPolicy.levelShape p j).occupied = 3 * 2^(ParameterBounds.config p).folds[j]! := by
    simp [SpongefishCurrentRootPolicy.levelShape,WHIRPhysicalVerifier.leafWords,nonzero]
  have fits : (SpongefishCurrentRootPolicy.levelShape p j).occupied ≤
      (SpongefishCurrentRootPolicy.levelShape p j).leafWords := le_refl _
  obtain ⟨oracle,decoded,size⟩ := PCSBCSSourceFrozenAccessorStructural.frozenOracle_freeze log root _ fits j
    (Or.inr (by rw [words]; omega))
  obtain ⟨cells,rawSize,rows⟩ := PCSBCSSourceFrozenAccessorStructural.freeze_shape_exact log root _ fits
  obtain ⟨_,codec⟩ := PCSBCSCapturedNativeReplyBridge.frozenOracle_row j _ oracle decoded
  rw [decoded,Option.getD_some]
  simp only [oracleValid,Bool.and_eq_true,beq_iff_eq,Array.all_eq_true]
  constructor
  · rw [size,cells,(SpongefishCurrentRootPolicy.levelShape_geometry p j).1]
  · intro k hk
    have rawK : k < (freeze log root (SpongefishCurrentRootPolicy.levelShape p j)).raw.size := by
      rw [rawSize,← size]
      exact hk
    have row := codec ⟨k,rawK⟩
    simp only [PCSBCSCapturedNativeReplyBridge.rowCodec,nonzero,↓reduceIte] at row
    have width := rows _ (Array.getElem_mem_toList rawK)
    have rowSize := extensionRow_size _ _ row
    simp only [Fin.getElem_fin] at rowSize
    rw [width,words,getElem!_pos oracle k hk] at rowSize
    rw [rowSize]
    simp

/-- The frozen Root0 image is a rectangular base oracle of the initial geometry. -/
theorem root_valid (shape : SpongefishSessionAdapter.Shape)
    (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p shape)
    (log : DuplexPublicSimulator.PublicLog) (root : Digest32) :
    oracleValid (liftRoot (freeze log root (SpongefishCurrentPhysicalRootCapture.physicalShape shape)).raw)
      (2^((ParameterBounds.config p).logN-(ParameterBounds.config p).folds[0]!+
        (ParameterBounds.config p).rates[0]!)) shape.lanes = true := by
  have fits := (SpongefishCurrentPhysicalRootCapture.occupied_guard shape supported.valid).2.1
  obtain ⟨cells,rawSize,rows⟩ := PCSBCSSourceFrozenAccessorStructural.freeze_shape_exact log root _ fits
  obtain ⟨height,_,occupied⟩ := SpongefishCurrentPhysicalRootCapture.physical_shape shape
  simp only [oracleValid,Bool.and_eq_true,beq_iff_eq,Array.all_eq_true,liftRoot]
  constructor
  · rw [Array.size_map,rawSize,cells,height,supported.dimension,supported.batch,supported.rate]
  · intro k hk
    rw [Array.size_map] at hk
    simp only [Array.getElem_map,Array.size_map]
    rw [rows _ (Array.getElem_mem_toList hk),occupied]

/-! ## Literal public trace of an indexed strategy -/

/-- The public snapshot only reads strictly prior visible replies, so the replayed replies of an indexed strategy give the same snapshot as the indexed reply array. -/
theorem snapshot_indexed (input : Public) (answers : Array Reply) (ring : RingPCSGame.Prefix)
    (t : Tape input.config) (q : CausalProbability.Coordinate input.config) :
    PCSRoundByRoundTranscriptState.snapshot ring t
        (PCSRoundByRoundTranscriptState.replies input (CausalStrategy.indexedStrategy answers) t) q =
      PCSRoundByRoundTranscriptState.snapshot ring t answers q := by
  unfold PCSRoundByRoundTranscriptState.snapshot PCSRoundByRoundTranscriptState.priorAnswers
  congr 2
  funext n
  have bound : n.val < (visibleBatches input.config t.1 (challenges input.config t)).length := by
    rw [← CausalProbability.visibleCoordinates_map,List.length_map]
    exact Nat.lt_of_lt_of_le n.isLt List.idxOf_le_length
  unfold PCSRoundByRoundTranscriptState.replies
  rw [List.getElem!_toArray,CausalStrategy.indexed_response answers input [] _ n.val bound]
  simp

/-- The current original reconstruction binds the record to the caller layout's shape and the original's lanes, anchor point and value to the record. -/
theorem candidate_binding {Q : Nat} (layout : WHIRCallerClaims.CallerLayout) (q : Coordinate)
    (r : SpongefishSessionAdapter.Record) (instanceBytes : List Byte) (observations : List Observation)
    (input : PCSBCSCallerBinding.CallerInput p)
    (original : SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout q r instanceBytes observations =
      some input) :
    r.shape = AnchoredSourceCaller.shape layout ∧ input.lanes = r.shape.lanes ∧
      input.anchorPoint = r.point.toArray ∧ input.anchorValue = r.value := by
  unfold SpongefishCurrentSourceCallerOriginal.candidate at original
  obtain ⟨result,_,finished⟩ := Option.bind_eq_some_iff.mp original
  exact SpongefishCurrentOpeningExperiment.finish_binding layout q r _ input finished

/-! ## Ideal rows, oracle shapes and the terminal state -/

section IdealRows
variable {Q : Nat} {Packet : Type} {Block : Packet → Type}
  (part : RawOracleCoupling.Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)
  (iv : Digest32) (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
  (before payloadCalls messages : List Call) (decode : Decoder)
  (grinding : Fin (ParameterBounds.config p).folds.size → Fin 64)
  (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
  (counted : Counts Q (fullProgram (p := p) iv tag instanceBytes layout before payloadCalls messages decode
    grinding prefixProgram))
  (table : (key : part.Key) → part.Answer (D := Digest32) key)
  (headerFrames boundary : Nat)

/-- Row binding of the ideal walk: on every partition table, if every walk root has a first-mention capture and every query opening is quiet against its capture, the reply at position `position (.query i)` carries the rows of the decoded frozen oracle of level `i` (the frozen Root0 image at level 0) at the native query indices of the tape. -/
theorem ideal_rows (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
    (result : (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram counted table).result = (some (.ok data),some col))
    (quiet : SpongefishCurrentGoodEvent.Quiet grinding (AnchoredSourceCaller.shape layout) headerFrames boundary
      Q iv (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table))
    (frozens : Nat → Frozen)
    (found : Captured grinding (AnchoredSourceCaller.shape layout) headerFrames boundary Q iv
      (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table) col frozens) :
    SpongefishCurrentOpeningExperiment.RowsAuthenticated col.tape col.replies (rootOracle (frozens 0))
      (nextOracle frozens) := by
  obtain ⟨root0,_,evaluated,_⟩ := ideal_walk part iv tag instanceBytes layout before payloadCalls messages
    decode grinding prefixProgram counted table data col result
  obtain ⟨_,_,each⟩ := walk_spec _ decode grinding _ root0 _ col evaluated
  intro i
  obtain ⟨o,m,member,level,rootAt,replyAt,opened⟩ := each i
  have capture := found i.val o.root i.isLt rootAt
  obtain ⟨literal,origin⟩ := publicCapture_spec grinding _ headerFrames boundary iv _ _ _ capture
  obtain ⟨rootEq,geometry⟩ := rootReference_geometry _ supported i.val o.root
  have auth : PublicMerkleLog.AuthenticLog (PCSBCSPublicPrimitiveOpening.publicSeed
      (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table)) (frozens i.val).queryPrefix := by
    intro n a recorded
    obtain ⟨purpose,observed⟩ := origin n a recorded
    exact source_seed part iv _ counted table purpose n a observed
  have clean := quiet col (by rw [result]) o member (frozens i.val) (by
    rw [openingReference_eq,level]
    exact capture)
  obtain ⟨oracle,decoded,rows⟩ := captured_rows _ i _ (lanes_fit _ supported) _ (frozens i.val) literal
    geometry auth o.root rootEq o.proof _ o.opened opened clean
  have reply : col.replies[CausalProbability.position (CausalProbability.Coordinate.query i)]! =
      .query o.opened.rows m := by
    simp only [getElem!_def,replyAt]
  rw [reply]
  change o.opened.rows = _
  rw [rows]
  congr 1
  unfold SpongefishCurrentOpeningExperiment.levelOracle
  by_cases zero : i.val = 0
  · simp only [zero,↓reduceIte]
    rw [zero] at decoded
    simp only [PCSBCSFrozenOracleRows.frozenOracle,↓reduceIte,Option.some.injEq] at decoded
    rw [← decoded]
    rfl
  · simp only [zero,↓reduceIte]
    unfold nextOracle
    rw [decoded]
    rfl

/-- The ghost next oracles decoded from the level captures have their public rectangular shapes. -/
theorem ideal_nextShapes (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
    (result : (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram counted table).result = (some (.ok data),some col))
    (frozens : Nat → Frozen)
    (found : Captured grinding (AnchoredSourceCaller.shape layout) headerFrames boundary Q iv
      (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table) col frozens) :
    SpongefishCurrentOpeningExperiment.NextShapes (ParameterBounds.config p) (nextOracle frozens) := by
  obtain ⟨root0,_,evaluated,_⟩ := ideal_walk part iv tag instanceBytes layout before payloadCalls messages
    decode grinding prefixProgram counted table data col result
  obtain ⟨_,_,each⟩ := walk_spec _ decode grinding _ root0 _ col evaluated
  intro j positive bound
  obtain ⟨o,_,_,_,rootAt,_,_⟩ := each ⟨j,bound⟩
  obtain ⟨literal,_⟩ := publicCapture_spec grinding _ headerFrames boundary iv _ _ _ (found j o.root bound rootAt)
  have nonzero : j ≠ 0 := by omega
  unfold nextOracle
  rw [literal]
  simp only [rootReference,nonzero,↓reduceIte]
  exact next_valid _ _ j nonzero

/-- The frozen Root0 image has the public initial shape. -/
theorem ideal_rootShape (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
    (result : (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram counted table).result = (some (.ok data),some col))
    (frozens : Nat → Frozen)
    (found : Captured grinding (AnchoredSourceCaller.shape layout) headerFrames boundary Q iv
      (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table) col frozens) :
    oracleValid (liftRoot (rootOracle (frozens 0)))
      (2^((ParameterBounds.config p).logN-(ParameterBounds.config p).folds[0]!+
        (ParameterBounds.config p).rates[0]!)) (AnchoredSourceCaller.shape layout).lanes = true := by
  obtain ⟨root0,_,evaluated,_⟩ := ideal_walk part iv tag instanceBytes layout before payloadCalls messages
    decode grinding prefixProgram counted table data col result
  obtain ⟨rootAt,_,_⟩ := walk_spec _ decode grinding _ root0 _ col evaluated
  obtain ⟨literal,_⟩ := publicCapture_spec grinding _ headerFrames boundary iv _ _ _ (found 0 root0 (ParameterBounds.production_config_valid p).2.1 rootAt)
  unfold rootOracle
  rw [literal]
  simp only [rootReference,↓reduceIte,SpongefishCurrentPhysicalRootCapture.reference]
  exact root_valid _ supported _ _

/-- Terminal state of the ideal good event: the walk's native equations on the reconstructed original, row binding against the first-mention captures and extraction failure on the frozen Root0 image make the literal final public state true, for the frozen Root0 image as base oracle, the tape and the native replies with restored ghost next oracles. -/
theorem ideal_terminal (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
    (result : (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram counted table).result = (some (.ok data),some col))
    (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (original : SpongefishCurrentSourceCallerOriginal.candidate (Q := Q) p layout
      (SpongefishCurrentGoodEvent.postBinding boundary data) r instanceBytes
      (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table).observations = some input)
    (verdict : SpongefishCurrentGoodEvent.Verdict r input col)
    (fails : SpongefishCurrentGoodEvent.ExtractionFails grinding (AnchoredSourceCaller.shape layout)
      headerFrames boundary Q iv input (idealView part iv tag instanceBytes layout before payloadCalls messages
        decode grinding prefixProgram counted table))
    (quiet : SpongefishCurrentGoodEvent.Quiet grinding (AnchoredSourceCaller.shape layout) headerFrames boundary
      Q iv (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table))
    (frozens : Nat → Frozen)
    (found : Captured grinding (AnchoredSourceCaller.shape layout) headerFrames boundary Q iv
      (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table) col frozens)
    (seed : RingPCSGame.Prefix × E) (seeded : col.seed = some seed) :
    PCSBCSRestorationHazard.literalState p input (rootOracle (frozens 0)) seed.1 col.tape
      (SpongefishCurrentOpeningExperiment.restoredReplies col (nextOracle frozens))
      (PCSRoundByRoundTranscriptState.lastCoordinate (ParameterBounds.config p)) = true := by
  obtain ⟨shapeEq,lanes,anchorPoint,anchorValue⟩ := candidate_binding layout _ r instanceBytes _ input original
  obtain ⟨seed',proof,seeded',parsed,equations⟩ := verdict
  rw [seeded] at seeded'
  cases seeded'
  obtain ⟨root0,_,evaluated,_⟩ := ideal_walk part iv tag instanceBytes layout before payloadCalls messages
    decode grinding prefixProgram counted table data col result
  obtain ⟨rootAt,seedTape,_⟩ := walk_spec _ decode grinding _ root0 _ col evaluated
  have rows := ideal_rows part iv tag instanceBytes layout before payloadCalls messages decode grinding
    prefixProgram counted table headerFrames boundary supported data col result quiet frozens found
  have nextShapes := ideal_nextShapes part iv tag instanceBytes layout before payloadCalls messages decode
    grinding prefixProgram counted table headerFrames boundary data col result frozens found
  have rootShape := ideal_rootShape part iv tag instanceBytes layout before payloadCalls messages decode
    grinding prefixProgram counted table headerFrames boundary supported data col result frozens found
  rw [← shapeEq] at rootShape
  have accepted := SpongefishCurrentOpeningExperiment.experiment_accepts r input col seed proof
    (seedTape seed seeded) parsed equations lanes anchorPoint anchorValue
    (by rw [shapeEq]; exact supported.dimension) (by rw [shapeEq]; exact supported.batch)
    (rootOracle (frozens 0)) (nextOracle frozens) rootShape nextShapes rows
  have failure : ¬ ∃ w, PCSRoundByRoundKnowledge.extract p input.lanes input.family input.points
      input.anchorPoint input.anchorValue (rootOracle (frozens 0)) = some w ∧
      PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) input.lanes (rootOracle (frozens 0))
        input.family input.points input.anchorPoint input.anchorValue w := by
    rintro ⟨w,extracted,explains⟩
    apply fails
    refine ⟨root0,frozens 0,w,?_,?_,extracted,explains⟩
    · unfold SpongefishCurrentGoodEvent.publicRoot0
      rw [result]
      exact rootAt
    · have capture := found 0 root0 (ParameterBounds.production_config_valid p).2.1 rootAt
      simp only [rootReference,↓reduceIte] at capture
      exact capture
  have final := PCSRoundByRoundTranscriptState.literal_accepted_extraction_failure_final p input.lanes
    input.family input.points input.anchorPoint input.anchorValue input.prepared (rootOracle (frozens 0))
    (fun _ => CausalStrategy.indexedStrategy
      (SpongefishCurrentOpeningExperiment.restoredReplies col (nextOracle frozens)))
    input.familyCap input.claimCap seed.1 col.tape accepted failure
  have same : PCSRoundByRoundTranscriptState.snapshot (c := ParameterBounds.config p) seed.1 col.tape
      (PCSRoundByRoundTranscriptState.replies (ExecutionShapes.Input p input.lanes (rootOracle (frozens 0))
        (OriginalClaimsChecker.input input.prepared (rootOracle (frozens 0)) seed.1).claims)
        (CausalStrategy.indexedStrategy
          (SpongefishCurrentOpeningExperiment.restoredReplies col (nextOracle frozens))) col.tape)
      (PCSRoundByRoundTranscriptState.lastCoordinate (ParameterBounds.config p)) =
    PCSRoundByRoundTranscriptState.snapshot seed.1 col.tape
      (SpongefishCurrentOpeningExperiment.restoredReplies col (nextOracle frozens))
      (PCSRoundByRoundTranscriptState.lastCoordinate (ParameterBounds.config p)) :=
    snapshot_indexed (ExecutionShapes.Input p input.lanes (rootOracle (frozens 0))
        (OriginalClaimsChecker.input input.prepared (rootOracle (frozens 0)) seed.1).claims)
      (SpongefishCurrentOpeningExperiment.restoredReplies col (nextOracle frozens)) seed.1 col.tape
      (PCSRoundByRoundTranscriptState.lastCoordinate (ParameterBounds.config p))
  unfold PCSBCSRestorationHazard.literalState
  rw [← same]
  exact final

/-- Every hashed input of every returned query opening has its real primitive plan, for the view's public seed, among the view's observations and in the view's public primitive log. -/
theorem ideal_opening_plans (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
    (result : (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram counted table).result = (some (.ok data),some col)) :
    ∀ o ∈ col.openings, ∀ path ∈ o.opened.paths,
      ∀ bytes ∈ path.opening.inputs (MerkleTransport.hashing (PublicMerkleLog.hash
        (PCSBCSPublicPrimitiveOpening.publicSeed (idealView part iv tag instanceBytes layout before payloadCalls
          messages decode grinding prefixProgram counted table)))),
      ∀ e ∈ PublicMerkleLog.plan (PCSBCSPublicPrimitiveOpening.publicSeed (idealView part iv tag instanceBytes
          layout before payloadCalls messages decode grinding prefixProgram counted table)) bytes,
        (⟨.primitive .verification e.1,e.2⟩ : Observation) ∈
          (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
            prefixProgram counted table).observations ∧
        (e.1,e.2) ∈ DuplexPublicSimulator.finalLog []
          (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
            prefixProgram counted table).observations := by
  obtain ⟨root0,_,evaluated,planned⟩ := ideal_walk part iv tag instanceBytes layout before payloadCalls messages
    decode grinding prefixProgram counted table data col result
  intro o member path present bytes input e queried
  have call := (walk_openings _ decode grinding _ root0 _ col evaluated o member).2 path present bytes input
  have observed := planned bytes call e queried
  exact ⟨observed,PCSBCSObservedPrimitiveExtension.primitive_in_finalLog [] _ .verification e.1 e.2 observed⟩

/-- The terminal state read off the public good event: the good event fixes the returned walk, the reconstructed original and the batching seed, and for every family of first-mention captures of the walk roots the literal final public state is true. -/
theorem good_terminal (supported : SpongefishCurrentAnchorAttackerPrefix.Supported p (AnchoredSourceCaller.shape layout))
    (k : Nat)
    (good : SpongefishCurrentGoodEvent.GoodFull Q iv instanceBytes layout grinding headerFrames boundary k
      (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table)) :
    ∃ (data : SpongefishCurrentMixedModeCompiler.Data) (col : Collected p)
      (input : PCSBCSCallerBinding.CallerInput p) (seed : RingPCSGame.Prefix × E),
      (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
        prefixProgram counted table).result = (some (.ok data),some col) ∧ col.seed = some seed ∧
      ∀ frozens : Nat → Frozen,
        Captured grinding (AnchoredSourceCaller.shape layout) headerFrames boundary Q iv
          (idealView part iv tag instanceBytes layout before payloadCalls messages decode grinding
            prefixProgram counted table) col frozens →
        PCSBCSRestorationHazard.literalState p input (rootOracle (frozens 0)) seed.1 col.tape
          (SpongefishCurrentOpeningExperiment.restoredReplies col (nextOracle frozens))
          (PCSRoundByRoundTranscriptState.lastCoordinate (ParameterBounds.config p)) = true := by
  obtain ⟨data,col,r,input,result,_,original,verdict,fails,_,quiet⟩ := good
  have seeds := verdict
  obtain ⟨seed,_,seeded,_⟩ := seeds
  exact ⟨data,col,input,seed,result,seeded,fun frozens found =>
    ideal_terminal part iv tag instanceBytes layout before payloadCalls messages decode grinding
      prefixProgram counted table headerFrames boundary supported data col result r input original verdict
      fails quiet frozens found seed seeded⟩

end IdealRows

#print axioms source_seed
#print axioms consistent_eval
#print axioms full_walk
#print axioms ideal_walk
#print axioms stepWalk_spec
#print axioms walkFrom_spec
#print axioms walk_spec
#print axioms publicCapture_spec
#print axioms rootReference_geometry
#print axioms captured_rows
#print axioms next_valid
#print axioms root_valid
#print axioms snapshot_indexed
#print axioms candidate_binding
#print axioms ideal_rows
#print axioms ideal_nextShapes
#print axioms ideal_rootShape
#print axioms ideal_terminal
#print axioms ideal_opening_plans
#print axioms good_terminal

end Whir.SpongefishCurrentIdealRows
