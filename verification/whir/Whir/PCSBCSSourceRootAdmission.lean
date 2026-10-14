import Whir.PCSBCSCapturedSourceTransport
import Whir.PCSBCSConstructionReplayTrace
import Whir.PublicCompressionCouplingCache
import Whir.WHIRRealSimulator
import Whir.PCSBCSNativePhysicalFreeze

/-! Actual historical pre-#607 source-root scanner admission. The scanner uses
its fixed all-query budget B and the source entry boundary. Earlier direct
queries, guessed chaining values, and repeats are retained. Quietness is the
same complete physical primitive alarm (including its CV late-link targets),
not an additional cryptographic event. A construction freeze may be taken
AFTER the current raw response's nonordinary full path; those calls do not
change the ordinary captured log. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Whir.PCSBCSSourceRootAdmission
open Concrete Protocol FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open TypedOracleCompiler PublicCompressionProgram PublicMerkleLog
open PCSBCSConstructionReplayTrace PCSBCSSourceRootReferences
open PublicCompressionCouplingRecognition

private theorem body_mono {small large : DuplexPublicSimulator.PublicLog}
    (sub : ∀ e ∈ small, e ∈ large) {cv : Digest32} {ns : List Node}
    (body : DuplexPublicSimulator.PublicBody small cv ns) :
    DuplexPublicSimulator.PublicBody large cv ns := by
  induction body with
  | seed member seed => exact .seed (sub _ member) seed
  | step member internal child ih => exact .step (sub _ member) internal ih

private theorem functional_of_auth (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) : DuplexPublicSimulator.Functional log := by
  intro n a b ha hb
  exact (auth n a ha).symm.trans (auth n b hb)

private theorem simulator_lookup_eq (log : PublicLog) (n : Node) :
    DuplexPublicSimulator.lookup log n = PublicMerkleLog.lookup log n := by
  induction log with
  | nil => rfl
  | cons record log ih =>
    rcases record with ⟨m,d⟩
    by_cases same : n = m
    · simp [DuplexPublicSimulator.lookup,PublicMerkleLog.lookup,List.find?,same]
    · have other : m ≠ n := Ne.symm same
      simp [DuplexPublicSimulator.lookup,PublicMerkleLog.lookup,List.find?,same,other] at ih ⊢
      exact ih

/-- Successful extraction of the admitted literal source name fixes every
seed CV and the entire instruction plan, not merely a proposed coordinate. -/
theorem sourceShape_of_extracted (iv : Digest32) (ns : List Node) (q : Coordinate)
    (complete : Complete ns) (valid : DuplexEncoding.Admissible q)
    (extracted : extract ns = some (modeKey iv q)) :
    PCSBCSSourceCoordinateDecoder.SourceShape iv ns q := by
  have fields : (⟨ns.map payload,ns.map (fun n => (n.tweak,n.last))⟩ : Extracted) =
      modeKey iv q := by
    exact Option.some.inj (by simpa only [extract,(complete?_correct ns).mpr complete,
      ite_eq_left] using extracted)
  have messages := congrArg Extracted.message fields
  have anchored : Anchored iv ns := by
    intro n member seed
    have present : payload n ∈ (modeKey iv q).message := by
      rw [← messages]
      exact List.mem_map.mpr ⟨n,member,rfl⟩
    unfold modeKey keyFromPlan at present
    obtain ⟨instruction,_,same⟩ := List.mem_map.mp present
    have value := congrArg Prod.fst same
    simp only [payload,ite_eq_left seed] at value
    split at value
    · exact (Option.some.inj value).symm
    · cases value
  have plan := extract_plan ns complete
  rw [extracted] at plan
  simp only [Option.map_some,PCSBCSSourceCoordinateDecoder.extractedPlan_modeKey,
    Option.some.injEq] at plan
  exact ⟨complete,anchored,valid,plan.symm⟩

/-- Recover at the first physical occurrence, not necessarily at the current
(repeated) terminal. Erasing a later fresh record uses the alarm's CV targets;
erasing a repeat uses its earlier literal record. Thus an arbitrary terminal
prequery is not excluded or hidden from an observer. -/
theorem first_recovery (C : PrimitiveOracle) (roots : PublicMerkleProbability.RootPolicy)
    (B : Nat) (log : PublicLog) (auth : AuthenticLog C log)
    (quiet : PublicMerkleProbability.traceAlarm roots [] log.reverse = false)
    (budget : log.length ≤ B) (input : Node) (rest : List Node)
    (terminal : isTerminal input)
    (body : DuplexPublicSimulator.PublicBody log input.cv rest)
    (present : (input,C input) ∈ log) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q)
    (extracted : extract (input::rest) = some (modeKey PCSBCSSourceCoordinateDecoder.seedIV q)) :
    ∃ newer older, log = newer ++ (input,C input)::older ∧
      PCSBCSSourceCoordinateDecoder.recover B PCSBCSSourceCoordinateDecoder.seedIV older input = some q := by
  induction log with
  | nil => cases present
  | cons record log ih =>
    rcases record with ⟨n,d⟩
    have answer := auth n d List.mem_cons_self
    subst d
    have oldAuth : AuthenticLog C log := fun n d h => auth n d (List.mem_cons_of_mem _ h)
    have oldBudget : log.length ≤ B := by simp only [List.length_cons] at budget; omega
    have parts := quiet
    rw [List.reverse_cons,PublicMerkleProbability.traceAlarm_append] at parts
    simp only [Bool.or_eq_false_iff,List.reverse_reverse,List.append_nil,
      PublicMerkleProbability.traceAlarm,Bool.or_false,decide_eq_false_iff_not] at parts
    have oldQuiet := parts.1
    have safe := parts.2
    cases hit : PublicMerkleLog.lookup log n with
    | some d =>
      have old := PublicMerkleLog.lookup_mem hit
      have same := oldAuth n d old
      rw [← same] at old
      have oldBody := PublicCompressionCouplingRecognition.PublicBody.erase_repeat old body
      have oldPresent : (input,C input) ∈ log := by
        rcases List.mem_cons.mp present with equal | member
        · cases equal; exact old
        · exact member
      obtain ⟨newer,older,equal,recovered⟩ := ih oldAuth oldQuiet oldBudget oldBody oldPresent
      exact ⟨(n,C n)::newer,older,by simp only [List.cons_append,equal],recovered⟩
    | none =>
      by_cases same : n = input
      · subst n
        have oldBody := PublicCompressionCouplingRecognition.PublicBody.erase_terminal terminal body
        have clean : ¬ DuplexPublicSimulator.OutputCollision log := by
          have h := PublicMerkleProbability.traceAlarm_clean C roots [] log.reverse
            (by intro n d h; cases h)
            (fun n d h => oldAuth n d (List.mem_reverse.mp h))
            (by rintro ⟨a,b,d,h,_⟩; cases h) oldQuiet
          simp only [List.reverse_reverse,List.append_nil] at h
          exact fun ⟨a,b,d,ha,hb,ne⟩ => h ⟨a,b,d,ha,hb,ne⟩
        have recognized := DuplexPublicSimulator.recognized_complete
          (functional_of_auth C log oldAuth) clean terminal oldBody
        obtain ⟨key,found,keyExtracted⟩ := DuplexPublicSimulator.privateKey_of_recognized
          (by simpa only [simulator_lookup_eq] using hit) recognized budget
        have keySame : expandKey key = modeKey PCSBCSSourceCoordinateDecoder.seedIV q :=
          Option.some.inj (keyExtracted.symm.trans extracted)
        exact ⟨[],log,rfl,PCSBCSSourceCoordinateDecoder.recover_of_modeKey found valid keySame⟩
      · have oldPresent : (input,C input) ∈ log := by
          rcases List.mem_cons.mp present with equal | member
          · exact False.elim (same (congrArg Prod.fst equal).symm)
          · exact member
        have avoid : ∀ m d, (m,d) ∈ log → C n ≠ m.cv := by
          intro m d member equal
          apply safe
          refine ⟨hit,?_⟩
          apply Finset.mem_union_right
          apply Finset.mem_union_right
          rw [equal]
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(m,d),member,rfl⟩)
        have oldBody := PublicCompressionCouplingRecognition.PublicBody.erase_record body avoid
          (avoid input (C input) oldPresent)
        obtain ⟨newer,older,equal,recovered⟩ := ih oldAuth oldQuiet oldBudget oldBody oldPresent
        exact ⟨(n,C n)::newer,older,by simp only [List.cons_append,equal],recovered⟩

private theorem targets_append (p : ParameterBounds.Profile) (B boundary : Nat)
    (registry : AnchoredHeaderRoots.Public) (newer older : PublicLog) :
    PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry older ⊆
      PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry (newer++older) := by
  induction newer with
  | nil => exact fun _ h => h
  | cons record newer ih =>
    exact fun _ h => PCSBCSSourcePrimitiveRootBudget.targets_grow p B boundary registry _ _ (ih h)

/-- Public native role parsing is sufficient: no root-membership or recovered
coordinate is assumed. This inner lemma consumes physical tree provenance;
its actual-source endpoints below produce that provenance from compilation. -/
theorem tree_target (p : ParameterBounds.Profile) (B boundary : Nat)
    (registry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log)
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry) [] log.reverse = false)
    (budget : log.length ≤ B) (input : Node) (rest : List Node)
    (terminal : isTerminal input) (body : DuplexPublicSimulator.PublicBody log input.cv rest)
    (present : (input,C input) ∈ log) (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    (extracted : extract (input::rest) = some (modeKey PCSBCSSourceCoordinateDecoder.seedIV q))
    (refs : List Reference)
    (parsed : PCSBCSSourcePrimitiveRootBudget.openingReferences p boundary q = some refs)
    (ref : Reference) (member : ref ∈ refs) :
    ref.root ∈ PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry log := by
  obtain ⟨newer,older,equal,recovered⟩ := first_recovery C _ B log auth quiet budget
    input rest terminal body present q valid extracted
  have reference : ref ∈ PCSBCSSourcePrimitiveRootBudget.references p B boundary registry older input := by
    simp only [PCSBCSSourcePrimitiveRootBudget.references,recovered,Option.map_some,
      Option.getD_some,parsed]
    exact List.mem_append_right _ member
  have announced : ref.root ∈ PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry
      ((input,C input)::older) := by
    simp only [PCSBCSSourcePrimitiveRootBudget.targets,List.mem_toFinset,List.mem_map,
      PCSBCSSourcePrimitiveRootBudget.scan_cons]
    refine ⟨⟨older,ref.root,ref.shape⟩,List.mem_append_right _ ?_,rfl⟩
    exact List.mem_map.mpr ⟨ref,reference,rfl⟩
  rw [equal]
  exact targets_append p B boundary registry newer _ announced

private def planTrace (C : PrimitiveOracle) (cv : Digest32)
    (instructions : List DuplexEncoding.Instruction) : PublicLog :=
  toLog (Sampling.execute C (planCalls cv instructions)).2

private theorem planCalls_append_trace (C : PrimitiveOracle) (cv : Digest32)
    (left right : List DuplexEncoding.Instruction) :
    planTrace C cv (left++right) =
      planTrace C cv left ++
      planTrace C (evalPlan (compressionOf C) cv left) right := by
  induction left generalizing cv with
  | nil => rfl
  | cons instruction left ih =>
    simpa only [planTrace,List.cons_append,planCalls,Sampling.execute,toLog,List.map_cons,
      evalPlan,List.foldl_cons,List.cons_append,compressionOf] using congrArg
      (fun log => (⟨cv,instruction.1,instruction.2,true⟩,
        C ⟨cv,instruction.1,instruction.2,true⟩)::log) (ih _)

private theorem tree_plan (C : PrimitiveOracle) (iv : Digest32) {cv : Digest32}
    {ns : List Node} (tree : Tree (compressionOf C) cv ns) (anchored : Anchored iv ns) :
    evalPlan (compressionOf C) iv (rawPlan ns) = cv ∧
    planTrace C iv (rawPlan ns) =
      (ns.map (fun n => (n,C n))).reverse := by
  induction tree with
  | seed n seed =>
    have initial := anchored n List.mem_cons_self seed
    have last : n.last = true := seed.2
    have canonical : (⟨iv,n.block,n.tweak,true⟩ : Node) = n := by
      cases n
      simp_all only
    constructor
    · simp only [rawPlan,List.reverse_cons,List.reverse_nil,List.nil_append,
        List.map_cons,List.map_nil,evalPlan,List.foldl_cons,List.foldl_nil,compressionOf]
      rw [canonical]
      rfl
    · simp only [rawPlan,List.reverse_singleton,List.map_cons,List.map_nil]
      simp only [planTrace,planCalls,Sampling.execute,toLog,List.map_cons,List.map_nil]
      rw [canonical]
  | step n ns internal child ih =>
    have oldAnchor : Anchored iv ns := fun m hm hs => anchored m (List.mem_cons_of_mem _ hm) hs
    have previous := ih oldAnchor
    have last : n.last = true := internal.2
    have plan : rawPlan (n::ns) = rawPlan ns ++ [(n.block,n.tweak)] := by
      simp only [rawPlan,List.reverse_cons,List.map_append,List.map_singleton]
    rw [plan]
    constructor
    · rw [evalPlan,List.foldl_append]
      change evalPlan (compressionOf C) (evalPlan (compressionOf C) iv (rawPlan ns))
        [(n.block,n.tweak)] = nodeValue (compressionOf C) n
      rw [previous.1]
      simp only [evalPlan,List.foldl_cons,List.foldl_nil,nodeValue,compressionOf,last]
    · rw [planCalls_append_trace,previous.1,previous.2]
      have canonical : (⟨n.cv,n.block,n.tweak,true⟩ : Node) = n := by
        cases n
        simp_all only
      simp only [planTrace,planCalls,Sampling.execute,toLog,List.map_cons,List.map_nil,List.reverse_cons]
      rw [canonical]

/-- The complete literal construction contributes its terminal and every body
record, including when all inputs have already been queried. -/
theorem construction_body (C : PrimitiveOracle) (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) (log : PublicLog)
    (present : ∀ e ∈ queryTrace C iv (.construction q valid), e ∈ log) :
    let t := traceHistory (compressionOf C) iv q.history
    DuplexPublicSimulator.PublicBody log t.state.cv t.nodes ∧
      (terminalNode t.state.cv q.terminal,C (terminalNode t.state.cv q.terminal)) ∈ log := by
  dsimp only
  have tree := (traceHistory_valid (compressionOf C) iv q.history valid.1).1
  have trace : queryTrace C iv (.construction q valid) =
      ((coordinateTree (compressionOf C) iv q).map (fun n => (n,C n))).reverse := by
    change planTrace C iv (DuplexEncoding.plan q) = _
    rw [← coordinateTree_plan (compressionOf C) iv q]
    unfold coordinateTree rawPlan
    rw [List.reverse_cons,List.map_append,List.map_singleton,planCalls_append_trace]
    have bodyPlan := tree_plan C iv tree (traceHistory_anchored (compressionOf C) iv q.history valid.1)
    unfold rawPlan at bodyPlan
    rw [bodyPlan.1,bodyPlan.2]
    have last : (terminalNode (traceHistory (compressionOf C) iv q.history).state.cv q.terminal).last = true :=
      (terminal_node _ _).2
    cases q.terminal <;>
      simp [planTrace,planCalls,Sampling.execute,toLog,terminalNode,List.reverse_cons]
  have nodes : ∀ n ∈ coordinateTree (compressionOf C) iv q, (n,C n) ∈ log := by
    intro n member
    apply present
    rw [trace]
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨n,member,rfl⟩)
  constructor
  · have convert : ∀ {cv : Digest32} {ns : List Node},
        Tree (compressionOf C) cv ns →
        (∀ n ∈ ns, (n,C n) ∈ log) → DuplexPublicSimulator.PublicBody log cv ns := by
      intro cv ns tree
      induction tree with
      | seed n seed => intro recorded; exact .seed (recorded n List.mem_cons_self) seed
      | step n ns internal child ih =>
        intro recorded
        exact .step (recorded n List.mem_cons_self) internal
          (ih (fun m hm => recorded m (List.mem_cons_of_mem _ hm)))
    exact convert tree (fun n hn => nodes n (List.mem_cons_of_mem _ hn))
  · exact nodes _ List.mem_cons_self

/-- The public boundary recovers the admitted packet's actual live entry for
every continuation block; B is the whole budget, not this packet's ancestry. -/
theorem packet_entry {p : ParameterBounds.Profile} {B boundary : Nat} {iv : Digest32}
    (packet : PCSBCSChallengeOracle.EnteredPacket p B iv boundary)
    (block : PCSBCSChallengeOracle.EnteredPacket.Block packet) :
    PCSBCSSourcePrimitiveRootBudget.entry (packet.2.2.coordinate block) boundary = packet.1.val := by
  have history := WHIRCallerPrefix.outputKeyFrom_history _
    (WHIRHistoryKey.stackWidth_positive p) packet.1.val
    (WHIRHistoryKey.scheduled_normal _ _ packet.2.2.nonempty packet.2.2.admitted) block.val
  unfold PCSBCSSourcePrimitiveRootBudget.entry PCSBCSChallengeOracle.SourcePacket.coordinate
  rw [history]
  have take : (packet.1.val.frames ++ WHIRHistoryKey.canonicalFrames
      (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) packet.2.messages).take boundary =
      packet.1.val.frames := by
    exact (congrArg (fun n => (packet.1.val.frames ++ WHIRHistoryKey.canonicalFrames
      (WHIRHistoryKey.stackWidth (ParameterBounds.config p)) packet.2.messages).take n)
      packet.1.property).symm.trans List.take_left
  change {packet.1.val with frames := (packet.1.val.frames ++
    WHIRHistoryKey.canonicalFrames (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
      packet.2.messages).take boundary} = packet.1.val
  rw [take]

theorem packet_openingReferences {p : ParameterBounds.Profile} {B boundary : Nat}
    (packet : PCSBCSChallengeOracle.EnteredPacket p B PCSBCSSourceCoordinateDecoder.seedIV boundary)
    (block : PCSBCSChallengeOracle.EnteredPacket.Block packet) :
    (PCSBCSSourcePrimitiveRootBudget.openingReferences p boundary
      (packet.2.2.coordinate block)).getD [] =
      PCSBCSCapturedSourceTransport.address (.inl packet) := by
  unfold PCSBCSSourcePrimitiveRootBudget.openingReferences
  rw [packet_entry]
  have pending := parsePendingKey_roundtrip p packet.1.val packet.2.messages
    packet.2.2.nonempty packet.2.2.admitted block.val
  have first := parsePendingKey_roundtrip p packet.1.val packet.2.messages
    packet.2.2.nonempty packet.2.2.admitted 0
  dsimp only [PCSBCSChallengeOracle.CanonicalPacket.messages] at pending first
  simp only [PCSBCSCapturedSourceTransport.address,
    PCSBCSSourcePrimitiveRootBudget.openingReferencesFromEntry,
    PCSBCSChallengeOracle.SourcePacket.coordinate,
    PCSBCSChallengeOracle.CanonicalPacket.messages,pending,first]

/-- An actual mixed raw draw and its public byte-only address determine a
literal admitted source coordinate. In the primitive branch, recognition and
public-body provenance are obtained from the compiler's actual privateKey;
in the construction branch they are obtained from its complete physical path. -/
theorem draw_admission (p : ParameterBounds.Profile) (B boundary : Nat)
    (registry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle)
    (earlier cache : PublicLog) (current : Observation)
    (event : PCSBCSNativePhysicalFreeze.RawEvent B)
    (cacheSub : ∀ e ∈ cache, e ∈ earlier)
    (auth : AuthenticLog C (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query))
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry) []
      (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query) = false)
    (budget : (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query).length ≤ B)
    (draw : PCSBCSNativePublicCapture.observationDraw B PCSBCSSourceCoordinateDecoder.seedIV cache current = [event])
    (ref : Reference)
    (mentioned : ref ∈ PCSBCSCapturedSourceTransport.address
      (PCSBCSNativePublicCapture.allocatedKey (p := p)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary) event.1)) :
    ∃ (packet : PCSBCSChallengeOracle.EnteredPacket p B PCSBCSSourceCoordinateDecoder.seedIV boundary)
      (block : PCSBCSChallengeOracle.EnteredPacket.Block packet),
      event.1 = .inr (packet.2.2.key block) ∧
      ref.root ∈ PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry
        (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query).reverse ∧
      ∃ input newer older,
        (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query).reverse =
          newer ++ (input,C input)::older ∧
        PCSBCSSourceCoordinateDecoder.recover B PCSBCSSourceCoordinateDecoder.seedIV older input =
          some (packet.2.2.coordinate block) := by
  classical
  let part := PCSBCSChallengeOracle.EnteredPacket.partition
    (p := p) (Q := B) (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary)
  unfold PCSBCSNativePublicCapture.allocatedKey at mentioned
  split at mentioned
  next source found =>
    have raw := part.encode_recognize event.1 source found
    change Sum.inr (source.1.2.2.key source.2) = event.1 at raw
    have addressed : ref ∈ PCSBCSCapturedSourceTransport.address (.inl source.1) := mentioned
    have role := packet_openingReferences source.1 source.2
    cases parsed : PCSBCSSourcePrimitiveRootBudget.openingReferences p boundary
        (source.1.2.2.coordinate source.2) with
    | none => simp only [parsed,Option.getD_none] at role; rw [← role] at addressed; cases addressed
    | some refs =>
      have member : ref ∈ refs := by
        rw [← role] at addressed
        simpa only [parsed,Option.getD_some] using addressed
      have prefixAuth : AuthenticLog C
          (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query).reverse :=
        fun n d h => auth n d (List.mem_reverse.mp h)
      have prefixQuiet : PublicMerkleProbability.traceAlarm
          (PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry) []
          ((earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query).reverse).reverse = false := by
        simpa only [List.reverse_reverse] using quiet
      have prefixBudget : (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query).reverse.length ≤ B := by
        simpa only [List.length_reverse] using budget
      rcases current with ⟨query,d⟩
      cases query with
      | primitive purpose input =>
        unfold PCSBCSNativePublicCapture.observationDraw at draw
        cases hit : DuplexPublicSimulator.lookup cache input with
        | some old => simp [hit] at draw
        | none =>
          cases key : DuplexPublicSimulator.privateKey B cache input with
          | none =>
            simp only [hit,key,List.singleton_inj] at draw
            have impossible := congrArg Sigma.fst draw
            rw [← raw] at impossible
            cases impossible
          | some actual =>
            simp only [hit,key,List.singleton_inj] at draw
            have keys : actual = source.1.2.2.key source.2 :=
              Sum.inr.inj ((congrArg Sigma.fst draw).trans raw.symm)
            obtain ⟨nodes,recognized,complete,extracted⟩ := DuplexPublicSimulator.privateKey_sound key
            obtain ⟨rest,rfl,body⟩ := DuplexPublicSimulator.recognized_publicBody recognized
            have terminal : isTerminal input := by
              obtain ⟨n,ns,equal,terminal,_⟩ := complete
              cases equal
              exact terminal
            have publicBody : DuplexPublicSimulator.PublicBody
                (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV (.primitive purpose input)).reverse
                input.cv rest := body_mono
              (fun e he => List.mem_reverse.mpr (List.mem_append_left _ (cacheSub e he))) body
            have recorded : (input,C input) ∈
                (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV (.primitive purpose input)).reverse := by
              exact List.mem_reverse.mpr (List.mem_append_right _ List.mem_cons_self)
            have sourceExtract : extract (input::rest) =
                some (modeKey PCSBCSSourceCoordinateDecoder.seedIV (source.1.2.2.coordinate source.2)) := by
              rw [keys] at extracted
              exact extracted.trans (congrArg some (expand_constructionKey B
                PCSBCSSourceCoordinateDecoder.seedIV (source.1.2.2.coordinate source.2)
                (source.1.2.2.pathBound source.2)))
            have shape := sourceShape_of_extracted PCSBCSSourceCoordinateDecoder.seedIV
              (input::rest) (source.1.2.2.coordinate source.2) complete (source.1.2.2.valid source.2) sourceExtract
            have target := tree_target p B boundary registry C _ prefixAuth prefixQuiet prefixBudget
              input rest terminal publicBody recorded _ shape.2.2.1
              sourceExtract refs parsed ref member
            obtain ⟨newer,older,equal,recovered⟩ := first_recovery C _ B _ prefixAuth prefixQuiet prefixBudget
              input rest terminal publicBody recorded _ shape.2.2.1 sourceExtract
            exact ⟨source.1,source.2,raw.symm,target,input,newer,older,equal,recovered⟩
      | construction coordinate valid =>
        change (if bound : pathCost coordinate ≤ B then
          [⟨.inr (constructionKey B PCSBCSSourceCoordinateDecoder.seedIV coordinate bound),d⟩]
          else []) = [event] at draw
        split at draw
        next bound =>
          have keys : constructionKey B PCSBCSSourceCoordinateDecoder.seedIV coordinate bound =
              source.1.2.2.key source.2 :=
            Sum.inr.inj ((congrArg Sigma.fst (List.singleton_inj.mp draw)).trans raw.symm)
          have same : coordinate = source.1.2.2.coordinate source.2 :=
            constructionKey_injective B PCSBCSSourceCoordinateDecoder.seedIV valid
              (source.1.2.2.valid source.2) bound (source.1.2.2.pathBound source.2) keys
          cases same
          obtain ⟨body,recorded⟩ := construction_body C PCSBCSSourceCoordinateDecoder.seedIV
            (source.1.2.2.coordinate source.2) (source.1.2.2.valid source.2)
            (earlier ++ queryTrace C PCSBCSSourceCoordinateDecoder.seedIV
              (.construction (source.1.2.2.coordinate source.2) valid)).reverse
            (fun e he => List.mem_reverse.mpr (List.mem_append_right _ he))
          have cv : (terminalNode
              (traceHistory (compressionOf C) PCSBCSSourceCoordinateDecoder.seedIV
                (source.1.2.2.coordinate source.2).history).state.cv
              (source.1.2.2.coordinate source.2).terminal).cv =
              (traceHistory (compressionOf C) PCSBCSSourceCoordinateDecoder.seedIV
                (source.1.2.2.coordinate source.2).history).state.cv := by
            cases (source.1.2.2.coordinate source.2).terminal <;> rfl
          rw [← cv] at body
          have terminal := terminal_node
            (traceHistory (compressionOf C) PCSBCSSourceCoordinateDecoder.seedIV
              (source.1.2.2.coordinate source.2).history).state.cv
            (source.1.2.2.coordinate source.2).terminal
          have extracted := coordinateTree_key (compressionOf C) PCSBCSSourceCoordinateDecoder.seedIV
            (source.1.2.2.coordinate source.2) (source.1.2.2.valid source.2)
          have shape := PCSBCSSourceCoordinateDecoder.coordinateTree_sourceShape
            (compressionOf C) PCSBCSSourceCoordinateDecoder.seedIV
            (source.1.2.2.coordinate source.2) (source.1.2.2.valid source.2)
          have target := tree_target p B boundary registry C _ prefixAuth prefixQuiet prefixBudget
            _ _ terminal body recorded _ shape.2.2.1 extracted refs parsed ref member
          obtain ⟨newer,older,equal,recovered⟩ := first_recovery C _ B _ prefixAuth prefixQuiet prefixBudget
            _ _ terminal body recorded _ shape.2.2.1 extracted
          exact ⟨source.1,source.2,raw.symm,target,_,newer,older,equal,recovered⟩
        next => simp at draw
  next => simp only [PCSBCSCapturedSourceTransport.address,List.not_mem_nil] at mentioned

/-- Actual complete first-mention endpoint. All low-level provenance and freeze
conditions come from the whole fixed compiler and actual table; only its
Counts/source admission, fixed PARAM_IV, and the SAME global alarm are used.
No recovered key, recognized tree, root target, or observer exclusion is a
precondition. -/
theorem actual_firstMention_admitted {R : Type} (p : ParameterBounds.Profile)
    (B boundary : Nat) (registry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle)
    (program : Program R) (A : Nat) (limit : A ≤ B) (counted : Counts A program)
    (ref : Reference)
    (events : List (Sigma (PCSBCSSourceRootCapture.Answer
      (p := p) (Q := B) (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary))))
    (mentioned : PCSBCSFirstRootDisclosure.firstMention
      (PCSBCSCapturedSourceTransport.address (p := p) (Q := B)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary)) ref
      (PCSBCSNativePhysicalFreeze.allocationProgram (p := p) (boundary := boundary) program A limit counted)
      (PCSBCSNativePhysicalFreeze.actualTable (p := p) (B := B)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary) C) = some events)
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry) []
      (primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV program A counted) = false) :
    ∃ frozen : PCSBCSNativePhysicalFreeze.PhysicalFreeze
        (primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV program A counted)
        (PCSBCSNativePhysicalFreeze.actualSourceLog (p := p)
          (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary) C program A limit counted ref),
      ref.root ∈ PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry frozen.before.reverse ∧
      ∃ (packet : PCSBCSChallengeOracle.EnteredPacket p B PCSBCSSourceCoordinateDecoder.seedIV boundary)
        (block : PCSBCSChallengeOracle.EnteredPacket.Block packet) (input : Node) (newer older : PublicLog),
        frozen.before.reverse = newer ++ (input,C input)::older ∧
        PCSBCSSourceCoordinateDecoder.recover B PCSBCSSourceCoordinateDecoder.seedIV older input =
          some (packet.2.2.coordinate block) := by
  obtain ⟨earlier,current,later,cache,event,next,observations,reached,draw,addressed,cacheSub,
      cacheAuth,split,sub,saturated⟩ :=
    PCSBCSNativePhysicalFreeze.source_firstMention_freeze (p := p) (boundary := boundary)
      C program A limit counted PCSBCSCapturedSourceTransport.address (by intro other; rfl)
      ref events mentioned
  have auth : AuthenticLog C (PCSBCSNativePhysicalFreeze.physicalTrace C
      PCSBCSSourceCoordinateDecoder.seedIV earlier ++
      queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query) := by
    intro n d member
    apply primitiveLog_authentic C PCSBCSSourceCoordinateDecoder.seedIV program A counted n d
    rw [split]
    exact List.mem_append_left _ member
  have prefixQuiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry) []
      (PCSBCSNativePhysicalFreeze.physicalTrace C PCSBCSSourceCoordinateDecoder.seedIV earlier ++
        queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query) = false := by
    rw [split,PublicMerkleProbability.traceAlarm_append] at quiet
    exact (Bool.or_eq_false_iff.mp quiet).1
  have prefixBudget : (PCSBCSNativePhysicalFreeze.physicalTrace C
      PCSBCSSourceCoordinateDecoder.seedIV earlier ++
      queryTrace C PCSBCSSourceCoordinateDecoder.seedIV current.query).length ≤ B := by
    have bound := primitiveLog_length C PCSBCSSourceCoordinateDecoder.seedIV program A counted
    rw [split,List.length_append] at bound
    omega
  obtain ⟨packet,block,_,target,input,newer,older,equal,recovered⟩ :=
    draw_admission p B boundary registry C _ cache current event cacheSub auth prefixQuiet prefixBudget
      draw ref addressed
  exact ⟨⟨_,_,split,sub,saturated⟩,target,packet,block,input,newer,older,equal,recovered⟩

section CountedWhole
variable (cap : Nat)
    (nativeRegistry : {r : WHIRPhysicalDriver.ProductionRegistry //
      r.context.iv = PCSBCSSourceCoordinateDecoder.seedIV}) (Q : Nat)
    (attacker : WHIRSourceChronology.Source cap
      (AnchoredPhysicalAfter.Input nativeRegistry.val.context Q))
    (a b : Nat) (attackerCounted : WHIRSourceChronology.Counts a attacker)
    (nativeBudget : WHIRSourceBackfill.AllResults
      (fun input => WHIRPhysicalVerifier.sourceBudget nativeRegistry.val.context Q input.packet ≤ b)
      (WHIRSourceChronology.erase attacker))
local notation "whole" => PCSBCSNativePhysicalFreeze.wholeProgram cap nativeRegistry.val Q attacker
local notation "counted" => PCSBCSNativePhysicalFreeze.whole_counted
  cap nativeRegistry.val Q attacker a b attackerCounted nativeBudget

/-- Arbitrary attacker Source operations precede the native program. The
attacker Counts and reachable native sourceBudget check derive the WHOLE
Counts certificate; Q remains the native packet bound, B the scanner cap. -/
theorem counted_whole_firstMention_admitted (p : ParameterBounds.Profile) (B boundary : Nat)
    (registry : AnchoredHeaderRoots.Public) (C : PrimitiveOracle) (limit : a+b ≤ B)
    (ref : Reference)
    (events : List (Sigma (PCSBCSSourceRootCapture.Answer
      (p := p) (Q := B) (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary))))
    (mentioned : PCSBCSFirstRootDisclosure.firstMention
      (PCSBCSCapturedSourceTransport.address (p := p) (Q := B)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary)) ref
      (PCSBCSNativePhysicalFreeze.allocationProgram (p := p) (boundary := boundary)
        whole (a+b) limit counted)
      (PCSBCSNativePhysicalFreeze.actualTable (p := p) (B := B)
        (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary) C) = some events)
    (quiet : PublicMerkleProbability.traceAlarm
      (PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry) []
      (primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV whole (a+b) counted) = false) :
    ∃ frozen : PCSBCSNativePhysicalFreeze.PhysicalFreeze
        (primitiveLog C PCSBCSSourceCoordinateDecoder.seedIV whole (a+b) counted)
        (PCSBCSNativePhysicalFreeze.actualSourceLog (p := p)
          (iv := PCSBCSSourceCoordinateDecoder.seedIV) (boundary := boundary)
          C whole (a+b) limit counted ref),
      ref.root ∈ PCSBCSSourcePrimitiveRootBudget.targets p B boundary registry frozen.before.reverse ∧
      ∃ (packet : PCSBCSChallengeOracle.EnteredPacket p B PCSBCSSourceCoordinateDecoder.seedIV boundary)
        (block : PCSBCSChallengeOracle.EnteredPacket.Block packet) (input : Node) (newer older : PublicLog),
        frozen.before.reverse = newer ++ (input,C input)::older ∧
        PCSBCSSourceCoordinateDecoder.recover B PCSBCSSourceCoordinateDecoder.seedIV older input =
          some (packet.2.2.coordinate block) :=
  actual_firstMention_admitted p B boundary registry C whole (a+b) limit counted ref events mentioned quiet
end CountedWhole

#print axioms sourceShape_of_extracted
#print axioms first_recovery
#print axioms construction_body
#print axioms packet_entry
#print axioms packet_openingReferences
#print axioms draw_admission
#print axioms actual_firstMention_admitted
#print axioms counted_whole_firstMention_admitted

end Whir.PCSBCSSourceRootAdmission
