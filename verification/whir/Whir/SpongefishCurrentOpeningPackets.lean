import Whir.SpongefishCurrentBCSKnowledge

/-! Current #607 opening draws as exposed round packets in the IDEAL world, on every table of the current round packet partition.

The counted current source replays a fixed call list `pre ++ openingCalls grinding` through the semantic replay (`SpongefishCurrentMixedModeCompiler.replayProgram`), possibly followed by an arbitrary continuation. The replay contains only construction queries; on an ideal table every one of them is answered by the raw table at its literal construction key. The opening schedule never has two verifier draws without a nonempty prover payload between them (for every grinding), so the `j`-th opening draw closes a history with exactly `boundary + j + 1` frames when the opening starts with `boundary` closed frames and a pending prover run. The first block of every draw is cached or observed by the replay, hence recorded in the atomic trace with its whole packet, and the literal drawn bytes decode to the grouped packet value. This is a deterministic statement on every table; it contains no probability or acceptance assumption. -/
namespace Whir.SpongefishCurrentOpeningPackets
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame RawOracleCoupling
open TypedOracleCompiler SpongefishPCSRoundFrames SpongefishCurrentModeQueries
open SpongefishCurrentMixedModeCompiler
set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## Construction-only programs answered by a fixed coordinate function -/

/-- Answer every construction query by `ans`; primitive queries get zero. -/
def answerOf (ans : Coordinate → Digest32) : Query → Digest32
  | .construction q _ => ans q
  | .primitive _ _ => zeroDigest

def runWith (ans : Coordinate → Digest32) {R : Type} : Program R → View R
  | .done r => ⟨[],r⟩
  | .ask q next =>
    let rest := runWith ans (next (answerOf ans q))
    ⟨⟨q,answerOf ans q⟩ :: rest.observations,rest.result⟩

def ConstructionOnly {R : Type} : Program R → Prop
  | .done _ => True
  | .ask (.construction _ _) next => ∀ d, ConstructionOnly (next d)
  | .ask (.primitive _ _) _ => False

/-- The ideal answer of a construction coordinate within the raw-key budget. -/
def idealAnswer (Q : Nat) (iv : Digest32) (ro : RawKey Q → Digest32) (q : Coordinate) : Digest32 :=
  if h : pathCost q ≤ Q then ro (constructionKey Q iv q h) else zeroDigest

theorem runWith_bind (ans : Coordinate → Digest32) {R S : Type} (p : Program R)
    (k : R → Program S) :
    runWith ans (WHIRModeFinal.bind p k) =
      ⟨(runWith ans p).observations ++ (runWith ans (k (runWith ans p).result)).observations,
        (runWith ans (k (runWith ans p).result)).result⟩ := by
  induction p with
  | done r => rfl
  | ask q next ih =>
    simp only [WHIRModeFinal.bind,runWith,ih,List.cons_append]

theorem constructionOnly_bind {R S : Type} (p : Program R) (k : R → Program S)
    (first : ConstructionOnly p) (rest : ∀ r, ConstructionOnly (k r)) :
    ConstructionOnly (WHIRModeFinal.bind p k) := by
  induction p with
  | done r => exact rest r
  | ask q next ih =>
    cases q with
    | primitive => exact first.elim
    | construction c valid => exact fun d => ih d (first d)

theorem ideal_runWith {Q : Nat} {Seed State R : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (p : Program R) (only : ConstructionOnly p) :
    ∀ (state : State) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p),
      (runIdeal sim ro iv state p remaining cap counted).view = runWith (idealAnswer Q iv ro) p := by
  induction p with
  | done r => intro _ _ _ _; rfl
  | ask q next ih =>
    cases q with
    | primitive => exact only.elim
    | construction c valid =>
      intro state remaining cap counted
      have bound : pathCost c ≤ Q := counted.1.trans cap
      have answer : ro (constructionKey Q iv c bound) = idealAnswer Q iv ro c := by
        simp only [idealAnswer,bound,↓reduceDIte]
      have rest := ih (ro (constructionKey Q iv c bound)) (only _) state (remaining-pathCost c)
        (by omega) (counted.2 _)
      simp only [runIdeal,prepend,runWith,answerOf]
      rw [rest,answer]

theorem ideal_cost {Q : Nat} {Seed State R : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (p : Program R) :
    ∀ (state : State) (remaining : Nat) (cap : remaining ≤ Q) (counted : Counts remaining p),
      ∀ o ∈ (runIdeal sim ro iv state p remaining cap counted).view.observations,
        o.query.cost ≤ remaining := by
  induction p with
  | done r => intro _ _ _ _ o member; cases member
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      intro state remaining cap counted o member
      simp only [runIdeal,prepend,List.mem_cons] at member
      rcases member with rfl | later
      · exact counted.1
      · exact (ih _ _ _ _ _ o later).trans (Nat.sub_le _ _)
    | construction c valid =>
      intro state remaining cap counted o member
      simp only [runIdeal,prepend,List.mem_cons] at member
      rcases member with rfl | later
      · exact counted.1
      · exact (ih _ _ _ _ _ o later).trans (Nat.sub_le _ _)

/-- Ideal runs of an appended program split at the first program's result. -/
theorem ideal_bind {Q : Nat} {Seed State R S : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (p : Program R) (k : R → Program S) :
    ∀ (state : State) (remaining : Nat) (cap : remaining ≤ Q)
      (counted : Counts remaining (WHIRModeFinal.bind p k)),
    ∃ (state' : State) (rest : Nat) (cap' : rest ≤ Q)
      (counted' : Counts rest (k (runIdeal sim ro iv state p remaining cap
        (WHIRModeFinal.bind_prefix_counted p k remaining counted)).view.result)),
      (runIdeal sim ro iv state (WHIRModeFinal.bind p k) remaining cap counted).view =
        ⟨(runIdeal sim ro iv state p remaining cap
            (WHIRModeFinal.bind_prefix_counted p k remaining counted)).view.observations ++
          (runIdeal sim ro iv state' (k (runIdeal sim ro iv state p remaining cap
            (WHIRModeFinal.bind_prefix_counted p k remaining counted)).view.result) rest cap'
              counted').view.observations,
         (runIdeal sim ro iv state' (k (runIdeal sim ro iv state p remaining cap
            (WHIRModeFinal.bind_prefix_counted p k remaining counted)).view.result) rest cap'
              counted').view.result⟩ := by
  induction p with
  | done r => intro state remaining cap counted; exact ⟨state,remaining,cap,counted,rfl⟩
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      intro state remaining cap counted
      obtain ⟨state',rest,cap',counted',same⟩ := ih (runRO ro (sim.answer state input)).1.2
        (runRO ro (sim.answer state input)).1.1 (remaining-1) (by omega) (counted.2 _)
      refine ⟨state',rest,cap',counted',?_⟩
      simp only [WHIRModeFinal.bind,runIdeal,prepend]
      rw [same]
      rfl
    | construction c valid =>
      intro state remaining cap counted
      obtain ⟨state',rest,cap',counted',same⟩ := ih (ro (constructionKey Q iv c (counted.1.trans cap)))
        state (remaining-pathCost c) (by omega) (counted.2 _)
      refine ⟨state',rest,cap',counted',?_⟩
      simp only [WHIRModeFinal.bind,runIdeal,prepend]
      rw [same]
      rfl

/-! ## The semantic replay under a fixed coordinate answer -/

section Replay
variable (ans : Coordinate → Digest32)

/-- Every cached reply is the fixed answer of its coordinate. -/
def CacheOK (cache : Cache) : Prop := ∀ q d, cache q = some d → d = ans q

/-- A construction coordinate observed with its answer. -/
def Observed (obs : List Observation) (q : Coordinate) : Prop :=
  ∃ valid, (⟨.construction q valid,ans q⟩ : Observation) ∈ obs

/-- Every coordinate cached after a phase was cached before or observed in it. -/
def Known (before : Cache) (obs : List Observation) (after : Cache) : Prop :=
  ∀ q, after q ≠ none → before q ≠ none ∨ Observed ans obs q

theorem request_only (cache : Cache) (q : Coordinate) (valid : DuplexEncoding.Admissible q) :
    ConstructionOnly (SpongefishCurrentMixedModeCompiler.request cache q valid) := by
  unfold SpongefishCurrentMixedModeCompiler.request
  cases cache q with
  | none => exact fun _ => trivial
  | some => trivial

theorem collect_only (m : Pending) (positions : List Nat)
    (valid : ∀ p ∈ positions, DuplexEncoding.Admissible (coordinate m (p/32))) (cache : Cache) :
    ConstructionOnly (collect m positions valid cache) := by
  induction positions generalizing cache with
  | nil => trivial
  | cons p ps ih =>
    exact constructionOnly_bind _ _ (request_only _ _ _)
      (fun r => constructionOnly_bind _ _ (ih _ _) (fun _ => trivial))

theorem replay_only (cur : SemanticCursor) (calls : List Call) :
    ConstructionOnly (replayProgram cur calls) := by
  induction calls generalizing cur with
  | nil => trivial
  | cons call calls ih =>
    cases call with
    | read kind =>
      simp only [replayProgram]
      cases kind.codec.parse cur.data.narg with
      | none => trivial
      | some pair => exact ih _
    | hint =>
      simp only [replayProgram]
      cases cur.data.hints with
      | nil => trivial
      | cons bytes rest => exact ih _
    | draw g =>
      simp only [replayProgram]
      split
      · exact ih _
      · split
        · exact constructionOnly_bind _ _ (collect_only _ _ _ _) (fun _ => ih _)
        · trivial

theorem request_with (cache : Cache) (good : CacheOK ans cache) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) :
    let v := runWith ans (SpongefishCurrentMixedModeCompiler.request cache q valid)
    CacheOK ans v.result.1 ∧ v.result.2 = ans q ∧ v.result.1 q ≠ none ∧
      (∀ c, cache c ≠ none → v.result.1 c ≠ none) ∧ Known ans cache v.observations v.result.1 := by
  unfold SpongefishCurrentMixedModeCompiler.request
  cases found : cache q with
  | some d =>
    simp only [runWith]
    exact ⟨good,good q d found,by simp [found],fun _ h => h,fun c h => Or.inl h⟩
  | none =>
    simp only [runWith,answerOf]
    refine ⟨?_,by trivial,by simp [store],?_,?_⟩
    · intro c d stored
      unfold store at stored
      split at stored
      · rename_i same
        subst same
        exact (Option.some.inj stored).symm
      · exact good c d stored
    · intro c cached
      unfold store
      split
      · simp
      · exact cached
    · intro c cached
      unfold store at cached
      split at cached
      · rename_i same
        subst same
        exact Or.inr ⟨valid,List.mem_singleton_self _⟩
      · exact Or.inl cached

theorem collect_with (m : Pending) (positions : List Nat)
    (valid : ∀ p ∈ positions, DuplexEncoding.Admissible (coordinate m (p/32))) (cache : Cache)
    (good : CacheOK ans cache) :
    let v := runWith ans (collect m positions valid cache)
    CacheOK ans v.result.1 ∧
      v.result.2 = positions.map (fun p => ans (coordinate m (p/32)) ⟨p%32,Nat.mod_lt _ (by decide)⟩) ∧
      (∀ p ∈ positions, v.result.1 (coordinate m (p/32)) ≠ none) ∧
      (∀ c, cache c ≠ none → v.result.1 c ≠ none) ∧ Known ans cache v.observations v.result.1 := by
  induction positions generalizing cache with
  | nil => exact ⟨good,rfl,by simp,fun _ h => h,fun c h => Or.inl h⟩
  | cons p ps ih =>
    dsimp only
    simp only [collect,seq,runWith_bind]
    obtain ⟨good₁,answer₁,hit₁,mono₁,known₁⟩ := request_with ans cache good
      (coordinate m (p/32)) (valid p List.mem_cons_self)
    generalize (runWith ans (SpongefishCurrentMixedModeCompiler.request cache (coordinate m (p/32))
      (valid p List.mem_cons_self))) = first at *
    obtain ⟨obs₁,next,d⟩ := first
    dsimp only at good₁ answer₁ hit₁ mono₁ known₁ ⊢
    obtain ⟨good₂,answer₂,hit₂,mono₂,known₂⟩ := ih (fun j h => valid j (List.mem_cons_of_mem _ h))
      next good₁
    simp only [runWith] at good₂ answer₂ hit₂ mono₂ known₂ ⊢
    generalize (runWith ans (collect m ps (fun j h => valid j (List.mem_cons_of_mem _ h)) next)) = rest at *
    obtain ⟨obs₂,last,bs⟩ := rest
    dsimp only at good₂ answer₂ hit₂ mono₂ known₂ ⊢
    refine ⟨good₂,by rw [answer₁,answer₂]; rfl,?_,fun c h => mono₂ c (mono₁ c h),?_⟩
    · intro j member
      rcases List.mem_cons.mp member with rfl | later
      · exact mono₂ _ hit₁
      · exact hit₂ j later
    · intro c cached
      rcases known₂ c cached with before | seen
      · rcases known₁ c before with older | seen
        · exact Or.inl older
        · obtain ⟨v,member⟩ := seen
          exact Or.inr ⟨v,by simp [member]⟩
      · obtain ⟨v,member⟩ := seen
        exact Or.inr ⟨v,by simp [member]⟩

theorem observed_mono (obs obs' : List Observation) (q : Coordinate)
    (sub : ∀ o ∈ obs, o ∈ obs') (seen : Observed ans obs q) : Observed ans obs' q := by
  obtain ⟨valid,member⟩ := seen
  exact ⟨valid,sub _ member⟩

theorem group_bytes_pos (g : Group) : g.bytes ≠ 0 := by
  cases g <;> simp [Group.bytes,Group.elements]

theorem bind_frames (m : Pending) (bytes : List Byte) :
    (SpongefishPCSRoundFrames.bind m bytes).frames = m.frames := by
  unfold SpongefishPCSRoundFrames.bind; split <;> rfl

theorem bind_domain (m : Pending) (bytes : List Byte) :
    (SpongefishPCSRoundFrames.bind m bytes).domain = m.domain := by
  unfold SpongefishPCSRoundFrames.bind; split <;> rfl

theorem bind_nonempty (m : Pending) (bytes : List Byte) (nonempty : bytes ≠ []) :
    (SpongefishPCSRoundFrames.bind m bytes).run ≠ [] ∧
      (SpongefishPCSRoundFrames.bind m bytes).consumed = 0 := by
  simp [SpongefishPCSRoundFrames.bind,nonempty]

theorem codec_bytes_eq_nil (kind : WireKind) (value : kind.Value) :
    kind.codec.bytes value = [] ↔ kind.codec.size = 0 := by
  constructor
  · intro empty
    have length := congrArg List.length empty
    simpa only [Codec.bytes,List.length_ofFn,List.length_nil] using length
  · intro zero
    apply List.eq_nil_of_length_eq_zero
    simpa only [Codec.bytes,List.length_ofFn] using zero

theorem draw_facts (m : Pending) (n : Nat) (positive : n ≠ 0) :
    (draw m n).frames = (close m).frames ∧ (draw m n).run = [] ∧ (draw m n).domain = m.domain := by
  by_cases empty : m.run = [] <;> simp [draw,positive,close,empty]

theorem close_frames (m : Pending) (nonempty : m.run ≠ []) :
    (close m).frames = m.frames ++ [.absorb m.previous m.run] := by
  simp [close,nonempty]

theorem close_prefix (m : Pending) : m.frames <+: (close m).frames := by
  by_cases empty : m.run = []
  · simp [close,empty]
  · rw [close_frames m empty]
    exact List.prefix_append _ _

/-- Static frame shape of a call list: closed frames and whether a prover run is pending. Every group draws a positive number of bytes. -/
def frameShape : Nat × Bool → List Call → Nat × Bool
  | s, [] => s
  | s, .read kind :: rest => frameShape (s.1,s.2 || decide (kind.codec.size ≠ 0)) rest
  | s, .hint :: rest => frameShape s rest
  | s, .draw _ :: rest => frameShape (if s.2 then s.1+1 else s.1,false) rest

def Shaped (m : Pending) (s : Nat × Bool) : Prop :=
  m.frames.length = s.1 ∧ (s.2 = true ↔ m.run ≠ []) ∧ (m.run ≠ [] → m.consumed = 0)

theorem replay_shape (cur : SemanticCursor) (calls : List Call) (s : Nat × Bool)
    (shaped : Shaped cur.data.pending s) (good : CacheOK ans cur.cache) (fin : SemanticCursor)
    (ok : (runWith ans (replayProgram cur calls)).result = .ok fin) :
    Shaped fin.data.pending (frameShape s calls) ∧ CacheOK ans fin.cache ∧
      Known ans cur.cache (runWith ans (replayProgram cur calls)).observations fin.cache := by
  induction calls generalizing cur s with
  | nil =>
    simp only [replayProgram,runWith,Except.ok.injEq] at ok
    subst ok
    exact ⟨shaped,good,fun c h => Or.inl h⟩
  | cons call calls ih =>
    cases call with
    | read kind =>
      cases parsed : kind.codec.parse cur.data.narg with
      | none => simp [replayProgram,parsed,runWith] at ok
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        simp only [replayProgram,parsed] at ok ⊢
        refine ih (readNext cur kind value rest) _ ?_ good ok
        obtain ⟨frames,ready,zeroed⟩ := shaped
        change Shaped (SpongefishPCSRoundFrames.bind cur.data.pending (kind.codec.bytes value)) _
        by_cases zero : kind.codec.size = 0
        · have empty := (codec_bytes_eq_nil kind value).mpr zero
          rw [empty]
          simpa [Shaped,SpongefishPCSRoundFrames.bind,zero] using
            (⟨frames,ready,zeroed⟩ : Shaped cur.data.pending s)
        · have nonempty : kind.codec.bytes value ≠ [] := fun h => zero ((codec_bytes_eq_nil kind value).mp h)
          obtain ⟨run,consumed⟩ := bind_nonempty cur.data.pending _ nonempty
          refine ⟨by rw [bind_frames]; exact frames,?_,fun _ => consumed⟩
          simp [zero,run]
    | hint =>
      cases hints : cur.data.hints with
      | nil => simp [replayProgram,hints,runWith] at ok
      | cons bytes rest =>
        simp only [replayProgram,hints] at ok ⊢
        exact ih (hintNext cur bytes rest) s shaped good ok
    | draw g =>
      have positive := group_bytes_pos g
      by_cases guard : cur.data.pending.consumed + g.bytes ≤ maxCursor
      · simp only [replayProgram,positive,guard,↓reduceDIte,seq,runWith_bind] at ok ⊢
        obtain ⟨good₁,_,_,_,known₁⟩ := collect_with ans cur.data.pending
          (positions cur.data.pending g.bytes) (positions_valid _ cur.framed _ guard) cur.cache good
        generalize (runWith ans (collect cur.data.pending (positions cur.data.pending g.bytes)
          (positions_valid _ cur.framed _ guard) cur.cache)) = first at *
        obtain ⟨obs₁,cache,bytes⟩ := first
        dsimp only at good₁ known₁ ok ⊢
        obtain ⟨frames,ready,zeroed⟩ := shaped
        obtain ⟨drawFrames,drawRun,_⟩ := draw_facts cur.data.pending g.bytes positive
        have next : Shaped (draw cur.data.pending g.bytes) (if s.2 then s.1+1 else s.1,false) := by
          refine ⟨?_,by simp [drawRun],fun h => (h drawRun).elim⟩
          rw [drawFrames]
          by_cases empty : cur.data.pending.run = []
          · have notReady : s.2 = false := by simpa [empty] using ready
            simp [close,empty,notReady,frames]
          · have isReady : s.2 = true := ready.mpr empty
            simp [close_frames _ empty,isReady,frames]
        obtain ⟨shaped',good',known'⟩ := ih (drawn cur g.bytes guard cache bytes) _ next good₁ ok
        refine ⟨shaped',good',fun c cached => ?_⟩
        rcases known' c cached with before | seen
        · rcases known₁ c before with older | seen
          · exact Or.inl older
          · exact Or.inr (observed_mono ans _ _ c (fun o h => List.mem_append_left _ h) seen)
        · exact Or.inr (observed_mono ans _ _ c (fun o h => List.mem_append_right _ h) seen)
      · simp [replayProgram,positive,guard,runWith] at ok

/-- Successful replay of an appended call list splits at the cursor reached by the first part; observations split accordingly. -/
theorem replay_append (cur : SemanticCursor) (xs ys : List Call) (fin : SemanticCursor)
    (ok : (runWith ans (replayProgram cur (xs ++ ys))).result = .ok fin) :
    ∃ mid, (runWith ans (replayProgram cur xs)).result = .ok mid ∧
      (runWith ans (replayProgram mid ys)).result = .ok fin ∧
      (runWith ans (replayProgram cur (xs ++ ys))).observations =
        (runWith ans (replayProgram cur xs)).observations ++
          (runWith ans (replayProgram mid ys)).observations := by
  induction xs generalizing cur with
  | nil => exact ⟨cur,rfl,ok,rfl⟩
  | cons call xs ih =>
    cases call with
    | read kind =>
      cases parsed : kind.codec.parse cur.data.narg with
      | none => simp [replayProgram,parsed,runWith] at ok
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        simp only [List.cons_append,replayProgram,parsed] at ok ⊢
        exact ih _ ok
    | hint =>
      cases hints : cur.data.hints with
      | nil => simp [replayProgram,hints,runWith] at ok
      | cons bytes rest =>
        simp only [List.cons_append,replayProgram,hints] at ok ⊢
        exact ih _ ok
    | draw g =>
      have positive := group_bytes_pos g
      by_cases guard : cur.data.pending.consumed + g.bytes ≤ maxCursor
      · simp only [List.cons_append,replayProgram,positive,guard,↓reduceDIte,seq,runWith_bind]
          at ok ⊢
        generalize (runWith ans (collect cur.data.pending (positions cur.data.pending g.bytes)
          (positions_valid _ cur.framed _ guard) cur.cache)) = first at *
        obtain ⟨obs₁,cache,bytes⟩ := first
        dsimp only at ok ⊢
        obtain ⟨mid,first,second,split⟩ := ih (drawn cur g.bytes guard cache bytes) ok
        exact ⟨mid,first,second,by rw [split,List.append_assoc]⟩
      · simp [List.cons_append,replayProgram,positive,guard,runWith] at ok

/-- Groups of the draw calls, in order. -/
def drawGroups (calls : List Call) : List Group :=
  calls.filterMap fun call => match call with | .draw g => some g | _ => none

/-- Drawn bytes of the verifier events, in order. -/
def verifierBytes (events : List SourceEvent) : List (List Byte) :=
  events.filterMap fun event => match event with | .verifier bytes => some bytes | _ => none

/-- Facts about the `k`-th positive draw of a separated replay segment: its pending cursor `m`, group `g` and drawn bytes. -/
structure DrawFact (domain : Digest32) (base : Nat) (cache : Cache) (final : List ByteFrame)
    (obs : List Observation) (k : Nat) (g : Group) (m : Pending) (bytes : List Byte) : Prop where
  domain_eq : m.domain = domain
  run_ne : m.run ≠ []
  consumed_eq : m.consumed = 0
  framed : FrameDomain m
  guard : g.bytes ≤ maxCursor
  frames_eq : m.frames.length = base + k
  closed : (close m).frames <+: final
  bytes_eq : bytes =
    (positions m g.bytes).map (fun p => ans (coordinate m (p/32)) ⟨p%32,Nat.mod_lt _ (by decide)⟩)
  first : cache (coordinate m 0) ≠ none ∨ Observed ans obs (coordinate m 0)

/-- A replay segment without two verifier draws in a row (the source `scan`) adds one history frame per draw: the `k`-th draw closes the pending run into `base + k + 1` frames, its bytes are the fixed answers of its coordinates, and its first coordinate is cached at the start or observed in the segment. -/
theorem replay_draws (cur : SemanticCursor) (calls : List Call) (waiting : Bool)
    (ready : waiting = true ↔ cur.data.pending.run = [])
    (zeroed : cur.data.pending.run ≠ [] → cur.data.pending.consumed = 0)
    (separated : SpongefishCurrentRoundSeparation.scan waiting calls ≠ none)
    (good : CacheOK ans cur.cache) (fin : SemanticCursor)
    (ok : (runWith ans (replayProgram cur calls)).result = .ok fin) :
    ∃ (evs : List SourceEvent) (ms : List Pending),
      fin.data.events = cur.data.events ++ evs ∧ evs.length = calls.length ∧
      cur.data.pending.frames <+: fin.data.pending.frames ∧
      ms.length = (drawGroups calls).length ∧
      (verifierBytes evs).length = (drawGroups calls).length ∧
      ∀ k g m bytes, (drawGroups calls)[k]? = some g → ms[k]? = some m →
        (verifierBytes evs)[k]? = some bytes →
        DrawFact ans cur.data.pending.domain cur.data.pending.frames.length cur.cache
          fin.data.pending.frames (runWith ans (replayProgram cur calls)).observations k g m bytes := by
  induction calls generalizing cur waiting with
  | nil =>
    simp only [replayProgram,runWith,Except.ok.injEq] at ok
    subst ok
    refine ⟨[],[],by simp,rfl,List.prefix_refl _,rfl,rfl,?_⟩
    intro k g m bytes found
    simp [drawGroups] at found
  | cons call calls ih =>
    cases call with
    | read kind =>
      cases parsed : kind.codec.parse cur.data.narg with
      | none => simp [replayProgram,parsed,runWith] at ok
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        simp only [replayProgram,parsed] at ok ⊢
        have nextReady : (if kind.codec.size = 0 then waiting else false) = true ↔
            (readNext cur kind value rest).data.pending.run = [] := by
          change _ ↔ (SpongefishPCSRoundFrames.bind cur.data.pending (kind.codec.bytes value)).run = []
          by_cases zero : kind.codec.size = 0
          · rw [(codec_bytes_eq_nil kind value).mpr zero]
            simpa [zero,SpongefishPCSRoundFrames.bind] using ready
          · have nonempty : kind.codec.bytes value ≠ [] :=
              fun h => zero ((codec_bytes_eq_nil kind value).mp h)
            simp [zero,(bind_nonempty cur.data.pending _ nonempty).1]
        have nextZeroed : (readNext cur kind value rest).data.pending.run ≠ [] →
            (readNext cur kind value rest).data.pending.consumed = 0 := by
          change (SpongefishPCSRoundFrames.bind cur.data.pending (kind.codec.bytes value)).run ≠ [] →
            (SpongefishPCSRoundFrames.bind cur.data.pending (kind.codec.bytes value)).consumed = 0
          by_cases empty : kind.codec.bytes value = []
          · rw [empty]
            simpa [SpongefishPCSRoundFrames.bind] using zeroed
          · exact fun _ => (bind_nonempty cur.data.pending _ empty).2
        obtain ⟨evs,ms,events,length,prefixed,msLength,bytesLength,facts⟩ :=
          ih (readNext cur kind value rest) _ nextReady nextZeroed separated good ok
        have sameFrames : (readNext cur kind value rest).data.pending.frames = cur.data.pending.frames :=
          bind_frames _ _
        have sameDomain : (readNext cur kind value rest).data.pending.domain = cur.data.pending.domain :=
          bind_domain _ _
        refine ⟨.prover kind (kind.codec.bytes value) :: evs,ms,?_,by simp [length],
          sameFrames ▸ prefixed,by simpa [drawGroups] using msLength,
          by simpa [verifierBytes,drawGroups] using bytesLength,?_⟩
        · rw [events]
          simp [readNext,boundData]
        · intro k g m bytes found member drawn
          have fact := facts k g m bytes (by simpa [drawGroups] using found) member
            (by simpa [verifierBytes] using drawn)
          rw [sameDomain,sameFrames] at fact
          exact fact
    | hint =>
      cases hints : cur.data.hints with
      | nil => simp [replayProgram,hints,runWith] at ok
      | cons bytes rest =>
        simp only [replayProgram,hints] at ok ⊢
        obtain ⟨evs,ms,events,length,prefixed,msLength,bytesLength,facts⟩ :=
          ih (hintNext cur bytes rest) waiting ready zeroed separated good ok
        refine ⟨.hint bytes :: evs,ms,?_,by simp [length],prefixed,
          by simpa [drawGroups] using msLength,by simpa [verifierBytes,drawGroups] using bytesLength,?_⟩
        · rw [events]
          simp [hintNext]
        · intro k g m drawnBytes found member drawn
          exact facts k g m drawnBytes (by simpa [drawGroups] using found) member
            (by simpa [verifierBytes] using drawn)
    | draw g =>
      have positive := group_bytes_pos g
      have notWaiting : waiting = false := by
        cases waiting
        · rfl
        · simp [SpongefishCurrentRoundSeparation.scan] at separated
      subst notWaiting
      have nonempty : cur.data.pending.run ≠ [] := fun h => by simpa using ready.mpr h
      have consumed := zeroed nonempty
      have rest : SpongefishCurrentRoundSeparation.scan true calls ≠ none := by
        simpa [SpongefishCurrentRoundSeparation.scan] using separated
      by_cases guard : cur.data.pending.consumed + g.bytes ≤ maxCursor
      · simp only [replayProgram,positive,guard,↓reduceDIte,seq,runWith_bind] at ok ⊢
        obtain ⟨good₁,answer₁,hit₁,_,known₁⟩ := collect_with ans cur.data.pending
          (positions cur.data.pending g.bytes) (positions_valid _ cur.framed _ guard) cur.cache good
        generalize (runWith ans (collect cur.data.pending (positions cur.data.pending g.bytes)
          (positions_valid _ cur.framed _ guard) cur.cache)) = first at *
        obtain ⟨obs₁,cache,bytes⟩ := first
        dsimp only at good₁ answer₁ hit₁ known₁ ok ⊢
        obtain ⟨drawFrames,drawRun,drawDomain⟩ := draw_facts cur.data.pending g.bytes positive
        obtain ⟨evs,ms,events,length,prefixed,msLength,bytesLength,facts⟩ :=
          ih (drawn cur g.bytes guard cache bytes) true (by simp [drawn,drawRun])
            (fun h => (h drawRun).elim) rest good₁ ok
        have nextFrames : (drawn cur g.bytes guard cache bytes).data.pending.frames =
            cur.data.pending.frames ++ [.absorb cur.data.pending.previous cur.data.pending.run] :=
          drawFrames.trans (close_frames _ nonempty)
        refine ⟨.verifier bytes :: evs,cur.data.pending :: ms,?_,by simp [length],
          (List.prefix_append _ _).trans (nextFrames ▸ prefixed),
          by simp [drawGroups,msLength],by simpa [verifierBytes,drawGroups] using bytesLength,?_⟩
        · rw [events]
          simp [drawn]
        · intro k g' m drawnBytes found member drawnAt
          cases k with
          | zero =>
            simp only [drawGroups,List.filterMap_cons,List.getElem?_cons_zero,Option.some.injEq]
              at found
            simp only [List.getElem?_cons_zero,Option.some.injEq] at member
            simp only [verifierBytes,List.filterMap_cons,List.getElem?_cons_zero,Option.some.injEq]
              at drawnAt
            subst found member drawnAt
            have zeroPosition : 0 ∈ positions cur.data.pending g.bytes := by
              simp only [positions,consumed,List.mem_map,List.mem_range]
              exact ⟨0,Nat.pos_of_ne_zero positive,rfl⟩
            have hit := hit₁ 0 zeroPosition
            refine ⟨rfl,nonempty,consumed,cur.framed,by omega,by simp,?_,answer₁,?_⟩
            · rw [← drawFrames]
              exact prefixed
            · rcases known₁ _ hit with before | seen
              · exact Or.inl before
              · exact Or.inr (observed_mono ans _ _ _ (fun o h => List.mem_append_left _ h) seen)
          | succ k =>
            have fact := facts k g' m drawnBytes (by simpa [drawGroups] using found)
              (by simpa using member) (by simpa [verifierBytes] using drawnAt)
            refine ⟨fact.domain_eq.trans drawDomain,fact.run_ne,fact.consumed_eq,fact.framed,
              fact.guard,?_,fact.closed,fact.bytes_eq,?_⟩
            · rw [fact.frames_eq,nextFrames]
              simp only [List.length_append,List.length_singleton]
              omega
            · rcases fact.first with before | seen
              · rcases known₁ _ before with older | seen
                · exact Or.inl older
                · exact Or.inr (observed_mono ans _ _ _ (fun o h => List.mem_append_left _ h) seen)
              · exact Or.inr (observed_mono ans _ _ _ (fun o h => List.mem_append_right _ h) seen)
      · simp [replayProgram,positive,guard,runWith] at ok

end Replay

/-! ## The opening schedule: separation, draw order and group widths -/

section Schedule
open SpongefishCurrentOpeningAcceptance SpongefishCurrentRoundSeparation
variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

theorem scan_reads (xs : List Call) (reads : ∀ c ∈ xs, ∃ kind, c = .read kind) :
    scan false xs = some false := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    obtain ⟨kind,rfl⟩ := reads c List.mem_cons_self
    simp only [scan,ite_self]
    exact ih (fun d h => reads d (List.mem_cons_of_mem _ h))

/-- Every coordinate block but an invisible final tail ends with a nonempty prover payload after its draws. -/
theorem scan_callsOf (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p) :
    scan false (callsOf grinding q) = some false ∨
      ∃ j, q = .tail j ∧ isVisibleTail j = false ∧ scan false (callsOf grinding q) = some true := by
  cases q with
  | initial =>
    left
    simp [callsOf,powCalls,drawCalls,replyCalls,PCSBCSRounds.rawWidth,WHIRHistory.stackScalarCount,
      scan,WireKind.codec,vectorCodec]
  | fold i j =>
    left
    simp only [callsOf,powCalls,drawCalls,replyCalls,List.nil_append,scan_append]
    have width : PCSBCSRounds.rawWidth (CausalProbability.Coordinate.fold (c := cfg) i j) = 1 := rfl
    rw [width]
    simp only [one_ne_zero,↓reduceIte,scan,Option.bind_some,Bool.false_eq_true]
    have size : (WireKind.vector 2).codec.size ≠ 0 := by simp [WireKind.codec,vectorCodec]
    simp only [size,↓reduceIte]
    apply scan_reads
    intro c member
    split_ifs at member <;> simp_all
  | ood i j =>
    left
    simp only [callsOf,powCalls,drawCalls,replyCalls,List.nil_append]
    split_ifs <;> simp [scan,WireKind.codec,vectorCodec]
  | query i =>
    left
    simp only [callsOf,powCalls,drawCalls,replyCalls,scan_append,scan_pow]
    split_ifs <;> simp_all [scan,WireKind.codec,vectorCodec]
  | tail j =>
    cases visible : isVisibleTail j with
    | true =>
      left
      simp [callsOf,powCalls,drawCalls,replyCalls,visible,PCSBCSRounds.rawWidth,
        WHIRHistory.stackScalarCount,WHIRHistory.scalarCount,scan,WireKind.codec,vectorCodec]
    | false =>
      right
      refine ⟨j,rfl,visible,?_⟩
      simp [callsOf,powCalls,drawCalls,replyCalls,visible,PCSBCSRounds.rawWidth,
        WHIRHistory.stackScalarCount,WHIRHistory.scalarCount,scan]

theorem scan_flatMap_false {A : Type} (xs : List A) (f : A → List Call)
    (reset : ∀ x ∈ xs, scan false (f x) = some false) :
    scan false (xs.flatMap f) = some false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,scan_append,reset x List.mem_cons_self,Option.bind_some]
    exact ih (fun y h => reset y (List.mem_cons_of_mem _ h))

/-- The whole opening, for every grinding, never has two verifier draws without a nonempty prover payload between them. -/
theorem scan_opening_calls (grinding : Fin (cfg).folds.size → Fin 64) :
    scan false (openingCalls grinding) ≠ none := by
  have visible : ∀ q ∈ CausalProbability.visibleCoordinates cfg,
      scan false (callsOf grinding q) = some false := by
    intro q member
    rcases scan_callsOf grinding q with reset | ⟨j,rfl,invisible,_⟩
    · exact reset
    · exfalso
      simp only [CausalProbability.visibleCoordinates,List.mem_append,List.mem_cons,
        List.mem_flatMap,List.mem_ofFn,List.not_mem_nil] at member
      rcases member with ((same | none) | ⟨i,_,inLevel⟩) | ⟨k,same⟩
      · cases same
      · exact none.elim
      · unfold CausalProbability.levelCoordinates at inLevel
        split at inLevel
        · simp [List.mem_ofFn] at inLevel
        · cases inLevel
      · cases same
        simp only [isVisibleTail,decide_eq_false_iff_not] at invisible
        omega
  unfold openingCalls WHIRHistory.schedule
  rw [List.flatMap_append,scan_append,scan_flatMap_false _ _ visible,Option.bind_some]
  unfold WHIRHistory.hiddenTail
  split
  · simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rcases scan_callsOf grinding (.tail ⟨(cfg).logN - (cfg).folds.toList.sum - 1,by omega⟩) with
      reset | ⟨_,_,_,final⟩
    · rw [reset]; simp
    · rw [final]; simp
  · simp [scan]

/-- Draw-call groups match the opening draw list: a PCS draw of `q` uses `group q`. -/
def Matches : Option (Coord p) → Group → Prop
  | some q, g => g = group q
  | none, _ => True

theorem drawGroups_append (xs ys : List Call) :
    drawGroups (xs ++ ys) = drawGroups xs ++ drawGroups ys := by
  simp [drawGroups,List.filterMap_append]

theorem forall₂_flatMap {A B C : Type} (R : B → C → Prop) (xs : List A) (f : A → List B)
    (g : A → List C) (each : ∀ x ∈ xs, List.Forall₂ R (f x) (g x)) :
    List.Forall₂ R (xs.flatMap f) (xs.flatMap g) := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (each x List.mem_cons_self) (ih (fun y h => each y (List.mem_cons_of_mem _ h)))

theorem forall₂_getElem? {B C : Type} {R : B → C → Prop} :
    ∀ {xs : List B} {ys : List C}, List.Forall₂ R xs ys → ∀ (k : Nat) (a : B), xs[k]? = some a →
      ∃ b, ys[k]? = some b ∧ R a b
  | _,_,.nil,_,_,found => by simp at found
  | _,_,.cons head _,0,_,found => by
    simp only [List.getElem?_cons_zero,Option.some.injEq] at found
    subst found
    exact ⟨_,rfl,head⟩
  | _,_,.cons _ rest,k+1,a,found => by
    simp only [List.getElem?_cons_succ] at found ⊢
    exact forall₂_getElem? rest k a found

theorem opening_matches (grinding : Fin (cfg).folds.size → Fin 64) :
    List.Forall₂ Matches (SpongefishCurrentRoundPackets.openingDraws grinding)
      (drawGroups (openingCalls grinding)) := by
  have flat : ∀ xs : List (Coord p), drawGroups (xs.flatMap (callsOf grinding)) =
      xs.flatMap (fun q => drawGroups (callsOf grinding q)) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.flatMap_cons,drawGroups_append,ih]
  unfold openingCalls SpongefishCurrentRoundPackets.openingDraws
  rw [flat]
  apply forall₂_flatMap
  intro q _
  cases q with
  | initial =>
    simp [callsOf,powCalls,drawCalls,replyCalls,drawGroups,PCSBCSRounds.rawWidth,
      WHIRHistory.stackScalarCount,Matches]
  | fold i j =>
    simp only [callsOf,powCalls,drawCalls,replyCalls,drawGroups_append]
    split_ifs <;> simp_all [drawGroups,Matches]
  | ood i j =>
    simp only [callsOf,powCalls,drawCalls,replyCalls,drawGroups_append]
    split_ifs <;> simp_all [drawGroups,Matches]
  | query i =>
    simp only [callsOf,powCalls,drawCalls,replyCalls,drawGroups_append,powSchedule]
    split_ifs <;> simp_all [drawGroups,Matches]
  | tail j =>
    simp only [callsOf,powCalls,drawCalls,replyCalls,drawGroups_append]
    split_ifs <;> simp_all [drawGroups,Matches]

theorem group_bytes (q : Coord p) (width : PCSBCSRounds.rawWidth q ≠ 0) :
    (group q).bytes = 24 * PCSBCSRounds.rawWidth q := by
  cases q with
  | initial => rfl
  | fold i j => rfl
  | ood i j =>
    simp only [PCSBCSRounds.rawWidth,WHIRHistory.stackScalarCount,WHIRHistory.scalarCount] at width ⊢
    simp only [group,Group.bytes,Group.elements]
    congr 1
    omega
  | query i => rfl
  | tail j => rfl

theorem openingDraws_complete (grinding : Fin (cfg).folds.size → Fin 64) (q : Coord p)
    (scheduled : q ∈ WHIRHistory.schedule cfg) (width : PCSBCSRounds.rawWidth q ≠ 0) :
    ∃ k : Nat, (SpongefishCurrentRoundPackets.openingDraws grinding)[k]? = some (some q) := by
  have member : some q ∈ SpongefishCurrentRoundPackets.openingDraws grinding := by
    unfold SpongefishCurrentRoundPackets.openingDraws
    refine List.mem_flatMap.mpr ⟨q,scheduled,?_⟩
    simp [width]
  obtain ⟨k,found,same⟩ := List.getElem_of_mem member
  exact ⟨k,by rw [List.getElem?_eq_getElem found,same]⟩

end Schedule

/-! ## Grouped decoding of literal drawn bytes -/

section Decode
open SpongefishCurrentOpeningAcceptance PCSBCSChallengeOracle
variable {p : ParameterBounds.Profile}

/-- Drawn bytes agreeing with the concatenated packet blocks on the payload prefix decode to the grouped packet value. -/
theorem decode_grouped (q : Coord p) (packet : Fin (blocks (PCSBCSRounds.rawWidth q)) → Digest32)
    (bytes : List Byte)
    (agree : ∀ j (within : j < 24 * PCSBCSRounds.rawWidth q), bytes[j]? = some
      (packet ⟨j/32,by unfold blocks; omega⟩ ⟨j%32,Nat.mod_lt _ (by decide)⟩)) :
    decodeSample q bytes = grouped q packet := by
  have payload := grouped_payload_bytes q packet
  simp only [grouped,Equiv.apply_symm_apply] at payload
  unfold decodeSample grouped
  apply congrArg (rawVector q).symm
  funext k
  rw [← ByteCodec.decodeE_encodeE ((packetEquiv (PCSBCSRounds.rawWidth q) packet).1 k)]
  apply congrArg ByteCodec.decodeE
  funext i
  have index : (finProdFinEquiv (k,i) : Fin (PCSBCSRounds.rawWidth q * 24)).val = 24*k.val+i.val := by
    rw [finProdFinEquiv_apply_val]
    dsimp only
    omega
  have byteAt := payload (finProdFinEquiv (k,i))
  have flat : vectorBytes (PCSBCSRounds.rawWidth q) (packetEquiv (PCSBCSRounds.rawWidth q) packet).1
      (finProdFinEquiv (k,i)) = ByteCodec.encodeE ((packetEquiv (PCSBCSRounds.rawWidth q) packet).1 k) i := by
    simp [vectorBytes,flatten,scalarBytesEquiv]
  rw [agree (24*k.val+i.val) (by have := k.isLt; have := i.isLt; omega)]
  simp only [Option.getD_some]
  rw [← flat,byteAt]
  simp only [index]

end Decode

/-! ## Ideal sources on an arbitrary table -/

section Source
variable {Q : Nat} {Packet : Type} {Block : Packet → Type}
  (part : Partition (PublicCompressionCouplingMixed.Key Q) Packet Block)

/-- Fallback seed and raw oracle carried by a typed table. -/
def seedOf (table : (key : part.Key) → part.Answer (D := Digest32) key) : DuplexPublicSimulator.Seed :=
  fun n => part.join table (.inl n)

def roOf (table : (key : part.Key) → part.Answer (D := Digest32) key) : RawKey Q → Digest32 :=
  fun key => part.join table (.inr key)

theorem join_oracle (table : (key : part.Key) → part.Answer (D := Digest32) key) :
    part.join table = PublicCompressionCouplingMixed.oracle (seedOf part table) (roOf part table) := by
  funext key
  cases key <;> rfl

theorem join_encode (table : (key : part.Key) → part.Answer (D := Digest32) key) (c : Sigma Block) :
    part.join table (part.encode c) = table (.inl c.1) c.2 :=
  congrFun (congrFun (Partition.split_join part table) (.inl c.1)) c.2

theorem eval_source {R : Type} (iv : Digest32) (program : Program R) (counted : Counts Q program)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) :
    Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program counted) =
      (runIdeal (DuplexPublicSimulator.simulator Q) (roOf part table) iv ⟨seedOf part table,[]⟩
        program Q (Nat.le_refl Q) counted).view := by
  unfold SpongefishCurrentBCSKnowledge.source
  rw [PCSBCSChallengeOracle.Atomic.eval_program,join_oracle,PublicCompressionCouplingMixed.compile_actual]

/-- The source view of an appended program starts with the source view of its first part, at the same budget and partition, and continues with an ideal run of the continuation on that part's result. -/
theorem source_bind {R S : Type} (iv : Digest32) (program : Program R) (k : R → Program S)
    (counted : Counts Q (WHIRModeFinal.bind program k))
    (table : (key : part.Key) → part.Answer (D := Digest32) key) :
    ∃ (state : DuplexPublicSimulator.State) (rest : Nat) (cap : rest ≤ Q)
      (counted' : Counts rest (k (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program
        (WHIRModeFinal.bind_prefix_counted program k Q counted))).result)),
      Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv (WHIRModeFinal.bind program k) counted) =
        ⟨(Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program
            (WHIRModeFinal.bind_prefix_counted program k Q counted))).observations ++
          (runIdeal (DuplexPublicSimulator.simulator Q) (roOf part table) iv state _ rest cap
            counted').view.observations,
         (runIdeal (DuplexPublicSimulator.simulator Q) (roOf part table) iv state _ rest cap
            counted').view.result⟩ := by
  rw [eval_source,eval_source]
  exact ideal_bind _ _ iv program k _ Q (Nat.le_refl Q) counted

theorem mixedTrace_construction (iv : Digest32) (c : Coordinate) (valid : DuplexEncoding.Admissible c)
    (answer : Digest32) (bound : pathCost c ≤ Q) :
    ∀ (log : DuplexPublicSimulator.PublicLog) (obs : List Observation),
      (⟨.construction c valid,answer⟩ : Observation) ∈ obs →
      (⟨.inr (constructionKey Q iv c bound),answer⟩ :
        Sigma (fun _ : PublicCompressionCouplingMixed.Key Q => Digest32)) ∈
        PCSBCSNativePublicCapture.mixedTrace Q iv log obs
  | _,[],member => by cases member
  | log,o :: rest,member => by
    simp only [PCSBCSNativePublicCapture.mixedTrace,List.mem_append]
    rcases List.mem_cons.mp member with same | later
    · left
      subst same
      simp [PCSBCSNativePublicCapture.observationDraw,bound]
    · right
      exact mixedTrace_construction iv c valid answer bound _ rest later

/-- A construction observation of the source view whose raw key is a block of a packet records that whole packet in the atomic trace. -/
theorem observed_recorded {R : Type} (iv : Digest32) (program : Program R) (counted : Counts Q program)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) (c : Coordinate)
    (valid : DuplexEncoding.Admissible c) (answer : Digest32)
    (member : (⟨.construction c valid,answer⟩ : Observation) ∈
      (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv program counted)).observations)
    (block : Sigma Block)
    (recognized : ∀ bound, part.recognize (.inr (constructionKey Q iv c bound)) = some block) :
    (⟨.inl block.1,table (.inl block.1)⟩ : Sigma (part.Answer (D := Digest32))) ∈
      (Sampling.execute table (SpongefishCurrentBCSKnowledge.source part iv program counted)).2 := by
  have bound : pathCost c ≤ Q := by
    rw [eval_source] at member
    exact ideal_cost _ _ _ _ _ _ _ _ _ member
  unfold SpongefishCurrentBCSKnowledge.source
  apply PCSBCSAtomicAllocationTrace.recognized_recorded part table _ _ answer block _ (recognized bound)
  rw [join_oracle,PCSBCSNativePublicCapture.mixedTrace_actual]
  apply mixedTrace_construction iv c valid answer bound
  rw [← join_oracle,← PCSBCSChallengeOracle.Atomic.eval_program]
  exact member

end Source

/-! ## The semantic replay inside the initialized source program -/

theorem ideal_bind_parts {Q : Nat} {Seed State R S : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (p : Program R) (k : R → Program S)
    (state : State) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining (WHIRModeFinal.bind p k)) :
    (∀ o ∈ (runIdeal sim ro iv state p remaining cap
        (WHIRModeFinal.bind_prefix_counted p k remaining counted)).view.observations,
      o ∈ (runIdeal sim ro iv state (WHIRModeFinal.bind p k) remaining cap counted).view.observations) ∧
    ∃ (state' : State) (rest : Nat) (cap' : rest ≤ Q)
      (counted' : Counts rest (k (runIdeal sim ro iv state p remaining cap
        (WHIRModeFinal.bind_prefix_counted p k remaining counted)).view.result)),
      (runIdeal sim ro iv state (WHIRModeFinal.bind p k) remaining cap counted).view.result =
        (runIdeal sim ro iv state' _ rest cap' counted').view.result ∧
      ∀ o ∈ (runIdeal sim ro iv state' _ rest cap' counted').view.observations,
        o ∈ (runIdeal sim ro iv state (WHIRModeFinal.bind p k) remaining cap counted).view.observations := by
  obtain ⟨state',rest,cap',counted',same⟩ := ideal_bind sim ro iv p k state remaining cap counted
  rw [same]
  exact ⟨fun o h => List.mem_append_left _ h,state',rest,cap',counted',rfl,
    fun o h => List.mem_append_right _ h⟩

/-- A successful initialized source run contains the semantic replay of its whole call list from the literal initial cursor, answered by the ideal raw oracle, with all of its observations. -/
theorem afterPrefix_replay {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (tag instanceBytes : List Byte)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (calls : List Call)
    (state : State) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining
      (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram calls))
    (data : Data)
    (success : (runIdeal sim ro iv state
      (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram calls)
        remaining cap counted).view.result = some (.ok data)) :
    ∃ (session : Digest32) (narg : List Byte) (hints : List (List Byte)) (fin : SemanticCursor),
      (runWith (idealAnswer Q iv ro) (replayProgram
        (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints) calls)).result =
          .ok fin ∧ fin.data = data ∧
      ∀ o ∈ (runWith (idealAnswer Q iv ro) (replayProgram
        (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints) calls)).observations,
        o ∈ (runIdeal sim ro iv state
          (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram calls)
            remaining cap counted).view.observations := by
  change (runIdeal sim ro iv state (WHIRModeFinal.bind prefixProgram (fun input =>
    SpongefishCurrentInitializedMode.program iv tag instanceBytes input.narg input.hints calls))
      remaining cap counted).view.result = _ at success
  obtain ⟨_,state₁,rest₁,cap₁,counted₁,result₁,inside₁⟩ := ideal_bind_parts sim ro iv prefixProgram
    (fun input => SpongefishCurrentInitializedMode.program iv tag instanceBytes input.narg input.hints calls)
    state remaining cap counted
  generalize (runIdeal sim ro iv state prefixProgram remaining cap _).view.result = input at *
  change _ = (runIdeal sim ro iv state₁ (WHIRModeFinal.bind
    (SpongefishCurrentObservedSessionEntry.setupProgram iv tag instanceBytes input.narg input.hints) _)
      rest₁ cap₁ counted₁).view.result at result₁
  obtain ⟨_,state₂,rest₂,cap₂,counted₂,result₂,inside₂⟩ := ideal_bind_parts sim ro iv _ _
    state₁ rest₁ cap₁ counted₁
  generalize (runIdeal sim ro iv state₁
    (SpongefishCurrentObservedSessionEntry.setupProgram iv tag instanceBytes input.narg input.hints)
      rest₁ cap₁ _).view.result = setup at *
  cases setup with
  | none =>
    change _ = (runIdeal sim ro iv state₂ (.done none) rest₂ cap₂ counted₂).view.result at result₂
    rw [result₁,result₂] at success
    cases success
  | some actual =>
    change _ = (runIdeal sim ro iv state₂ (WHIRModeFinal.bind (replayProgram
      (SpongefishCurrentInitializedMode.initial actual.pending.domain instanceBytes input.narg input.hints)
        calls) _) rest₂ cap₂ counted₂).view.result at result₂
    obtain ⟨inside₃,state₃,rest₃,cap₃,counted₃,result₃,_⟩ := ideal_bind_parts sim ro iv _ _
      state₂ rest₂ cap₂ counted₂
    rw [ideal_runWith sim ro iv _ (replay_only _ _)] at inside₃ result₃
    generalize replayEq : (runWith (idealAnswer Q iv ro) (replayProgram
      (SpongefishCurrentInitializedMode.initial actual.pending.domain instanceBytes input.narg input.hints)
        calls)).result = replayed at *
    rw [result₁,result₂,result₃] at success
    cases replayed with
    | error failure => cases success
    | ok fin =>
      refine ⟨actual.pending.domain,input.narg,input.hints,fin,replayEq,?_,?_⟩
      · simpa [runIdeal,eraseResult] using success
      · intro o member
        exact inside₁ o (inside₂ o (inside₃ o member))

/-! ## Opening packets of the counted current source -/

section Packets
open SpongefishCurrentOpeningAcceptance SpongefishCurrentRoundPackets
variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

/-- Static frame shape at the opening start after replaying `pre` from the literal initial cursor: `(boundary,true)` means `boundary` closed frames and a pending nonempty prover run. -/
def openingShape (instanceBytes : List Byte) (pre : List Call) : Nat × Bool :=
  frameShape (0,decide (instanceBytes ≠ [])) pre

theorem frameShape_append (s : Nat × Bool) (xs ys : List Call) :
    frameShape s (xs ++ ys) = frameShape (frameShape s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons call xs ih => cases call <;> exact ih _

/-- A call list ending with a positive read leaves a pending prover run, so its static shape is `(boundary,true)` for `boundary := (openingShape instanceBytes pre).1`. -/
theorem openingShape_ready (instanceBytes : List Byte) (pre pre' : List Call) (kind : WireKind)
    (ends : pre = pre' ++ [.read kind]) (positive : kind.codec.size ≠ 0) :
    openingShape instanceBytes pre = ((openingShape instanceBytes pre).1,true) := by
  unfold openingShape
  rw [ends,frameShape_append]
  simp [frameShape,positive]

/-- The events of the opening calls: the suffix of one event per opening call. -/
def openingEvents (grinding : Fin (cfg).folds.size → Fin 64) (events : List SourceEvent) :
    List SourceEvent :=
  events.drop (events.length - (openingCalls grinding).length)

theorem close_domain (m : Pending) : (close m).domain = m.domain := by
  unfold close; split <;> rfl

theorem initial_shaped (session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) :
    Shaped (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints).data.pending
      (0,decide (instanceBytes ≠ [])) := by
  by_cases empty : instanceBytes = [] <;>
    simp [Shaped,SpongefishCurrentInitializedMode.initial,forget,
      SpongefishCurrentObservedSessionEntry.cursor,SpongefishPCSRoundFrames.bind,empty]

/-- Opening draws of the counted current source as exposed round packets, on an arbitrary ideal table. The source is the initialized current program of `pre ++ openingCalls grinding` followed by an arbitrary continuation `k`. If its initialized part returns a successful replay with data `data`, then the `j`-th opening draw has a history with `boundary + j + 1` frames whose output blocks supply its literal drawn bytes, earlier histories are frame prefixes of later ones, and every PCS draw of `q` is a packet with coordinate `q` whose complete answer is recorded in the atomic trace and whose grouped value is the decoded literal drawn bytes. -/
theorem opening_packets {S : Type} (Q : Nat) (iv : Digest32)
    (grinding : Fin (cfg).folds.size → Fin 64) (boundary : Nat)
    (tag instanceBytes : List Byte) (pre : List Call)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (k : Option SpongefishCurrentInitializedMode.Result → Program S)
    (counted : Counts Q (WHIRModeFinal.bind (SpongefishCurrentInitializedMode.afterPrefix iv tag
      instanceBytes prefixProgram (pre ++ openingCalls grinding)) k))
    (shape : openingShape instanceBytes pre = (boundary,true))
    (table : (key : Key p Q iv grinding boundary) → Answer p Q iv grinding boundary key)
    (data : Data)
    (success : (Sampling.eval table (SpongefishCurrentBCSKnowledge.source
      (partition p Q iv grinding boundary) iv
      (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram
        (pre ++ openingCalls grinding))
      (WHIRModeFinal.bind_prefix_counted _ k Q counted))).result = some (.ok data)) :
    ∃ histories : List FramedHistory,
      histories.length = (openingDraws grinding).length ∧
      (∀ (j : Nat) (h : FramedHistory), histories[j]? = some h → h.frames.length = boundary + j + 1) ∧
      (∀ (i j : Nat) (hi hj : FramedHistory), i ≤ j → histories[i]? = some hi →
        histories[j]? = some hj → hi = {hj with frames := hj.frames.take (boundary + i + 1)}) ∧
      (verifierBytes (openingEvents grinding data.events)).length = (openingDraws grinding).length ∧
      (∀ (j : Nat) (h : FramedHistory) (bytes : List Byte), histories[j]? = some h →
        (verifierBytes (openingEvents grinding data.events))[j]? = some bytes →
        ∃ g, (drawGroups (openingCalls grinding))[j]? = some g ∧
          bytes = (List.range g.bytes).map (fun i => idealAnswer Q iv
            (roOf (partition p Q iv grinding boundary) table) ⟨h,.output (i/32)⟩
              ⟨i%32,Nat.mod_lt _ (by decide)⟩)) ∧
      ∀ (j : Nat) (q : Coord p), (openingDraws grinding)[j]? = some (some q) →
        ∃ (packet : Packet p Q grinding boundary) (bytes : List Byte),
          packet.coord = q ∧ histories[j]? = some packet.history ∧
          (verifierBytes (openingEvents grinding data.events))[j]? = some bytes ∧
          decodeSample packet.coord bytes =
            PCSBCSChallengeOracle.grouped packet.coord (table (.inl packet)) ∧
          (⟨.inl packet,table (.inl packet)⟩ : Sigma (Answer p Q iv grinding boundary)) ∈
            (Sampling.execute table (SpongefishCurrentBCSKnowledge.source
              (partition p Q iv grinding boundary) iv
              (WHIRModeFinal.bind (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes
                prefixProgram (pre ++ openingCalls grinding)) k) counted)).2 := by
  let part := partition p Q iv grinding boundary
  let ro := roOf part table
  let ans := idealAnswer Q iv ro
  rw [eval_source] at success
  obtain ⟨session,narg,hints,fin,replayOk,finData,replayInside⟩ := afterPrefix_replay
    (DuplexPublicSimulator.simulator Q) ro iv tag instanceBytes prefixProgram
    (pre ++ openingCalls grinding) _ Q (Nat.le_refl Q) _ data success
  obtain ⟨oldInside,_⟩ := ideal_bind_parts (DuplexPublicSimulator.simulator Q) ro iv _ k
    ⟨seedOf part table,[]⟩ Q (Nat.le_refl Q) counted
  have inFinal : ∀ o ∈ (runWith ans (replayProgram
      (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints)
        (pre ++ openingCalls grinding))).observations,
      o ∈ (Sampling.eval table (SpongefishCurrentBCSKnowledge.source part iv _ counted)).observations := by
    rw [eval_source]
    exact fun o h => oldInside o (replayInside o h)
  obtain ⟨mid,preOk,openOk,obsSplit⟩ := replay_append ans _ pre (openingCalls grinding) fin replayOk
  obtain ⟨midShaped,midGood,midKnown⟩ := replay_shape ans _ pre _
    (initial_shaped session instanceBytes narg hints) (fun _ _ h => by cases h) mid preOk
  rw [show frameShape (0,decide (instanceBytes ≠ [])) pre = (boundary,true) from shape] at midShaped
  obtain ⟨midFrames,midReady,midZeroed⟩ := midShaped
  have midRun : mid.data.pending.run ≠ [] := midReady.mp rfl
  obtain ⟨evs,ms,events,evLength,_,msLength,bytesLength,facts⟩ := replay_draws ans mid
    (openingCalls grinding) false (by simpa using midRun) midZeroed (scan_opening_calls grinding)
    midGood fin openOk
  have openEvents : openingEvents grinding data.events = evs := by
    rw [← finData,events]
    unfold openingEvents
    rw [List.length_append,evLength,Nat.add_sub_cancel]
    exact List.drop_left
  have matched := opening_matches grinding (p := p)
  have drawLength : (drawGroups (openingCalls grinding)).length = (openingDraws grinding).length :=
    matched.length_eq.symm
  have factAt : ∀ j m, ms[j]? = some m → ∃ g bytes, (drawGroups (openingCalls grinding))[j]? = some g ∧
      (verifierBytes evs)[j]? = some bytes ∧
      DrawFact ans mid.data.pending.domain mid.data.pending.frames.length mid.cache
        fin.data.pending.frames (runWith ans (replayProgram mid (openingCalls grinding))).observations
        j g m bytes := by
    intro j m found
    have within : j < ms.length := (List.getElem?_eq_some_iff.mp found).1
    obtain ⟨g,hg⟩ : ∃ g, (drawGroups (openingCalls grinding))[j]? = some g :=
      ⟨_,List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨bytes,hb⟩ : ∃ bytes, (verifierBytes evs)[j]? = some bytes :=
      ⟨_,List.getElem?_eq_getElem (by omega)⟩
    exact ⟨g,bytes,hg,hb,facts j g m bytes hg found hb⟩
  have historyLength : ∀ j m, ms[j]? = some m →
      ((close m).core.history.frames).length = boundary + j + 1 := by
    intro j m found
    obtain ⟨g,bytes,_,_,fact⟩ := factAt j m found
    simp only [Pending.core,List.length_map,close_frames m fact.run_ne,List.length_append,
      List.length_singleton,fact.frames_eq,midFrames]
  refine ⟨ms.map (fun m => (close m).core.history),by simp [msLength,drawLength],?_,?_,
    by rw [openEvents,bytesLength,drawLength],?_,?_⟩
  · intro j h found
    rw [List.getElem?_map] at found
    obtain ⟨m,member,rfl⟩ := Option.map_eq_some_iff.mp found
    exact historyLength j m member
  · intro i j hi hj order foundI foundJ
    rw [List.getElem?_map] at foundI foundJ
    obtain ⟨mi,memberI,rfl⟩ := Option.map_eq_some_iff.mp foundI
    obtain ⟨mj,memberJ,rfl⟩ := Option.map_eq_some_iff.mp foundJ
    obtain ⟨_,_,_,_,factI⟩ := factAt i mi memberI
    obtain ⟨_,_,_,_,factJ⟩ := factAt j mj memberJ
    have lengthI := historyLength i mi memberI
    have lengthJ := historyLength j mj memberJ
    simp only [Pending.core,List.length_map] at lengthI lengthJ
    have nested : (close mi).frames <+: (close mj).frames :=
      List.prefix_of_prefix_length_le factI.closed factJ.closed (by omega)
    have taken := List.prefix_iff_eq_take.mp nested
    rw [lengthI] at taken
    simp only [Pending.core,close_domain,factI.domain_eq,factJ.domain_eq,← List.map_take,← taken]
  · intro j h bytes found bytesAt
    rw [List.getElem?_map] at found
    obtain ⟨m,member,rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨g,bytes',groupAt,bytesAt',fact⟩ := factAt j m member
    rw [openEvents,bytesAt'] at bytesAt
    cases bytesAt
    refine ⟨g,groupAt,?_⟩
    rw [fact.bytes_eq]
    simp only [positions,fact.consumed_eq,Nat.zero_add,List.map_map]
    rfl
  · intro j q found
    obtain ⟨g,groupAt,groupEq⟩ := forall₂_getElem? matched j (some q) found
    change g = group q at groupEq
    have within : j < ms.length := by
      have := (List.getElem?_eq_some_iff.mp groupAt).1
      omega
    obtain ⟨m,member⟩ : ∃ m, ms[j]? = some m := ⟨_,List.getElem?_eq_getElem within⟩
    obtain ⟨g',bytes,groupAt',bytesAt,fact⟩ := factAt j m member
    rw [groupAt] at groupAt'
    cases groupAt'
    subst groupEq
    have width := openingDraws_width grinding q (List.mem_of_getElem? found)
    have groupBytes := group_bytes q width
    have seen : Observed ans (runWith ans (replayProgram
        (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints)
          (pre ++ openingCalls grinding))).observations (coordinate m 0) := by
      rw [obsSplit]
      rcases fact.first with cached | observed
      · rcases midKnown _ cached with impossible | observed
        · exact (impossible rfl).elim
        · exact observed_mono ans _ _ _ (fun o h => List.mem_append_left _ h) observed
      · exact observed_mono ans _ _ _ (fun o h => List.mem_append_right _ h) observed
    obtain ⟨valid0,seenAt⟩ := seen
    have bound0 : pathCost (coordinate m 0) ≤ Q := by
      have final := inFinal _ seenAt
      rw [eval_source] at final
      exact ideal_cost _ _ _ _ _ _ _ _ _ final
    have bound : ∀ b, pathCost (coordinate m b) ≤ Q := fun b => (coordinate_cost m b).le.trans bound0
    have small : ∀ b : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth q)), b.val < 2^44 := by
      intro b
      have := b.isLt
      have guard := fact.guard
      simp only [PCSBCSChallengeOracle.blocks,maxCursor] at this guard
      omega
    let packet : Packet p Q grinding boundary :=
      { history := (close m).core.history
        coord := q
        classified := by
          unfold classify
          rw [historyLength j m member]
          simp [show boundary < boundary + j + 1 by omega,
            show boundary + j + 1 - boundary - 1 = j by omega,found]
        admissible := fun b => coordinate_admissible m fact.framed b.val (small b)
        bounded := fun b => bound b.val }
    have blockAnswer : ∀ b : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth q)),
        ans (coordinate m b.val) = table (.inl packet) b := by
      intro b
      have encoded : part.encode ⟨packet,b⟩ = .inr (constructionKey Q iv (coordinate m b.val) (bound b.val)) :=
        rfl
      simp only [ans,idealAnswer,bound b.val,↓reduceDIte,ro,roOf]
      rw [← encoded]
      exact join_encode part table ⟨packet,b⟩
    refine ⟨packet,bytes,rfl,by simp [member,packet],by rw [openEvents]; exact bytesAt,?_,?_⟩
    · apply decode_grouped
      intro i within
      rw [fact.bytes_eq]
      change i < 24 * PCSBCSRounds.rawWidth q at within
      have inGroup : i < (group q).bytes := by omega
      simp only [positions,fact.consumed_eq,Nat.zero_add,List.map_map,List.getElem?_map,
        List.getElem?_range inGroup,Option.map_some,Function.comp_apply]
      exact congrArg some (congrFun (blockAnswer ⟨i/32,by unfold PCSBCSChallengeOracle.blocks; omega⟩) _)
    · apply observed_recorded part iv _ counted table (coordinate m 0) valid0 (ans (coordinate m 0))
        (inFinal _ seenAt) ⟨packet,firstBlock packet⟩
      intro bound'
      have encoded : part.encode ⟨packet,firstBlock packet⟩ = .inr (constructionKey Q iv (coordinate m 0) bound') :=
        rfl
      rw [← encoded]
      exact part.recognize_encode _

/-- Every PCS coordinate of the schedule with a positive draw width is an exposed packet of the successful counted current source. -/
theorem opening_packet_exposed {S : Type} (Q : Nat) (iv : Digest32)
    (grinding : Fin (cfg).folds.size → Fin 64) (boundary : Nat)
    (tag instanceBytes : List Byte) (pre : List Call)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (k : Option SpongefishCurrentInitializedMode.Result → Program S)
    (counted : Counts Q (WHIRModeFinal.bind (SpongefishCurrentInitializedMode.afterPrefix iv tag
      instanceBytes prefixProgram (pre ++ openingCalls grinding)) k))
    (shape : openingShape instanceBytes pre = (boundary,true))
    (table : (key : Key p Q iv grinding boundary) → Answer p Q iv grinding boundary key)
    (data : Data)
    (success : (Sampling.eval table (SpongefishCurrentBCSKnowledge.source
      (partition p Q iv grinding boundary) iv
      (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram
        (pre ++ openingCalls grinding))
      (WHIRModeFinal.bind_prefix_counted _ k Q counted))).result = some (.ok data))
    (q : Coord p) (scheduled : q ∈ WHIRHistory.schedule cfg) (width : PCSBCSRounds.rawWidth q ≠ 0) :
    ∃ (packet : Packet p Q grinding boundary) (j : Nat) (bytes : List Byte),
      packet.coord = q ∧ packet.history.frames.length = boundary + j + 1 ∧
      (verifierBytes (openingEvents grinding data.events))[j]? = some bytes ∧
      decodeSample packet.coord bytes =
        PCSBCSChallengeOracle.grouped packet.coord (table (.inl packet)) ∧
      (⟨.inl packet,table (.inl packet)⟩ : Sigma (Answer p Q iv grinding boundary)) ∈
        (Sampling.execute table (SpongefishCurrentBCSKnowledge.source
          (partition p Q iv grinding boundary) iv
          (WHIRModeFinal.bind (SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes
            prefixProgram (pre ++ openingCalls grinding)) k) counted)).2 := by
  obtain ⟨j,found⟩ := openingDraws_complete grinding q scheduled width
  obtain ⟨histories,_,frames,_,_,_,packets⟩ := opening_packets Q iv grinding boundary tag instanceBytes
    pre prefixProgram k counted shape table data success
  obtain ⟨packet,bytes,coord,history,bytesAt,value,recorded⟩ := packets j q found
  exact ⟨packet,j,bytes,coord,frames j _ history,bytesAt,value,recorded⟩

end Packets

#print axioms ideal_runWith
#print axioms ideal_bind
#print axioms replay_shape
#print axioms replay_append
#print axioms replay_draws
#print axioms scan_opening_calls
#print axioms opening_matches
#print axioms decode_grouped
#print axioms observed_recorded
#print axioms afterPrefix_replay
#print axioms opening_packets
#print axioms opening_packet_exposed
#print axioms source_bind
#print axioms openingShape_ready

end Whir.SpongefishCurrentOpeningPackets
