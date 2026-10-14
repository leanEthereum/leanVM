import Whir.WHIRPhysicalVerifier
import Whir.WHIRPhysicalHistory

/-! Operational replay of the actual counted physical packet reader. The source program, not a replay-correctness premise, supplies its scalar responses, query rows and complete challenge vectors. -/
namespace Whir.WHIRPhysicalReplay
open Concrete Protocol FiatShamirGame DuplexModeGame PublicMerkleProgram MerkleTransport
open RawOracleCoupling RawOracleCoupling.Concrete WHIRPhysicalVerifier

/-- Later query openings may append rows, but cannot change a previously opened row array. -/
def ExtendsRows {p : ParameterBounds.Profile} (before after : WireState p) : Prop :=
  ∃ suffix, after.rows = before.rows ++ suffix

theorem ExtendsRows.refl {p : ParameterBounds.Profile} (state : WireState p) : ExtendsRows state state :=
  ⟨#[],by simp⟩

theorem ExtendsRows.trans {p : ParameterBounds.Profile} {a b c : WireState p}
    (ab : ExtendsRows a b) (bc : ExtendsRows b c) : ExtendsRows a c := by
  obtain ⟨first,hfirst⟩ := ab
  obtain ⟨second,hsecond⟩ := bc
  exact ⟨first ++ second,by simp [hsecond,hfirst,Array.append_assoc]⟩

theorem ExtendsRows.get {p : ParameterBounds.Profile} {before after : WireState p}
    (extended : ExtendsRows before after) (i : Nat) (bound : i < before.rows.size) :
    after.rows[i]! = before.rows[i]! := by
  obtain ⟨suffix,extended⟩ := extended
  rw [extended]
  rw [getElem!_pos (before.rows ++ suffix) i (by simp; omega),
    getElem!_pos before.rows i bound,Array.getElem_append_left bound]

/-- A query answer is opened before the next scalar response can consume its rows. -/
def PreviousCovered {p : ParameterBounds.Profile} (state : WireState p) : Prop :=
  ∀ i, state.previous = some (.query i) → i.val < state.rows.size

theorem nonceMatches_shape {c : Config} (q : CausalProbability.Coordinate c)
    (pending : WHIRHistory.Pending) (matched : nonceMatches q pending = true) :
    WHIRReplay.nonceShape q pending = true := by
  cases q <;> cases hn : pending.nonce <;> simp [nonceMatches,WHIRReplay.nonceShape,hn] at matched ⊢

theorem afterNonce_fields {p : ParameterBounds.Profile} {ctx : RawWHIRKeys.Context} {Q : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} (state out : WireState p)
    (nonce : WHIRPowProgram.Outcome ctx Q packet) (ok : afterNonce state nonce = some out) :
    out.tape = state.tape ∧ out.previous = state.previous ∧ out.replies = state.replies ∧
      out.rows = state.rows ∧ out.initial = state.initial := by
  unfold afterNonce at ok
  split at ok
  · cases Option.some.inj ok
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · cases cached : state.outputCache with
    | none => simp [cached] at ok
    | some digest =>
      simp only [cached,Option.map_some,Option.some.injEq] at ok
      subst out
      exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem announce_erase {cap : Nat} {R : Type} (root : Option Digest32)
    (next : WHIRSourceChronology.Source cap R) :
    WHIRSourceChronology.erase (announce root next) = WHIRSourceChronology.erase next := by
  cases root <;> rfl

theorem takeSample_fields {p : ParameterBounds.Profile} (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (state out : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (trace : List Observation) (run : Runs (takeSample lanes proofs state q x) trace (some out)) :
    out.replies = state.replies ∧ out.tape = (recordSample state q x).tape ∧
      out.previous = some q ∧ out.initial = (recordSample state q x).initial ∧
      ExtendsRows state out ∧ PreviousCovered out := by
  cases q with
  | query i =>
    simp only [takeSample] at run
    split at run
    · rename_i index
      cases hp : proofs[i.val]? <;> cases hr : state.roots[i.val]?
      · simp only [hp,hr] at run
        cases run
      · simp only [hp,hr] at run
        cases run
      · simp only [hp,hr] at run
        cases run
      · simp only [hp,hr] at run
        obtain ⟨before,opened,after,_,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases opened with
        | none => cases continued
        | some opened =>
          cases continued
          refine ⟨rfl,rfl,rfl,rfl,⟨#[opened.rows],by simp⟩,?_⟩
          intro j same
          have equal : i = j := by
            exact CausalProbability.Coordinate.query.inj (Option.some.inj same)
          subst j
          simp only [Array.size_push]
          omega
    · cases run
  | initial =>
    cases run
    exact ⟨rfl,rfl,rfl,rfl,ExtendsRows.refl _,by simp [PreviousCovered,recordSample]⟩
  | fold i j =>
    cases run
    exact ⟨rfl,rfl,rfl,rfl,ExtendsRows.refl _,by simp [PreviousCovered,recordSample]⟩
  | ood i j =>
    cases run
    exact ⟨rfl,rfl,rfl,rfl,ExtendsRows.refl _,by simp [PreviousCovered,recordSample]⟩
  | tail j =>
    cases run
    exact ⟨rfl,rfl,rfl,rfl,ExtendsRows.refl _,by simp [PreviousCovered,recordSample]⟩

theorem absorbResponse_rows {p : ParameterBounds.Profile} (state out : WireState p)
    (pending : WHIRHistory.Pending) (root : Option Digest32)
    (ok : absorbResponse state pending = some (out,root)) :
    out.rows = state.rows ∧ out.tape = state.tape ∧ out.previous = state.previous ∧
      out.initial = state.initial := by
  unfold absorbResponse at ok
  cases previous : state.previous with
  | none =>
    simp only [previous] at ok
    split at ok
    · cases Option.some.inj ok
      exact ⟨rfl,rfl,previous,rfl⟩
    · contradiction
  | some q =>
    simp only [previous] at ok
    change (WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending).bind _ =
      some (out,root) at ok
    cases parsed : WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending with
    | none => simp [parsed] at ok
    | some response =>
      simp only [parsed,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at ok
      cases ok.1
      exact ⟨rfl,rfl,rfl,rfl⟩

/-- The transition relation retains the real scalar parse and physical opening run. It is derived below from source execution, not supplied as a cryptographic premise. -/
inductive Step (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (p : ParameterBounds.Profile) (lanes : Nat) (proofs : Array PrunedMerklePaths)
    (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p) :
    WireState p → GroupAnswer ctx Q (.inl packet) → WireState p → Prop where
  | run {state absorbed root bound raw checked trace} {nonce : WHIRPowProgram.Outcome ctx Q packet}
      (parsed : absorbResponse state (packet.val.messages.headD ⟨[],none⟩) = some (absorbed,root))
      (size : packet.val.messages.length = absorbed.replies.size + 1)
      (shape : nonceMatches (packetQuery ctx Q p packet profile) (packet.val.messages.headD ⟨[],none⟩) = true)
      (boundNonce : afterNonce absorbed nonce = some bound)
      (accepted : nonce.accepted = true)
      (opened : Runs (takeSample lanes proofs bound (packetQuery ctx Q p packet profile)
        (packetSample ctx stack Q p packet profile raw)) trace (some checked)) :
      Step ctx stack Q p lanes proofs packet profile state raw (withOutput ctx Q packet raw checked)

inductive Trace (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q : Nat) (p : ParameterBounds.Profile) (lanes : Nat) (proofs : Array PrunedMerklePaths) :
    List (RawWHIRKeys.Packet ctx Q) → WireState p → WireState p →
      List (Sigma (GroupAnswer ctx Q)) → Prop where
  | nil (state) : Trace ctx stack Q p lanes proofs [] state state []
  | cons {packet packets state next final raw history} (profile : packet.val.profile = p)
      (step : Step ctx stack Q p lanes proofs packet profile state raw next)
      (rest : Trace ctx stack Q p lanes proofs packets next final history) :
      Trace ctx stack Q p lanes proofs (packet::packets) state final (⟨.inl packet,raw⟩::history)

theorem readPhysicalPackets_trace {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (p : ParameterBounds.Profile) (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (packets : List (RawWHIRKeys.Packet ctx Q))
    (profiles : ∀ packet ∈ packets, packet.val.profile = p) (state : WireState p)
    (next : WireState p → List (Sigma (GroupAnswer ctx Q)) → WHIRSourceChronology.Source cap (Option R))
    (observations : List Observation) (result : R)
    (run : Runs (WHIRSourceChronology.erase
      (readPhysicalPackets ctx stack Q p lanes proofs none packets profiles state next)) observations (some result)) :
    ∃ final history suffix, Trace ctx stack Q p lanes proofs packets state final history ∧
      Runs (WHIRSourceChronology.erase (next final history)) suffix (some result) := by
  induction packets generalizing state next observations with
  | nil => exact ⟨state,[],observations,.nil state,run⟩
  | cons packet packets ih =>
    simp only [readPhysicalPackets] at run
    cases parsed : absorbResponse state (packet.val.messages.headD ⟨[],none⟩) with
    | none => simp only [parsed,WHIRSourceChronology.erase] at run; cases run
    | some value =>
      obtain ⟨absorbed,root⟩ := value
      simp only [parsed] at run
      split at run
      · rename_i guards
        rw [announce_erase,sourceLift_erase] at run
        obtain ⟨before,nonce,after,_,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases boundNonce : afterNonce absorbed nonce with
        | none => simp only [boundNonce,WHIRSourceChronology.erase] at continued; cases continued
        | some bound =>
          simp only [boundNonce] at continued
          split at continued
          · rename_i accepted
            rw [sourceLift_erase] at continued
            obtain ⟨beforeRaw,raw,afterRaw,_,_,read⟩ := (Runs.bind_iff _ _).mp continued
            rw [sourceLift_erase] at read
            obtain ⟨beforeOpen,opened,afterOpen,_,opening,rest⟩ := (Runs.bind_iff _ _).mp read
            cases opened with
            | none => cases rest
            | some checked =>
              obtain ⟨final,history,suffix,traced,last⟩ := ih _ _ _ _ rest
              exact ⟨final,⟨.inl packet,raw⟩::history,suffix,
                .cons (profiles packet (by simp))
                  (.run parsed guards.1 guards.2 boundNonce accepted opening) traced,last⟩
          · cases continued
      · cases run

theorem packetQuery_eq (ctx : RawWHIRKeys.Context) (Q : Nat) (p : ParameterBounds.Profile)
    (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p) (statement : Digest32) :
    packetQuery ctx Q p packet profile = WHIRReplay.query p (statement,packet.val.messages) := by
  cases profile
  rfl

theorem packetQuery_position (ctx : RawWHIRKeys.Context) (Q : Nat) (p : ParameterBounds.Profile)
    (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p) :
    CausalProbability.position (packetQuery ctx Q p packet profile) = packet.val.messages.length - 1 := by
  cases profile
  have bound := WHIRHistory.scheduledAdmissible_depth _ _ packet.property.2.2.1
  have positive := List.length_pos_iff.mpr packet.property.2.1
  have lt : packet.val.messages.length - 1 < WHIRHistory.depth (ParameterBounds.config packet.val.profile) := by omega
  rw [packetQuery_eq _ _ _ _ rfl packet.val.statement]
  change CausalProbability.position (WHIRHistory.queryFor _ (packet.val.statement,packet.val.messages)) = _
  rw [WHIRHistory.queryFor_at _ _ _ ⟨_,lt⟩ (by change _ = packet.val.messages.length - 1 + 1; omega)]
  exact WHIRHistory.position_schedule_get _ _

theorem packetQuery_initial (ctx : RawWHIRKeys.Context) (Q : Nat) (p : ParameterBounds.Profile)
    (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p)
    (single : packet.val.messages.length = 1) :
    packetQuery ctx Q p packet profile = .initial := by
  apply CausalPrefix.position_injective
  rw [packetQuery_position, single]
  simp [CausalProbability.position,CausalProbability.visibleCoordinates]

theorem packet_singleton (ctx : RawWHIRKeys.Context) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (single : packet.val.messages.length = 1) :
    packet.val.messages = [WHIRHistoryKey.initialPending] := by
  have normal := WHIRHistoryKey.scheduled_normal _ _ packet.property.2.1 packet.property.2.2.1
  have empty : packet.val.messages.dropLast = [] := List.length_eq_zero_iff.mp (by simp [single])
  have restore := normal.restore
  simpa only [empty,List.nil_append] using restore.symm

/-- Public syntax of the actual oldest-first completion, independently of its answers. -/
inductive Chain (ctx : RawWHIRKeys.Context) (Q : Nat) :
    RawWHIRKeys.Packet ctx Q → List (RawWHIRKeys.Packet ctx Q) → Prop where
  | initial (packet) (single : packet.val.messages = [WHIRHistoryKey.initialPending]) :
      Chain ctx Q packet [packet]
  | next {packet previous packets} (head : WHIRHistory.Pending)
      (prior : Chain ctx Q previous packets)
      (messages : packet.val.messages = head :: previous.val.messages)
      (statement : previous.val.statement = packet.val.statement)
      (profile : previous.val.profile = packet.val.profile) :
      Chain ctx Q packet (packets ++ [packet])

theorem completion_chain (ctx : RawWHIRKeys.Context) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) :
    Chain ctx Q packet (completion ctx Q packet) := by
  generalize length : packet.val.messages.length = n
  induction n using Nat.strong_induction_on generalizing packet with
  | h n ih =>
    by_cases empty : packet.val.messages.drop 1 = []
    · have positive := List.length_pos_iff.mpr packet.property.2.1
      have bound := congrArg List.length empty
      simp only [List.length_drop,List.length_nil] at bound
      have one : packet.val.messages.length = 1 := by omega
      rw [completion,RawWHIRKeys.ancestors_singleton ctx Q packet one]
      exact .initial packet (packet_singleton ctx Q packet one)
    · let previous := RawWHIRKeys.dropPacket ctx Q packet 1 empty
      have smaller : previous.val.messages.length < n := by
        simp only [previous,RawWHIRKeys.dropPacket,List.length_drop]
        have positive := List.length_pos_iff.mpr packet.property.2.1
        omega
      have prior := ih previous.val.messages.length smaller previous rfl
      rw [completion,RawWHIRKeys.ancestors_drop_one ctx Q packet empty]
      apply Chain.next (packet.val.messages.headD ⟨[],none⟩) prior
      · cases messages : packet.val.messages with
        | nil => exact False.elim (packet.property.2.1 messages)
        | cons head tail => simp [previous,RawWHIRKeys.dropPacket,messages]
      · rfl
      · rfl

def localEntry (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (p : ParameterBounds.Profile) (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p)
    (raw : GroupAnswer ctx Q (.inl packet)) : WHIRRawReplay.LocalEntry p :=
  (packet.val.messages.headD ⟨[],none⟩,
    ⟨packetQuery ctx Q p packet profile,packetSample ctx stack Q p packet profile raw⟩)

def localHistory (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (p : ParameterBounds.Profile) (history : List (Sigma (GroupAnswer ctx Q))) : List (WHIRRawReplay.LocalEntry p) :=
  (WHIRRawReplay.decodeHistory ctx stack Q history).filterMap (WHIRRawReplay.restrictEntry p)

theorem localEntry_eq (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (p : ParameterBounds.Profile) (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p)
    (raw : GroupAnswer ctx Q (.inl packet)) :
    WHIRRawReplay.restrictEntry p (WHIRRawReplay.packetEntry ctx stack Q packet raw) =
      some (localEntry ctx stack Q p packet profile raw) := by
  cases profile
  simp [WHIRRawReplay.packetEntry,localEntry,packetQuery,packetSample]

theorem localHistory_append (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (p : ParameterBounds.Profile) (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p)
    (raw : GroupAnswer ctx Q (.inl packet)) (history : List (Sigma (GroupAnswer ctx Q))) :
    localHistory ctx stack Q p (history ++ [⟨.inl packet,raw⟩]) =
      localEntry ctx stack Q p packet profile raw :: localHistory ctx stack Q p history := by
  simp [localHistory,WHIRRawReplay.decodeHistory,WHIRRawReplay.decodeEntry,
    List.filterMap_append,List.reverse_append,localEntry_eq ctx stack Q p packet profile raw]

theorem Step.extends {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    (step : Step ctx stack Q p lanes proofs packet profile state raw out) :
    ExtendsRows state out ∧ PreviousCovered out := by
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    obtain ⟨rows,_,_,_⟩ := absorbResponse_rows _ _ _ _ parsed
    obtain ⟨_,_,_,nonceRows,_⟩ := afterNonce_fields _ _ _ boundNonce
    obtain ⟨_,_,_,_,extended,covered⟩ := takeSample_fields _ _ _ _ _ _ _ opened
    constructor
    · obtain ⟨suffix,extended⟩ := extended
      refine ⟨suffix,?_⟩
      dsimp only [withOutput]
      rw [extended,nonceRows,rows]
    · exact covered

theorem Trace.extends {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {state out : WireState p} {history}
    (trace : Trace ctx stack Q p lanes proofs packets state out history) : ExtendsRows state out := by
  induction trace with
  | nil => exact ExtendsRows.refl _
  | cons profile step rest ih => exact ExtendsRows.trans step.extends.1 ih

theorem Trace.append_inv {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    (left right : List (RawWHIRKeys.Packet ctx Q)) {state out : WireState p} {history}
    (trace : Trace ctx stack Q p lanes proofs (left ++ right) state out history) :
    ∃ middle before after, history = before ++ after ∧
      Trace ctx stack Q p lanes proofs left state middle before ∧
      Trace ctx stack Q p lanes proofs right middle out after := by
  induction left generalizing state history with
  | nil => exact ⟨state,[],history,rfl,.nil state,trace⟩
  | cons packet left ih =>
    cases trace with
    | cons profile step rest =>
      obtain ⟨middle,before,after,equal,first,last⟩ := ih rest
      exact ⟨middle,_::before,after,by simp [equal],.cons profile step first,last⟩

def RowTable {p : ParameterBounds.Profile} (state : WireState p) (rows : WHIRPhysicalHistory.Rows) : Prop :=
  ∀ i, i < state.rows.size → rows i = state.rows[i]!

theorem RowTable.of_extends {p : ParameterBounds.Profile} {before after : WireState p}
    {rows : WHIRPhysicalHistory.Rows} (extended : ExtendsRows before after) (table : RowTable after rows) :
    RowTable before rows := by
  intro i bound
  have size : before.rows.size ≤ after.rows.size := by
    obtain ⟨suffix,extended⟩ := extended
    simp [extended]
  rw [table i (by omega),extended.get i bound]

/-- The invariant is a theorem conclusion derived from execution. Every larger physical row table may be used to replay every already consumed response. -/
def Completed {ctx : RawWHIRKeys.Context} (stack : ctx.mode = .stack) {Q : Nat}
    {p : ParameterBounds.Profile} (packet : RawWHIRKeys.Packet ctx Q) (state : WireState p)
    (history : List (Sigma (GroupAnswer ctx Q))) : Prop :=
  ∃ (profile : packet.val.profile = p) (raw : GroupAnswer ctx Q (.inl packet))
    (past : List (WHIRRawReplay.LocalEntry p)) (before : CausalGame.Tape (ParameterBounds.config p))
    (initial : RingPCSGame.Prefix × E),
    localHistory ctx stack Q p history = localEntry ctx stack Q p packet profile raw :: past ∧
    state.previous = some (packetQuery ctx Q p packet profile) ∧
    state.tape = CausalProbability.set (packetQuery ctx Q p packet profile) before
      (StackWHIRReplay.projectSample _ (packetSample ctx stack Q p packet profile raw)) ∧
    state.initial = some initial ∧
    StackWHIRReplay.initialSeed (localHistory ctx stack Q p history) = some initial ∧
    state.replies.size + 1 = packet.val.messages.length ∧
    PreviousCovered state ∧
    ∀ (statement : WHIRFiatShamir.Statement p) (rows : WHIRPhysicalHistory.Rows), RowTable state rows →
      WHIRPhysicalHistory.decodeHistory p (fun _ => some statement) (fun _ _ => #[]) rows
        packet.val.statement packet.val.messages (past.map StackWHIRReplay.projectEntry) =
          some ⟨statement,before,state.replies⟩

theorem recordSample_tape {p : ParameterBounds.Profile} (state : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q) :
    (recordSample state q x).tape =
      CausalProbability.set q state.tape (StackWHIRReplay.projectSample q x) := by
  cases q <;> rfl

theorem recordSample_initial {p : ParameterBounds.Profile} (state : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (first : q = .initial) :
    ∃ seed, (recordSample state q x).initial = some seed ∧
      StackWHIRReplay.seedValue ⟨q,x⟩ = some seed := by
  subst q
  exact ⟨x,rfl,rfl⟩

theorem recordSample_noninitial {p : ParameterBounds.Profile} (state : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (later : q ≠ .initial) : (recordSample state q x).initial = state.initial := by
  cases q <;> simp_all [recordSample]

theorem absorbResponse_some {p : ParameterBounds.Profile} (state out : WireState p)
    (pending : WHIRHistory.Pending) (root : Option Digest32)
    (q : CausalProbability.Coordinate (ParameterBounds.config p))
    (previous : state.previous = some q)
    (ok : absorbResponse state pending = some (out,root)) :
    ∃ response, WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending =
      some response ∧ out.replies = state.replies.push response := by
  simp only [absorbResponse,previous] at ok
  change (WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending).bind _ =
    some (out,root) at ok
  cases parsed : WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending with
  | none => simp [parsed] at ok
  | some response =>
    simp only [parsed,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at ok
    cases ok.1
    exact ⟨response,rfl,rfl⟩

theorem reply_rowTable {p : ParameterBounds.Profile} (state : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (pending : WHIRHistory.Pending)
    (rows : WHIRPhysicalHistory.Rows) (table : RowTable state rows)
    (covered : PreviousCovered state) (previous : state.previous = some q) :
    WHIRPhysicalHistory.reply (fun _ _ => #[]) rows q pending =
      WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending := by
  cases q with
  | query i => simp only [WHIRPhysicalHistory.reply_query,table i (covered i previous)]
  | initial => rfl
  | fold i j => rfl
  | ood i j => rfl
  | tail j => rfl

theorem completed_initial {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)} (root : Digest32)
    (single : packet.val.messages = [WHIRHistoryKey.initialPending])
    (step : Step ctx stack Q p lanes proofs packet profile (initialWireState p root) raw out) :
    Completed stack packet out [⟨.inl packet,raw⟩] := by
  have first := packetQuery_initial ctx Q p packet profile (by simp [single])
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    simp only [single,List.headD_cons,WHIRHistoryKey.initialPending,initialWireState,
      absorbResponse,List.isEmpty_nil,ite_true,Option.some.injEq,Prod.mk.injEq] at parsed
    obtain ⟨rfl,rfl⟩ := parsed
    obtain ⟨nonceTape,noncePrevious,nonceReplies,nonceRows,nonceInitial⟩ :=
      afterNonce_fields _ _ _ boundNonce
    obtain ⟨replies,tape,previous,initial,extended,covered⟩ :=
      takeSample_fields _ _ _ _ _ _ _ opened
    obtain ⟨seed,seedState,seedEntry⟩ := recordSample_initial _ _ _ first
    have history : localHistory ctx stack Q p [⟨.inl packet,raw⟩] =
        [localEntry ctx stack Q p packet profile raw] := by
      simpa [localHistory,WHIRRawReplay.decodeHistory] using
        localHistory_append ctx stack Q p packet profile raw []
    refine ⟨profile,raw,[],WHIRReplay.zeroTape p,seed,history,previous,?_,?_,?_,?_,covered,?_⟩
    · dsimp only [withOutput]
      rw [tape,recordSample_tape,nonceTape]
    · exact initial.trans seedState
    · rw [history]
      exact seedEntry
    · dsimp only [withOutput]
      rw [replies,nonceReplies]
      exact size.symm
    · intro statement rows table
      dsimp only [withOutput]
      rw [replies,nonceReplies,single]
      rfl

theorem completed_next {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet priorPacket : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    {history : List (Sigma (GroupAnswer ctx Q))} (head : WHIRHistory.Pending)
    (messages : packet.val.messages = head :: priorPacket.val.messages)
    (statement : priorPacket.val.statement = packet.val.statement)
    (prior : Completed stack priorPacket state history)
    (step : Step ctx stack Q p lanes proofs packet profile state raw out) :
    Completed stack packet out (history ++ [⟨.inl packet,raw⟩]) := by
  obtain ⟨priorProfile,priorRaw,past,before,seed,priorHistory,priorPrevious,priorTape,
    priorInitial,priorSeed,priorSize,priorCovered,priorDecoded⟩ := prior
  have later : packetQuery ctx Q p packet profile ≠ .initial := by
    intro first
    have position := packetQuery_position ctx Q p packet profile
    rw [first] at position
    have positive := List.length_pos_iff.mpr priorPacket.property.2.1
    simp only [messages,List.length_cons] at position
    simp [CausalProbability.position,CausalProbability.visibleCoordinates] at position
    omega
  have tables := step.extends
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    have headEq : packet.val.messages.headD ⟨[],none⟩ = head := by simp [messages]
    rw [headEq] at parsed shape
    obtain ⟨response,responseParsed,responseReplies⟩ :=
      absorbResponse_some _ _ _ _ _ priorPrevious parsed
    obtain ⟨absorbedRows,absorbedTape,absorbedPrevious,absorbedInitial⟩ :=
      absorbResponse_rows _ _ _ _ parsed
    obtain ⟨nonceTape,noncePrevious,nonceReplies,nonceRows,nonceInitial⟩ :=
      afterNonce_fields _ _ _ boundNonce
    obtain ⟨replies,tape,previous,initial,extended,covered⟩ :=
      takeSample_fields _ _ _ _ _ _ _ opened
    refine ⟨profile,raw,localEntry ctx stack Q p priorPacket priorProfile priorRaw :: past,
      state.tape,seed,?_,previous,?_,?_,?_,?_,covered,?_⟩
    · rw [localHistory_append,priorHistory]
    · dsimp only [withOutput]
      rw [tape,recordSample_tape,nonceTape,absorbedTape]
    · dsimp only [withOutput]
      rw [initial,recordSample_noninitial _ _ _ later,nonceInitial,absorbedInitial,priorInitial]
    · rw [localHistory_append ctx stack Q p packet profile raw history]
      have nonempty : localHistory ctx stack Q p history ≠ [] := by rw [priorHistory]; simp
      simpa only [StackWHIRReplay.initialSeed,List.getLast?_cons_of_ne_nil nonempty] using priorSeed
    · dsimp only [withOutput]
      rw [replies,nonceReplies]
      exact size.symm
    · intro replayStatement rows table
      have priorTable := table.of_extends tables.1
      have parsedBefore := priorDecoded replayStatement rows priorTable
      have responseAtRows := (reply_rowTable state _ head rows priorTable priorCovered priorPrevious).trans responseParsed
      have priorPosition := packetQuery_position ctx Q p priorPacket priorProfile
      have currentPosition := packetQuery_position ctx Q p packet profile
      have priorQuery := packetQuery_eq ctx Q p priorPacket priorProfile packet.val.statement
      have currentQuery := packetQuery_eq ctx Q p packet profile packet.val.statement
      have nonceShape := nonceMatches_shape _ _ shape
      cases priorMessages : priorPacket.val.messages with
      | nil => exact False.elim (priorPacket.property.2.1 priorMessages)
      | cons pending older =>
        rw [messages,priorMessages]
        simp only [localEntry,StackWHIRReplay.projectEntry,List.map_cons,List.headD_cons,priorMessages]
        simp only [messages,priorMessages,List.length_cons,Nat.add_sub_cancel] at priorPosition currentPosition
        rw [messages,priorMessages] at currentQuery
        rw [priorMessages] at priorQuery
        rw [statement,priorMessages] at parsedBefore
        simp only [WHIRPhysicalHistory.decodeHistory,← priorQuery,priorPosition,← currentQuery,
          currentPosition,nonceShape,ite_true,parsedBefore,
          WHIRPhysicalHistory.step,responseAtRows,Option.map_some]
        dsimp only [withOutput]
        rw [replies,nonceReplies,responseReplies,priorTape]
        rfl

theorem trace_completed {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    {out : WireState p} {history : List (Sigma (GroupAnswer ctx Q))} (root : Digest32)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history) :
    Completed stack packet out history := by
  induction chain generalizing out history with
  | initial packet single =>
    cases trace with
    | cons profile step rest =>
      cases rest
      exact completed_initial root single step
  | next head prior messages statement profile ih =>
    obtain ⟨middle,before,after,hist,first,last⟩ := Trace.append_inv _ _ trace
    cases last with
    | cons finalProfile step rest =>
      cases rest
      subst history
      exact completed_next head messages statement (ih first) step

theorem initialSeed_cons_noninitial {c : Config} (q : CausalProbability.Coordinate c)
    (x : StackWHIRReplay.Sample q) (pending : WHIRHistory.Pending)
    (past : List (WHIRHistory.Pending × Sigma (@StackWHIRReplay.Sample c))) (later : q ≠ .initial) :
    StackWHIRReplay.initialSeed ((pending,⟨q,x⟩)::past) = StackWHIRReplay.initialSeed past := by
  cases past with
  | nil => cases q <;> simp_all [StackWHIRReplay.initialSeed,StackWHIRReplay.seedValue]
  | cons entry past =>
    unfold StackWHIRReplay.initialSeed
    rw [List.getLast?_cons_of_ne_nil (show entry::past ≠ [] from by simp)]

/-- Actual completed physical rows, not an ideal-row agreement assumption, make the stack decoder succeed. The nonempty reply condition is derived separately from the native verifier's opening acceptance. -/
theorem Completed.decodeStack {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) (state : WireState packet.val.profile)
    (history : List (Sigma (GroupAnswer ctx Q)))
    (catalog : StackWHIRReplay.Catalog packet.val.profile cap)
    (original : WHIRFiatShamir.StackInitial packet.val.profile cap)
    (found : catalog packet.val.statement = some original)
    (complete : Completed stack packet state history) (nonempty : state.replies ≠ #[]) :
    ∃ head past, ∃ (x : StackWHIRReplay.Sample (WHIRReplay.query packet.val.profile
      (packet.val.statement,packet.val.messages))) (replay : StackWHIRReplay.Replay packet.val.profile cap),
      localHistory ctx stack Q packet.val.profile history =
        (head,⟨WHIRReplay.query packet.val.profile (packet.val.statement,packet.val.messages),x⟩)::past ∧
      WHIRPhysicalHistory.decodeStack packet.val.profile cap catalog (fun _ _ => #[])
        (fun i => state.rows[i]!) ⟨packet.val.statement,packet.val.messages,past⟩ = some replay ∧
      replay.original = original ∧ state.initial = some replay.initial ∧
      replay.whir.statement = StackWHIRReplay.transformedStatement original replay.initial.1 ∧
      (StackWHIRReplay.finish ⟨packet.val.statement,packet.val.messages,past⟩ replay x).whir.tape = state.tape ∧
      (StackWHIRReplay.finish ⟨packet.val.statement,packet.val.messages,past⟩ replay x).whir.replies = state.replies := by
  obtain ⟨profile,raw,past,before,seed,historyEq,previous,tape,initial,initialSeed,size,covered,decoded⟩ := complete
  have positive : 0 < state.replies.size := by
    by_contra notPositive
    have empty : state.replies.toList = [] := List.length_eq_zero_iff.mp (by
      change state.replies.size = 0
      omega)
    apply nonempty
    simpa using congrArg List.toArray empty
  have later : packetQuery ctx Q packet.val.profile packet profile ≠ .initial := by
    intro first
    have position := packetQuery_position ctx Q packet.val.profile packet profile
    rw [first] at position
    simp [CausalProbability.position,CausalProbability.visibleCoordinates] at position
    omega
  rw [historyEq] at initialSeed
  have pastSeed : StackWHIRReplay.initialSeed past = some seed :=
    (initialSeed_cons_noninitial _ _ _ _ later).symm.trans initialSeed
  let replay : StackWHIRReplay.Replay packet.val.profile cap :=
    ⟨original,seed,⟨StackWHIRReplay.transformedStatement original seed.1,before,state.replies⟩⟩
  refine ⟨packet.val.messages.headD ⟨[],none⟩,past,
    packetSample ctx stack Q packet.val.profile packet profile raw,replay,historyEq,?_,rfl,initial,rfl,?_,rfl⟩
  · have parsed := decoded (StackWHIRReplay.transformedStatement original seed.1)
      (fun i => state.rows[i]!) (fun _ _ => rfl)
    simp only [WHIRPhysicalHistory.decodeStack,found,pastSeed,
      WHIRPhysicalHistory.decode,StackWHIRReplay.projectKey]
    change (WHIRPhysicalHistory.decodeHistory packet.val.profile
      (fun _ => some (StackWHIRReplay.transformedStatement original seed.1)) (fun _ _ => #[])
      (fun i => state.rows[i]!) packet.val.statement packet.val.messages
      (past.map StackWHIRReplay.projectEntry)).bind _ = some replay
    rw [parsed]
    rfl
  · exact tape.symm

/-- The actual source reader produces the replay invariant for its canonical packet completion. No future oracle table occurs in this statement or its proof. -/
theorem readPhysicalCompletion_completed {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (root : Digest32)
    (next : WireState packet.val.profile → List (Sigma (GroupAnswer ctx Q)) → WHIRSourceChronology.Source cap (Option R))
    (observations : List Observation) (result : R)
    (run : Runs (WHIRSourceChronology.erase
      (readPhysicalPackets ctx stack Q packet.val.profile lanes proofs none (completion ctx Q packet)
        (completion_profiles ctx Q packet) (initialWireState packet.val.profile root) next)) observations (some result)) :
    ∃ state history suffix, Completed stack packet state history ∧
      Runs (WHIRSourceChronology.erase (next state history)) suffix (some result) := by
  obtain ⟨state,history,suffix,trace,last⟩ :=
    readPhysicalPackets_trace ctx stack Q packet.val.profile lanes proofs _ _ _ next observations result run
  exact ⟨state,history,suffix,trace_completed root (completion_chain ctx Q packet) trace,last⟩

end Whir.WHIRPhysicalReplay
