import Whir.WHIRPhysicalReplay
import Whir.WHIRNativeRestoration
import Whir.WHIRQueryOracleRecurrence

/-! Actual physical traces determine the immutable digest log, query payload slots, and sampled query coordinates. Canonical scalar decoding connects that log to the proof-only commitment replay, deriving stack row agreement from per-opening Merkle binding without replacing source rows or assuming a root-position association. -/

namespace Whir.WHIRPhysicalRoots
open Concrete Protocol FiatShamirGame DuplexModeGame PublicMerkleProgram MerkleTransport
open RawOracleCoupling RawOracleCoupling.Concrete WHIRPhysicalVerifier WHIRPhysicalReplay

/-- The root carried in this physical response, interpreted at its preceding canonical coordinate. -/
def packetRoot {ctx : RawWHIRKeys.Context} {Q : Nat} (packet : RawWHIRKeys.Packet ctx Q) : Option Digest32 :=
  absorbedRoot (WHIRReplay.query packet.val.profile (packet.val.statement,packet.val.messages.tail))
    (packet.val.messages.headD ⟨[],none⟩).scalars

private theorem afterNonce_roots {p : ParameterBounds.Profile} {ctx : RawWHIRKeys.Context} {Q : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} (state out : WireState p)
    (nonce : WHIRPowProgram.Outcome ctx Q packet) (ok : afterNonce state nonce = some out) :
    out.roots = state.roots ∧ out.openings = state.openings := by
  unfold afterNonce at ok
  split at ok
  · cases Option.some.inj ok
    exact ⟨rfl,rfl⟩
  · cases cached : state.outputCache with
    | none => simp [cached] at ok
    | some digest =>
      simp only [cached,Option.map_some,Option.some.injEq] at ok
      subst out
      exact ⟨rfl,rfl⟩

theorem takeSample_roots {p : ParameterBounds.Profile} (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (state out : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (trace : List Observation) (run : Runs (takeSample lanes proofs state q x) trace (some out)) :
    out.roots = state.roots ∧ ∀ opened ∈ state.openings, opened ∈ out.openings := by
  cases q with
  | query i =>
    simp only [takeSample] at run
    split at run
    · cases hp : proofs[i.val]? <;> cases hr : state.roots[i.val]?
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run
        obtain ⟨before,opened,after,_,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases opened with
        | none => cases continued
        | some opened =>
          cases continued
          exact ⟨rfl,fun _ h => List.mem_cons_of_mem _ h⟩
    · cases run
  | initial => cases run; exact ⟨rfl,fun _ h => h⟩
  | fold i j => cases run; exact ⟨rfl,fun _ h => h⟩
  | ood i j => cases run; exact ⟨rfl,fun _ h => h⟩
  | tail j => cases run; exact ⟨rfl,fun _ h => h⟩

theorem absorbResponse_roots {p : ParameterBounds.Profile} (state out : WireState p)
    (pending : WHIRHistory.Pending) (root : Option Digest32)
    (ok : absorbResponse state pending = some (out,root)) :
    out.roots = state.roots ++ root.toArray ∧ out.openings = state.openings ∧
      root = state.previous.bind (fun q => absorbedRoot q pending.scalars) := by
  unfold absorbResponse at ok
  cases previous : state.previous with
  | none =>
    simp only [previous] at ok
    split at ok
    · cases Option.some.inj ok
      simp
    · contradiction
  | some q =>
    simp only [previous] at ok
    change (WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending).bind _ =
      some (out,root) at ok
    cases parsed : WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending with
    | none => simp [parsed] at ok
    | some response =>
      simp only [parsed,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at ok
      obtain ⟨rfl,rfl⟩ := ok
      cases hroot : absorbedRoot q pending.scalars <;> simp [hroot]

theorem Step.roots {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    (step : Step ctx stack Q p lanes proofs packet profile state raw out) :
    out.roots = state.roots ++
      (state.previous.bind (fun q => absorbedRoot q (packet.val.messages.headD ⟨[],none⟩).scalars)).toArray ∧
      ∀ opened ∈ state.openings, opened ∈ out.openings := by
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    obtain ⟨roots,openings,root⟩ := absorbResponse_roots _ _ _ _ parsed
    obtain ⟨nonceRoots,nonceOpenings⟩ := afterNonce_roots _ _ _ boundNonce
    obtain ⟨sampleRoots,sampleOpenings⟩ := takeSample_roots _ _ _ _ _ _ _ opened
    constructor
    · dsimp only [withOutput]
      rw [sampleRoots,nonceRoots,roots,root]
    · intro opening member
      apply sampleOpenings
      rwa [nonceOpenings,openings]

theorem packetRoot_next {ctx : RawWHIRKeys.Context} {Q : Nat} {p : ParameterBounds.Profile}
    (packet prior : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p)
    (priorProfile : prior.val.profile = p) (head : WHIRHistory.Pending)
    (messages : packet.val.messages = head :: prior.val.messages)
    (_statement : prior.val.statement = packet.val.statement) :
    packetRoot packet = absorbedRoot (packetQuery ctx Q p prior priorProfile) head.scalars := by
  rw [packetQuery_eq ctx Q p prior priorProfile packet.val.statement]
  cases profile
  simp only [packetRoot,messages,List.tail_cons,List.headD_cons]

theorem absorbedRoot_empty {c : Config} (q : CausalProbability.Coordinate c) :
    absorbedRoot q [] = none := by
  cases q <;> simp [absorbedRoot]

/-- A completed canonical source trace has exactly its transmitted final-fold roots, in arrival order. -/
theorem trace_roots {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    {out : WireState p} {history : List (Sigma (GroupAnswer ctx Q))} (root : Digest32)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history) :
    out.roots = #[root] ++ (packets.filterMap packetRoot).toArray := by
  induction chain generalizing out history with
  | initial packet single =>
    cases trace with
    | cons profile step rest =>
      cases rest
      rw [(Step.roots step).1]
      simp [initialWireState,packetRoot,single,WHIRHistoryKey.initialPending,absorbedRoot_empty]
  | @next packet previousPacket packets head prior messages statement profile ih =>
    obtain ⟨middle,before,after,hist,first,last⟩ := Trace.append_inv _ _ trace
    cases last with
    | cons finalProfile step rest =>
      cases rest
      obtain ⟨priorProfile,priorRaw,past,tape,seed,priorHistory,previous,rest⟩ :=
        trace_completed root prior first
      rw [(Step.roots step).1,previous,Option.bind_some,
        show (packet.val.messages.headD ⟨[],none⟩).scalars = head.scalars by simp [messages],
        ← packetRoot_next packet _ finalProfile priorProfile head messages statement,ih first]
      cases found : packetRoot packet <;> simp [List.filterMap_append,found]

/-- Every retained opening names the actual root and actual row-array slot used by the physical source. -/
def RootedOpenings {p : ParameterBounds.Profile} (state : WireState p) : Prop :=
  ∀ opened ∈ state.openings,
    state.roots[opened.level.val]? = some opened.root ∧
    state.rows[opened.level.val]? = some opened.result.rows

private theorem append_preserves {α : Type} (a b : Array α) (i : Nat) (v : α)
    (found : a[i]? = some v) : (a ++ b)[i]? = some v := by
  obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
  apply Array.getElem?_eq_some_iff.mpr
  refine ⟨by simp; omega,?_⟩
  rw [Array.getElem_append_left bound]
  exact equal

theorem takeSample_rooted {p : ParameterBounds.Profile} (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (state out : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (trace : List Observation) (run : Runs (takeSample lanes proofs state q x) trace (some out))
    (rooted : RootedOpenings state) : RootedOpenings out := by
  cases q with
  | query i =>
    simp only [takeSample] at run
    split at run
    · rename_i index
      cases hp : proofs[i.val]? <;> cases hr : state.roots[i.val]?
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run
        obtain ⟨before,opened,after,_,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases opened with
        | none => cases continued
        | some opened =>
          cases continued
          intro old member
          rcases List.mem_cons.mp member with same | member
          · subst old
            exact ⟨hr,by simp [index]⟩
          · obtain ⟨root,row⟩ := rooted old member
            refine ⟨root,?_⟩
            exact append_preserves state.rows #[opened.rows] old.level.val old.result.rows row
    · cases run
  | initial => cases run; exact rooted
  | fold i j => cases run; exact rooted
  | ood i j => cases run; exact rooted
  | tail j => cases run; exact rooted

theorem Step.rooted {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    (step : Step ctx stack Q p lanes proofs packet profile state raw out)
    (rooted : RootedOpenings state) : RootedOpenings out := by
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    obtain ⟨roots,openings,_⟩ := absorbResponse_roots _ _ _ _ parsed
    obtain ⟨rows,_,_,_⟩ := absorbResponse_rows _ _ _ _ parsed
    obtain ⟨nonceRoots,nonceOpenings⟩ := afterNonce_roots _ _ _ boundNonce
    obtain ⟨_,_,_,nonceRows,_⟩ := afterNonce_fields _ _ _ boundNonce
    apply takeSample_rooted _ _ _ _ _ _ _ opened
    intro opening member
    rw [nonceOpenings,openings] at member
    obtain ⟨root,row⟩ := rooted opening member
    constructor
    · rw [nonceRoots,roots]
      exact append_preserves _ _ _ _ root
    · rwa [nonceRows,rows]

theorem Trace.rooted {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {state out : WireState p} {history}
    (trace : Trace ctx stack Q p lanes proofs packets state out history)
    (rooted : RootedOpenings state) : RootedOpenings out := by
  induction trace with
  | nil => exact rooted
  | cons profile step rest ih => exact ih (Step.rooted step rooted)

theorem trace_rooted {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {out : WireState p} {history}
    (root : Digest32)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history) :
    RootedOpenings out :=
  Trace.rooted trace (by simp [RootedOpenings,initialWireState])

/-- Retained query answers are exactly the coordinates in the current tape, all strictly before the next allocation position. -/
def OpeningSamples {p : ParameterBounds.Profile} (bound : Nat) (state : WireState p) : Prop :=
  ∀ opened ∈ state.openings,
    CausalProbability.position (.query opened.level) < bound ∧
    CausalProbability.get (.query opened.level) state.tape = opened.sample

private theorem sampled_old {p : ParameterBounds.Profile} (state : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (samples : OpeningSamples (CausalProbability.position q) state) (opened : QueryOpening p)
    (member : opened ∈ state.openings) :
    CausalProbability.position (.query opened.level) < CausalProbability.position q + 1 ∧
    CausalProbability.get (.query opened.level) (recordSample state q x).tape = opened.sample := by
  obtain ⟨bound,sample⟩ := samples opened member
  constructor
  · omega
  · rw [recordSample_tape,CausalProbability.get_set_ne]
    · exact sample
    · intro same
      have := congrArg CausalProbability.position same
      omega

theorem takeSample_samples {p : ParameterBounds.Profile} (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (state out : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (trace : List Observation) (run : Runs (takeSample lanes proofs state q x) trace (some out))
    (samples : OpeningSamples (CausalProbability.position q) state) :
    OpeningSamples (CausalProbability.position q + 1) out := by
  cases q with
  | query i =>
    simp only [takeSample] at run
    split at run
    · cases hp : proofs[i.val]? <;> cases hr : state.roots[i.val]?
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run
        obtain ⟨before,opened,after,_,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases opened with
        | none => cases continued
        | some opened =>
          cases continued
          intro old member
          rcases List.mem_cons.mp member with same | member
          · subst old
            constructor
            · exact Nat.lt_succ_self _
            · exact CausalProbability.get_set _ _ _
          · exact sampled_old state (.query i) x samples old member
    · cases run
  | initial => cases run; exact sampled_old state .initial x samples
  | fold i j => cases run; exact sampled_old state (.fold i j) x samples
  | ood i j => cases run; exact sampled_old state (.ood i j) x samples
  | tail j => cases run; exact sampled_old state (.tail j) x samples

theorem Step.samples {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    (step : Step ctx stack Q p lanes proofs packet profile state raw out)
    (samples : OpeningSamples (CausalProbability.position (packetQuery ctx Q p packet profile)) state) :
    OpeningSamples (CausalProbability.position (packetQuery ctx Q p packet profile) + 1) out := by
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    obtain ⟨_,openings,_⟩ := absorbResponse_roots _ _ _ _ parsed
    obtain ⟨_,tape,_,_⟩ := absorbResponse_rows _ _ _ _ parsed
    obtain ⟨_,nonceOpenings⟩ := afterNonce_roots _ _ _ boundNonce
    obtain ⟨nonceTape,_,_,_,_⟩ := afterNonce_fields _ _ _ boundNonce
    apply takeSample_samples _ _ _ _ _ _ _ opened
    intro opening member
    rw [nonceOpenings,openings] at member
    simpa only [nonceTape,tape] using samples opening member

theorem trace_samples {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    {out : WireState p} {history : List (Sigma (GroupAnswer ctx Q))} (root : Digest32)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history) :
    OpeningSamples packet.val.messages.length out := by
  induction chain generalizing out history with
  | initial packet single =>
    cases trace with
    | cons profile step rest =>
      cases rest
      have h := Step.samples step (by simp [OpeningSamples,initialWireState])
      rwa [packetQuery_position,show packet.val.messages.length - 1 + 1 = packet.val.messages.length by
        have := List.length_pos_iff.mpr packet.property.2.1; omega] at h
  | @next packet previousPacket packets head prior messages statement profile ih =>
    obtain ⟨middle,before,after,hist,first,last⟩ := Trace.append_inv _ _ trace
    cases last with
    | cons finalProfile step rest =>
      cases rest
      have samples := ih first
      have qpos := packetQuery_position ctx Q p packet finalProfile
      rw [messages,List.length_cons,Nat.add_sub_cancel] at qpos
      have h := Step.samples step (by rwa [qpos])
      simpa only [qpos,messages,List.length_cons] using h

def RecordedQuery {p : ParameterBounds.Profile} (state : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q) : Prop :=
  match q,x with
  | .query i,x => ∃ opened ∈ state.openings, opened.level = i ∧ HEq opened.sample x
  | _,_ => True

theorem takeSample_recorded {p : ParameterBounds.Profile} (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (state out : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (trace : List Observation) (run : Runs (takeSample lanes proofs state q x) trace (some out)) :
    RecordedQuery out q x := by
  cases q with
  | query i =>
    simp only [takeSample] at run
    split at run
    · cases hp : proofs[i.val]? <;> cases hr : state.roots[i.val]?
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run; cases run
      · simp only [hp,hr] at run
        obtain ⟨before,opened,after,_,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases opened with
        | none => cases continued
        | some opened =>
          cases continued
          exact ⟨_,List.mem_cons_self, rfl, HEq.rfl⟩
    · cases run
  | initial => trivial
  | fold i j => trivial
  | ood i j => trivial
  | tail j => trivial

theorem Trace.openings_mono {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {state out : WireState p} {history}
    (trace : Trace ctx stack Q p lanes proofs packets state out history) :
    ∀ opened ∈ state.openings, opened ∈ out.openings := by
  induction trace with
  | nil => exact fun _ h => h
  | cons profile step rest ih => exact fun opened h => ih opened ((Step.roots step).2 opened h)

theorem Step.recorded {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    (step : Step ctx stack Q p lanes proofs packet profile state raw out) :
    RecordedQuery out (packetQuery ctx Q p packet profile) (packetSample ctx stack Q p packet profile raw) := by
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    simpa only [RecordedQuery,withOutput] using takeSample_recorded _ _ _ _ _ _ _ opened

theorem RecordedQuery.mono {p : ParameterBounds.Profile} {state out : WireState p}
    {q : CausalProbability.Coordinate (ParameterBounds.config p)} {x : StackWHIRReplay.Sample q}
    (recorded : RecordedQuery state q x)
    (mono : ∀ opened ∈ state.openings, opened ∈ out.openings) : RecordedQuery out q x := by
  cases q with
  | query i =>
    obtain ⟨opened,member,level,sample⟩ := recorded
    exact ⟨opened,mono opened member,level,sample⟩
  | initial => trivial
  | fold i j => trivial
  | ood i j => trivial
  | tail j => trivial

theorem localHistory_cons (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (p : ParameterBounds.Profile) (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p)
    (raw : GroupAnswer ctx Q (.inl packet)) (history : List (Sigma (GroupAnswer ctx Q))) :
    localHistory ctx stack Q p (⟨.inl packet,raw⟩::history) =
      localHistory ctx stack Q p history ++ [localEntry ctx stack Q p packet profile raw] := by
  simp [localHistory,WHIRRawReplay.decodeHistory,WHIRRawReplay.decodeEntry,
    List.filterMap_append,localEntry_eq ctx stack Q p packet profile raw]

theorem trace_recorded {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {state out : WireState p} {history}
    (trace : Trace ctx stack Q p lanes proofs packets state out history) :
    ∀ entry ∈ localHistory ctx stack Q p history, RecordedQuery out entry.2.1 entry.2.2 := by
  induction trace with
  | nil => simp [localHistory,WHIRRawReplay.decodeHistory]
  | @cons packet packets state next final raw history profile step rest ih =>
    rw [localHistory_cons ctx stack Q p packet profile raw]
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact ih entry member
    · have equal := List.mem_singleton.mp member
      subst entry
      exact (Step.recorded step).mono (Trace.openings_mono rest)

/-- Per-opening binding obtained from the counted Merkle program, retaining its actual payload. -/
def BoundRows {p : ParameterBounds.Profile} (base : CausalGame.BaseOracle)
    (roots : WHIRReplay.Roots) (state : WireState p) : Prop :=
  ∀ opened ∈ state.openings, opened.result.rows =
    atQueries (if opened.level.val = 0 then CausalGame.liftRoot base else roots opened.root opened.level.val)
      (queryIndices p opened.level opened.sample)

theorem trace_query_rows {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {out : WireState p} {history}
    (root : Digest32) (base : CausalGame.BaseOracle) (roots : WHIRReplay.Roots)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history)
    (bound : BoundRows base roots out) (pending : WHIRHistory.Pending)
    (i : Fin (ParameterBounds.config p).folds.size) (x : CausalProbability.Sample (.query i))
    (member : (pending,⟨.query i,x⟩) ∈ localHistory ctx stack Q p history) :
    out.rows[i.val]! =
      atQueries (if i.val = 0 then CausalGame.liftRoot base else roots out.roots[i.val]! i.val)
        (queryIndices p i x) := by
  obtain ⟨opened,openedMember,level,sample⟩ := trace_recorded trace _ member
  obtain ⟨rootFound,rowFound⟩ := trace_rooted root trace opened openedMember
  have binding := bound opened openedMember
  cases opened with
  | mk level' digest sample' result =>
    dsimp only at level sample rootFound rowFound binding
    subst level'
    have sampleEq := eq_of_heq sample
    subst sample'
    obtain ⟨rootBound,rootValue⟩ := Array.getElem?_eq_some_iff.mp rootFound
    obtain ⟨rowBound,rowValue⟩ := Array.getElem?_eq_some_iff.mp rowFound
    rw [getElem!_pos out.rows i.val rowBound,rowValue,
      getElem!_pos out.roots i.val rootBound,rootValue]
    exact binding

theorem Trace.roots_prefix {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packets : List (RawWHIRKeys.Packet ctx Q)} {state out : WireState p} {history}
    (trace : Trace ctx stack Q p lanes proofs packets state out history) :
    ∃ suffix, out.roots = state.roots ++ suffix := by
  induction trace with
  | nil => exact ⟨#[],by simp⟩
  | cons profile step rest ih =>
    obtain ⟨suffix,equal⟩ := ih
    rw [equal,(Step.roots step).1,Array.append_assoc]
    exact ⟨_,rfl⟩

theorem trace_query_sample {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    {out : WireState p} {history} (root : Digest32) (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history)
    (pending : WHIRHistory.Pending) (i : Fin (ParameterBounds.config p).folds.size)
    (x : CausalProbability.Sample (.query i))
    (member : (pending,⟨.query i,x⟩) ∈ localHistory ctx stack Q p history) :
    CausalProbability.get (.query i) out.tape = x := by
  obtain ⟨opened,openedMember,level,sample⟩ := trace_recorded trace _ member
  have value := (trace_samples root chain trace opened openedMember).2
  cases opened with
  | mk level' digest sample' result =>
    dsimp only at level sample value
    subst level'
    exact value.trans (eq_of_heq sample)

theorem projectEntry_query_mem {p : ParameterBounds.Profile}
    (past : List (WHIRRawReplay.LocalEntry p)) (pending : WHIRHistory.Pending)
    (i : Fin (ParameterBounds.config p).folds.size) (x : CausalProbability.Sample (.query i))
    (member : (pending,⟨.query i,x⟩) ∈ past.map StackWHIRReplay.projectEntry) :
    (pending,⟨.query i,x⟩) ∈ past := by
  obtain ⟨⟨pending',⟨q,y⟩⟩,inPast,equal⟩ := List.mem_map.mp member
  cases q <;> simp_all [StackWHIRReplay.projectEntry,StackWHIRReplay.projectSample]
  rcases equal with ⟨_,rfl,heq⟩
  have same := eq_of_heq heq
  subst y
  exact inPast

theorem restored_rootShapes (c : Config) (proof : Opening) (lookup : Nat → Oracle)
    (shapes : ∀ i, i < c.folds.size → i + 1 < c.folds.size →
      oracleValid (lookup (i+1)) (2^(CausalGame.remaining c i-c.folds[i+1]!+c.rates[i+1]!))
        (2^c.folds[i+1]!) = true) :
    WHIRNativeArithmetic.RootShapes c (WHIRNativeErasure.restoreOracles proof lookup) := by
  intro i hi nextLevel next found
  by_cases bound : i < proof.levels.size
  · have slot : (WHIRNativeErasure.restoreOracles proof lookup).levels[i]! =
        {proof.levels[i] with nextOracle := proof.levels[i].nextOracle.map fun _ => lookup (i+1)} := by
      simp [WHIRNativeErasure.restoreOracles,getElem!_pos,bound]
    rw [slot] at found
    cases present : proof.levels[i].nextOracle with
    | none => simp [present] at found
    | some oracle =>
      simp only [present,Option.map_some,Option.some.injEq] at found
      rw [← found]
      exact shapes i hi nextLevel
  · have absent : ¬ i < (WHIRNativeErasure.restoreOracles proof lookup).levels.size := by
      simpa [WHIRNativeErasure.restoreOracles] using bound
    rw [getElem!_neg (WHIRNativeErasure.restoreOracles proof lookup).levels i absent] at found
    cases found

theorem decodeHistory_statement (p : ParameterBounds.Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List WHIRHistory.Pending)
    (ancestors : List (WHIRHistory.Pending × Sigma (@CausalProbability.Sample (ParameterBounds.config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors = some out) :
    catalog s = some out.statement := by
  induction messages generalizing ancestors out with
  | nil => cases parsed
  | cons m messages ih =>
    cases messages with
    | nil =>
      cases ancestors with
      | cons a ancestors => cases parsed
      | nil =>
        simp only [WHIRPhysicalHistory.decodeHistory] at parsed
        split at parsed
        · cases found : catalog s with
          | none => simp [found] at parsed
          | some statement =>
            simp [found] at parsed
            subst out
            rfl
        · cases parsed
    | cons previous older =>
      cases ancestors with
      | nil => cases parsed
      | cons a past =>
        rcases a with ⟨previous',q,x⟩
        simp only [WHIRPhysicalHistory.decodeHistory] at parsed
        split at parsed
        · split at parsed
          · split at parsed
            · split at parsed
              · split at parsed
                · cases prior : WHIRPhysicalHistory.decodeHistory p catalog roots rows s
                      (previous :: older) past with
                  | none => simp [prior] at parsed
                  | some before =>
                    simp only [prior,WHIRPhysicalHistory.step] at parsed
                    obtain ⟨response,decoded,rfl⟩ := Option.map_eq_some_iff.mp parsed
                    exact ih past before prior
                · cases parsed
              · cases parsed
            · cases parsed
          · cases parsed
        · cases parsed

theorem decodeHistory_ancestor_query (p : ParameterBounds.Profile) (catalog : WHIRReplay.Catalog p)
    (roots : WHIRReplay.Roots) (rows : WHIRPhysicalHistory.Rows) (s : Digest32)
    (messages : List WHIRHistory.Pending)
    (ancestors : List (WHIRHistory.Pending × Sigma (@CausalProbability.Sample (ParameterBounds.config p))))
    (out : WHIRReplay.Replay p)
    (parsed : WHIRPhysicalHistory.decodeHistory p catalog roots rows s messages ancestors = some out)
    (k : Nat) (q : CausalProbability.Coordinate (ParameterBounds.config p))
    (atQuery : (ancestors[k]?).map (fun e => e.2.1) = some q) :
    q = WHIRReplay.query p (s,messages.drop (k+1)) := by
  induction messages generalizing ancestors out k with
  | nil => cases parsed
  | cons m messages ih =>
    cases messages with
    | nil =>
      cases ancestors with
      | cons a ancestors => cases parsed
      | nil => simp at atQuery
    | cons previous older =>
      cases ancestors with
      | nil => cases parsed
      | cons a past =>
        rcases a with ⟨previous',current,x⟩
        simp only [WHIRPhysicalHistory.decodeHistory] at parsed
        split at parsed
        · split at parsed
          · rename_i phase
            split at parsed
            · split at parsed
              · split at parsed
                · cases prior : WHIRPhysicalHistory.decodeHistory p catalog roots rows s
                      (previous :: older) past with
                  | none => simp [prior] at parsed
                  | some before =>
                    cases k with
                    | zero =>
                      simp only [List.getElem?_cons_zero,Option.map_some,Option.some.injEq] at atQuery
                      subst q
                      simpa using phase
                    | succ k =>
                      have h := ih past before prior k (by simpa using atQuery)
                      simpa only [List.drop_succ_cons] using h
                · cases parsed
              · cases parsed
            · cases parsed
          · cases parsed
        · cases parsed

theorem chain_rootLog {ctx : RawWHIRKeys.Context} {Q : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    (chain : Chain ctx Q packet packets) :
    packets.filterMap packetRoot =
      WHIRQueryOracleRecurrence.rootLog packet.val.profile packet.val.statement packet.val.messages := by
  induction chain with
  | initial packet single =>
    simp [packetRoot,single,WHIRHistoryKey.initialPending,absorbedRoot_empty,
      WHIRQueryOracleRecurrence.rootLog,WHIRQueryOracleRecurrence.digestSlots]
  | @next packet previous packets head prior messages statement profile ih =>
    rw [List.filterMap_append,ih,profile,statement,messages]
    cases before : previous.val.messages with
    | nil => exact False.elim (previous.property.2.1 before)
    | cons pending older =>
      rw [WHIRQueryOracleRecurrence.rootLog_cons]
      simp only [List.filterMap_cons,List.filterMap_nil,packetRoot,messages,before,
        List.headD_cons,List.tail_cons]
      cases absorbedRoot (WHIRReplay.query packet.val.profile
        (packet.val.statement,pending::older)) head.scalars <;> rfl

theorem trace_roots_log {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    {out : WireState p} {history} (root : Digest32) (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history) :
    out.roots = #[root] ++
      (WHIRQueryOracleRecurrence.rootLog packet.val.profile packet.val.statement packet.val.messages).toArray := by
  rw [trace_roots root chain trace,chain_rootLog chain]

theorem rootLog_drop_prefix (p : ParameterBounds.Profile) (s : Digest32)
    (messages : List WHIRHistory.Pending) (k : Nat) :
    ∃ suffix, WHIRQueryOracleRecurrence.rootLog p s messages =
      WHIRQueryOracleRecurrence.rootLog p s (messages.drop k) ++ suffix := by
  induction k generalizing messages with
  | zero => exact ⟨[],by simp⟩
  | succ k ih =>
    cases messages with
    | nil => exact ⟨[],by simp⟩
    | cons m messages =>
      cases messages with
      | nil =>
        exact ⟨[],by simp [WHIRQueryOracleRecurrence.rootLog,WHIRQueryOracleRecurrence.digestSlots]⟩
      | cons previous older =>
        obtain ⟨suffix,equal⟩ := ih (previous::older)
        rw [WHIRQueryOracleRecurrence.rootLog_cons,equal,List.drop_succ_cons,List.append_assoc]
        exact ⟨_,rfl⟩

theorem rootLog_drop_get (p : ParameterBounds.Profile) (s : Digest32)
    (messages : List WHIRHistory.Pending) (k j : Nat) (digest : Digest32)
    (found : (WHIRQueryOracleRecurrence.rootLog p s (messages.drop k))[j]? = some digest) :
    (WHIRQueryOracleRecurrence.rootLog p s messages)[j]? = some digest := by
  obtain ⟨suffix,equal⟩ := rootLog_drop_prefix p s messages k
  obtain ⟨bound,value⟩ := List.getElem?_eq_some_iff.mp found
  rw [equal,List.getElem?_append_left bound]
  exact found

theorem trace_digest_from_prefix {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    {out : WireState p} {history} (root : Digest32) (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p lanes proofs packets (initialWireState p root) out history)
    (k j : Nat) (digest : Digest32)
    (found : (WHIRQueryOracleRecurrence.rootLog packet.val.profile packet.val.statement
      (packet.val.messages.drop k))[j]? = some digest) :
    out.roots[j+1]? = some digest := by
  have full := rootLog_drop_get _ _ _ k j digest found
  rw [trace_roots_log root chain trace]
  simpa using full

/-- The complete physical trace discharges row agreement from actual per-opening Merkle binding. No ideal rows are supplied to the physical decoder. -/
theorem trace_rowsAgree {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) {packets : List (RawWHIRKeys.Packet ctx Q)}
    {lanes : Nat} {proofs : Array PrunedMerklePaths} {out : WireState packet.val.profile} {history}
    (root : Digest32) (statement : WHIRFiatShamir.Statement packet.val.profile) (roots : WHIRReplay.Roots)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q packet.val.profile lanes proofs packets
      (initialWireState packet.val.profile root) out history)
    (bound : BoundRows statement.root roots out) :
    WHIRPhysicalHistory.RowsAgree packet.val.profile (fun _ => some statement) roots
      (fun i => out.rows[i]!) packet.val.statement packet.val.messages
      ((localHistory ctx stack Q packet.val.profile history).tail.map StackWHIRReplay.projectEntry) := by
  obtain ⟨profile,raw,past,before,seed,historyEq,previous,tape,initial,initialSeed,size,covered,decoded⟩ :=
    trace_completed root chain trace
  have zeroParsed := decoded statement (fun i => out.rows[i]!) (fun _ _ => rfl)
  have pastEq : (localHistory ctx stack Q packet.val.profile history).tail = past := by
    rw [historyEq]
    rfl
  intro k pending i x replay atQuery parsed
  change out.rows[i.val]! = WHIRReplay.queryRows replay i x
  have inProjected : (pending,⟨.query i,x⟩) ∈
      (localHistory ctx stack Q packet.val.profile history).tail.map StackWHIRReplay.projectEntry :=
    List.mem_of_getElem? atQuery
  have inPast := projectEntry_query_mem _ pending i x inProjected
  have inHistory := List.mem_of_mem_tail inPast
  have actual := trace_query_rows root statement.root roots trace bound pending i x inHistory
  have phase := decodeHistory_ancestor_query packet.val.profile (fun _ => some statement)
    (fun _ _ => #[]) (fun i => out.rows[i]!) packet.val.statement packet.val.messages
    (past.map StackWHIRReplay.projectEntry) _ zeroParsed k (.query i)
    (by rw [← pastEq,atQuery]; rfl)
  by_cases first : i.val = 0
  · have origin := decodeHistory_statement packet.val.profile (fun _ => some statement)
      roots (fun i => out.rows[i]!) packet.val.statement _ _ replay parsed
    have same : replay.statement = statement := (Option.some.inj origin).symm
    rw [actual,ite_eq_left first,WHIRQueryOracleRecurrence.queryRows_zero replay i first x]
    simp [atQueries,queryIndices,same,← Array.toList_map]
  · have later : 0 < i.val := by omega
    obtain ⟨digest,digestFound,ideal⟩ := WHIRQueryOracleRecurrence.queryRows_decoded_rootLog
      packet.val.profile (fun _ => some statement) roots (fun i => out.rows[i]!) packet.val.statement
      (packet.val.messages.drop (k+1))
      (((localHistory ctx stack Q packet.val.profile history).tail.map StackWHIRReplay.projectEntry).drop (k+1))
      replay parsed
      (WHIRHistory.scheduledAdmissible_drop _ _ _ packet.property.2.2.1) i phase.symm later x
    have found := trace_digest_from_prefix root chain trace (k+1) (i.val-1) digest digestFound
    have index : i.val - 1 + 1 = i.val := by omega
    rw [index] at found
    obtain ⟨rootBound,rootValue⟩ := Array.getElem?_eq_some_iff.mp found
    rw [actual,ite_eq_right first,getElem!_pos out.roots i.val rootBound,rootValue,ideal]
    simp [atQueries,queryIndices,← Array.toList_map]

/-- Exact stack-history bridge for the key extracted from the actual completed local history. The only authentication premise is the opened-row equality. -/
theorem trace_stackRowsAgree {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (packet : RawWHIRKeys.Packet ctx Q) {packets : List (RawWHIRKeys.Packet ctx Q)}
    {lanes : Nat} {proofs : Array PrunedMerklePaths} {out : WireState packet.val.profile} {history}
    (root : Digest32) (catalog : StackWHIRReplay.Catalog packet.val.profile cap)
    (original : WHIRFiatShamir.StackInitial packet.val.profile cap) (roots : WHIRReplay.Roots)
    (found : catalog packet.val.statement = some original)
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q packet.val.profile lanes proofs packets
      (initialWireState packet.val.profile root) out history)
    (bound : BoundRows original.root roots out) :
    WHIRPhysicalHistory.StackRowsAgree packet.val.profile cap catalog roots (fun i => out.rows[i]!)
      ⟨packet.val.statement,packet.val.messages,(localHistory ctx stack Q packet.val.profile history).tail⟩ := by
  intro other initial foundOther seed
  have same : other = original := Option.some.inj (foundOther.symm.trans found)
  subst other
  exact trace_rowsAgree packet root (StackWHIRReplay.transformedStatement original initial.1) roots
    chain trace bound

end Whir.WHIRPhysicalRoots
