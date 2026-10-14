import Whir.AnchoredPhysicalExecution
import Whir.PCSBCSCapturedIdealNativeAcceptance

/-! Exact historical native root roles. The invariant below is obtained from
successful physical transitions, including their scalar parser and nonce
interpreter; it is not a transport or Merkle-acceptance certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Whir.PCSBCSNativeRootRoles
open Concrete Protocol FiatShamirGame DuplexModeGame WHIRHistory
open WHIRPhysicalVerifier WHIRPhysicalReplay PublicMerkleProgram
open MerkleTransport MerkleTransport.Commitments
open RawOracleCoupling.Concrete PCSBCSSourceRootReferences

/-- Only final, nonterminal folds append native roots. -/
def rootPhase {c : Config} : CausalProbability.Coordinate c → Option Nat
  | .fold i j => if j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size then some (i.val+1) else none
  | _ => none

def phaseCount (c : Config) : Nat → Nat
  | 0 => 0
  | n+1 => phaseCount c n + (rootPhase (((schedule c)[n]?).getD .initial)).toList.length

/- This finite source-configuration fact covers all 56 supported profiles.
At each next-root role the chronological append index is its native phase. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem production_root_order : ∀ p : ParameterBounds.Profile,
    ∀ n : Fin (depth (ParameterBounds.config p)),
      (rootPhase (((schedule (ParameterBounds.config p))[n.val]?).getD .initial)).all
        (fun phase => decide (phaseCount (ParameterBounds.config p) n.val + 1 = phase)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem production_initial_remaining : ∀ p : ParameterBounds.Profile,
    CausalGame.remaining (ParameterBounds.config p) 0 =
      (ParameterBounds.config p).logN - (ParameterBounds.config p).folds[0]! := by
  decide +kernel

/-- Native root array indices carry the exact full-leaf shape, not merely the
occupied base-lane suffix. -/
def nativeShape (p : ParameterBounds.Profile) (saved : AnchoredHeaderCodec.Record) (i : Nat) :
    PCSBCSMerkleRootCache.Shape :=
  if i = 0 then initialShape saved.shape else phaseShape (ParameterBounds.config p) i

def nativeReferences (p : ParameterBounds.Profile) (saved : AnchoredHeaderCodec.Record)
    (roots : Array Digest32) : List Reference :=
  roots.toList.zipIdx.map fun (root,i) => ⟨root,nativeShape p saved i⟩

theorem nativeShape_opening (p : ParameterBounds.Profile) (saved : AnchoredHeaderCodec.Record)
    (profile : profileShape p saved.shape) (i : Nat) :
    nativeShape p saved i =
      ⟨(ParameterBounds.length (ParameterBounds.config p) i).log2,leafWords p i,
        if i = 0 then saved.shape.lanes else leafWords p i⟩ := by
  by_cases zero : i = 0
  · subst i
    rcases profile with ⟨hn,hb,hr⟩
    simp [nativeShape,initialShape,leafWords,ParameterBounds.length,
      production_initial_remaining,hn,hb,hr]
  · simp [nativeShape,zero,phaseShape,leafWords,ParameterBounds.length]

theorem nativeReferences_push (p : ParameterBounds.Profile) (saved : AnchoredHeaderCodec.Record)
    (roots : Array Digest32) (root : Digest32) :
    nativeReferences p saved (roots.push root) = nativeReferences p saved roots ++
      [⟨root,nativeShape p saved roots.size⟩] := by
  simp [nativeReferences,List.zipIdx_append]

theorem nativeReferences_lookup (p : ParameterBounds.Profile) (saved : AnchoredHeaderCodec.Record)
    (roots : Array Digest32) (i : Nat) (root : Digest32) (found : roots[i]? = some root) :
    (⟨root,nativeShape p saved i⟩ : Reference) ∈ nativeReferences p saved roots := by
  apply List.mem_map.mpr
  refine ⟨(root,i),List.mk_mem_zipIdx_iff_getElem?.mpr ?_,rfl⟩
  simpa using found

/-- The role check at chronological position n, with no suffix search. -/
def roleAdmitted (c : Config) (n : Nat) (m : Pending) : Bool :=
  if n = 0 then true else
    match rootPhase (((schedule c)[n-1]?).getD .initial) with
    | none => true
    | some phase => (parsePhase c (((schedule c)[n-1]?).getD .initial) m phase 2).isSome

theorem phaseRoles_eq (c : Config) (messages : List Pending) :
    phaseRolesAdmitted c messages = messages.reverse.zipIdx.all (fun (m,n) => roleAdmitted c n m) := by
  unfold phaseRolesAdmitted
  apply congrArg (fun f => messages.reverse.zipIdx.all f)
  funext pair
  rcases pair with ⟨m,n⟩
  dsimp only
  unfold roleAdmitted
  by_cases zero : n = 0
  · simp only [zero,ite_true]
  · simp only [ite_eq_right zero]
    cases (((schedule c)[n-1]?).getD .initial) <;> simp only [rootPhase]
    case fold i j => split <;> rfl

theorem phaseReferences_cons (c : Config) (m : Pending) (messages : List Pending) :
    phaseReferences c (m::messages) = phaseReferences c messages ++ (phaseAt c messages.length m).toList := by
  simp [phaseReferences,List.zipIdx_append]
  cases h : phaseAt c messages.length m <;> simp [h]

theorem phaseRoles_cons (c : Config) (m : Pending) (messages : List Pending) :
    phaseRolesAdmitted c (m::messages) = (phaseRolesAdmitted c messages && roleAdmitted c messages.length m) := by
  simp [phaseRoles_eq,List.zipIdx_append]

/-- Successful scalar parsing forces four scalars and canonical root halves
at an eligible fold. Malformed replies and decode errors are not elided. -/
theorem reply_fold_root {c : Config} (i : Fin c.folds.size) (j : Fin c.folds[i.val]!)
    (last : j.val+1 = c.folds[i.val]!) (later : i.val+1 < c.folds.size)
    (m : Pending) (rows : Oracle) (reply : CausalGame.Reply)
    (parsed : WHIRHistory.decodeReplyScalars (.fold i j) (fun _ => #[]) rows m.scalars = some reply) :
    ∃ root, absorbedRoot (.fold i j) m.scalars = some root ∧
      parsePhase c (.fold i j) m (i.val+1) 2 = some ⟨root,phaseShape c (i.val+1)⟩ := by
  rcases m with ⟨xs,nonce⟩
  cases xs with
  | nil => simp [WHIRHistory.decodeReplyScalars] at parsed
  | cons a xs =>
    cases xs with
    | nil => simp [WHIRHistory.decodeReplyScalars] at parsed
    | cons b xs =>
      cases xs with
      | nil => simp [WHIRHistory.decodeReplyScalars,last,later] at parsed
      | cons r xs =>
        cases xs with
        | nil => simp [WHIRHistory.decodeReplyScalars,last,later] at parsed
        | cons s xs =>
          cases xs with
          | cons t xs => simp [WHIRHistory.decodeReplyScalars,last,later] at parsed
          | nil =>
            cases decoded : ByteCodec.scalarsToHash (r,s) with
            | none => simp [WHIRHistory.decodeReplyScalars,last,later,decoded] at parsed
            | some root =>
              exact ⟨root,by simp [absorbedRoot,last,later,decoded],
                by simp [parsePhase,last,later,parseRootScalars,decoded]⟩

/-- A proof-independent Option update avoids dependent elimination of the
successful parser equation when the array itself is rewritten. -/
def appendRoot (roots : Array Digest32) : Option Digest32 → Array Digest32
  | none => roots
  | some root => roots.push root

/-- Root-array update, exact reference update and role admission from the
actual successful absorber, relative to its actual previous coordinate. -/
theorem absorbResponse_roles {p : ParameterBounds.Profile} (state out : WireState p)
    (m : Pending) (root : Option Digest32) (n : Nat)
    (positive : 0 < n)
    (previous : state.previous = some (((schedule (ParameterBounds.config p))[n-1]?).getD .initial))
    (ok : absorbResponse state m = some (out,root)) :
    out.roots = appendRoot state.roots root ∧
    phaseAt (ParameterBounds.config p) n m =
      (rootPhase (((schedule (ParameterBounds.config p))[n-1]?).getD .initial)).bind
        (fun phase => root.map (fun d => ⟨d,phaseShape (ParameterBounds.config p) phase⟩)) ∧
    roleAdmitted (ParameterBounds.config p) n m = true ∧
    root.toList.length =
      (rootPhase (((schedule (ParameterBounds.config p))[n-1]?).getD .initial)).toList.length := by
  let q := (((schedule (ParameterBounds.config p))[n-1]?).getD .initial)
  obtain ⟨reply,decoded,_⟩ := absorbResponse_some state out m root q previous ok
  have actual : root = absorbedRoot q m.scalars := by
    simp only [absorbResponse,previous] at ok
    change (WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q m).bind _ = some (out,root) at ok
    simp only [decoded,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at ok
    exact ok.2.symm
  have roots : out.roots = appendRoot state.roots root := by
    simp only [absorbResponse,previous] at ok
    change (WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q m).bind _ = some (out,root) at ok
    simp only [decoded,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at ok
    have equal := congrArg (fun s : WireState p => s.roots) ok.1
    change appendRoot state.roots (absorbedRoot q m.scalars) = out.roots at equal
    exact equal.symm.trans (congrArg (appendRoot state.roots) actual.symm)
  refine ⟨roots,?_,?_,?_⟩
  all_goals have nonzero : n ≠ 0 := by omega
  all_goals change WHIRHistory.decodeReplyScalars q (fun _ => #[]) _ m.scalars = some reply at decoded
  all_goals change state.previous = some q at previous
  all_goals change root = absorbedRoot q m.scalars at actual
  all_goals unfold q at *
  all_goals cases coord : (((schedule (ParameterBounds.config p))[n-1]?).getD .initial) with
    | initial => simp [phaseAt,roleAdmitted,nonzero,coord,rootPhase,actual,absorbedRoot]
    | ood i j => simp [phaseAt,roleAdmitted,nonzero,coord,rootPhase,actual,absorbedRoot]
    | query i => simp [phaseAt,roleAdmitted,nonzero,coord,rootPhase,actual,absorbedRoot]
    | tail j => simp [phaseAt,roleAdmitted,nonzero,coord,rootPhase,actual,absorbedRoot]
    | fold i j =>
      by_cases guard : j.val+1 = (ParameterBounds.config p).folds[i.val]! ∧ i.val+1 < (ParameterBounds.config p).folds.size
      · obtain ⟨d,absorbed,parsed⟩ := reply_fold_root i j guard.1 guard.2 m _ reply
          (by simpa only [coord] using decoded)
        have equal : root = some d := actual.trans (by simpa only [coord] using absorbed)
        simp [phaseAt,roleAdmitted,nonzero,coord,rootPhase,guard,equal,parsed]
      · have noParse : parsePhase (ParameterBounds.config p) (.fold i j) m (i.val+1) 2 = none := by
          simp only [parsePhase]
          rw [ite_eq_right (by intro h; exact guard ⟨h.1,h.2.1⟩)]
        have absent : rootPhase (.fold i j) = none := by simp only [rootPhase,ite_eq_right guard]
        have noRoot : absorbedRoot (.fold i j) m.scalars = none := by simp only [absorbedRoot,ite_eq_right guard]
        simp only [phaseAt,roleAdmitted,ite_eq_right nonzero,coord,absent,noParse,actual,noRoot,
          Option.bind_none,Option.toList_none,List.length_nil]

/-- Nonce binding and output caching cannot change the root array or openings. -/
theorem afterNonce_roots {p : ParameterBounds.Profile} {ctx : RawWHIRKeys.Context} {Q : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} (state out : WireState p)
    (nonce : WHIRPowProgram.Outcome ctx Q packet) (ok : afterNonce state nonce = some out) :
    out.roots = state.roots ∧ out.openings = state.openings := by
  unfold afterNonce at ok
  split at ok
  · cases Option.some.inj ok; exact ⟨rfl,rfl⟩
  · cases cached : state.outputCache with
    | none => simp [cached] at ok
    | some digest =>
      simp only [cached,Option.map_some,Option.some.injEq] at ok
      subst out
      exact ⟨rfl,rfl⟩

theorem absorbResponse_openings {p : ParameterBounds.Profile} (state out : WireState p)
    (pending : Pending) (root : Option Digest32) (ok : absorbResponse state pending = some (out,root)) :
    out.openings = state.openings := by
  unfold absorbResponse at ok
  cases previous : state.previous with
  | none =>
    simp only [previous] at ok
    split at ok
    · cases Option.some.inj ok; rfl
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
      rfl

def openingRole {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record)
    (opening : QueryOpening p) : Reference :=
  ⟨opening.root,nativeShape p saved opening.level.val⟩

theorem takeSample_roots {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (state out : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (trace : List Observation) (run : Runs (takeSample saved.shape.lanes proofs state q x) trace (some out))
    (prior : ∀ opening ∈ state.openings, openingRole saved opening ∈ nativeReferences p saved state.roots) :
    out.roots = state.roots ∧
      ∀ opening ∈ out.openings, openingRole saved opening ∈ nativeReferences p saved out.roots := by
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
          refine ⟨rfl,?_⟩
          intro opening member
          rcases List.mem_cons.mp member with equal | old
          · subst opening
            exact nativeReferences_lookup p saved state.roots i.val _ hr
          · exact prior opening old
    · cases run
  | initial => cases run; exact ⟨rfl,prior⟩
  | fold i j => cases run; exact ⟨rfl,prior⟩
  | ood i j => cases run; exact ⟨rfl,prior⟩
  | tail j => cases run; exact ⟨rfl,prior⟩

/-- Actual raw roots, exact full reference geometry, every retained opening,
and canonical admission of every chronological root role. -/
structure RootRoles {ctx : RawWHIRKeys.Context} {Q : Nat} {p : ParameterBounds.Profile}
    (saved : AnchoredHeaderCodec.Record) (packet : RawWHIRKeys.Packet ctx Q)
    (state : WireState p) : Prop where
  count : state.roots.size = phaseCount (ParameterBounds.config p) (packet.val.messages.length-1) + 1
  references : nativeReferences p saved state.roots =
    ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config p) packet.val.messages
  admitted : phaseRolesAdmitted (ParameterBounds.config p) packet.val.messages = true
  openings : ∀ opening ∈ state.openings, openingRole saved opening ∈ nativeReferences p saved state.roots

theorem RootRoles.roots {ctx : RawWHIRKeys.Context} {Q : Nat} {p : ParameterBounds.Profile}
    {saved : AnchoredHeaderCodec.Record} {packet : RawWHIRKeys.Packet ctx Q} {state : WireState p}
    (roles : RootRoles saved packet state) :
    state.roots.toList = saved.root ::
      (phaseReferences (ParameterBounds.config p) packet.val.messages).map Reference.root := by
  have equal := congrArg (List.map Reference.root) roles.references
  simpa [nativeReferences,List.map_map,Function.comp_def,List.zipIdx_map_fst] using equal


theorem step_sample_roles {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record) {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    (step : Step ctx stack Q p saved.shape.lanes proofs packet profile state raw out)
    (absorbedRoles : ∀ absorbed root,
      absorbResponse state (packet.val.messages.headD ⟨[],none⟩) = some (absorbed,root) →
      RootRoles saved packet absorbed) :
    RootRoles saved packet out := by
  cases step with
  | run parsed size shape boundNonce accepted opened =>
    have roles := absorbedRoles _ _ parsed
    obtain ⟨nonceRoots,nonceOpenings⟩ := afterNonce_roots _ _ _ boundNonce
    obtain ⟨sampleRoots,sampleOpenings⟩ := takeSample_roots saved _ _ _ _ _ _ opened
      (by rw [nonceOpenings,nonceRoots]; exact roles.openings)
    refine ⟨?_,?_,roles.admitted,sampleOpenings⟩
    · dsimp only [withOutput]
      rw [sampleRoots,nonceRoots]
      exact roles.count
    · dsimp only [withOutput]
      rw [sampleRoots,nonceRoots]
      exact roles.references

theorem roles_initial {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record) {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)}
    (single : packet.val.messages = [WHIRHistoryKey.initialPending])
    (step : Step ctx stack Q p saved.shape.lanes proofs packet profile (initialWireState p saved.root) raw out) :
    RootRoles saved packet out := by
  apply step_sample_roles saved step
  intro absorbed root parsed
  simp only [single,List.headD_cons,WHIRHistoryKey.initialPending,initialWireState,
    absorbResponse,List.isEmpty_nil,ite_true,Option.some.injEq,Prod.mk.injEq] at parsed
  obtain ⟨rfl,rfl⟩ := parsed
  constructor
  · simp [single,phaseCount]
  · simp [nativeReferences,nativeShape,single,phaseReferences,phaseAt]
  · simp [single,phaseRoles_eq,roleAdmitted]
  · simp

theorem roles_next {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record) {proofs : Array PrunedMerklePaths}
    {packet priorPacket : RawWHIRKeys.Packet ctx Q} {profile : packet.val.profile = p}
    {state out : WireState p} {raw : GroupAnswer ctx Q (.inl packet)} {history}
    (m : Pending) (messages : packet.val.messages = m::priorPacket.val.messages)
    (complete : Completed stack priorPacket state history)
    (prior : RootRoles saved priorPacket state)
    (step : Step ctx stack Q p saved.shape.lanes proofs packet profile state raw out) :
    RootRoles saved packet out := by
  obtain ⟨priorProfile,priorRaw,past,tape,seed,_,previous,_,_,_,_,_,_⟩ := complete
  have positive : 0 < priorPacket.val.messages.length := List.length_pos_iff.mpr priorPacket.property.2.1
  have priorQuery : packetQuery ctx Q p priorPacket priorProfile =
      (((schedule (ParameterBounds.config p))[priorPacket.val.messages.length-1]?).getD .initial) := by
    rw [packetQuery_eq ctx Q p priorPacket priorProfile priorPacket.val.statement]
    rfl
  have scheduled : priorPacket.val.messages.length-1 < depth (ParameterBounds.config p) := by
    have bounds := priorPacket.property.2.2.1
    simp only [WHIRHistory.scheduledAdmissible,Bool.and_eq_true] at bounds
    have admissible := bounds.1
    unfold WHIRHistory.admissible at admissible
    simp only [decide_eq_true_eq] at admissible
    rw [priorProfile] at admissible
    omega
  apply step_sample_roles saved step
  intro absorbed root parsed
  rw [messages,List.headD_cons] at parsed
  obtain ⟨roots,phase,admitted,length⟩ := absorbResponse_roles state absorbed m root
    priorPacket.val.messages.length positive (previous.trans (congrArg some priorQuery)) parsed
  have openingEq := absorbResponse_openings state absorbed m root parsed
  have count : absorbed.roots.size =
      phaseCount (ParameterBounds.config p) (packet.val.messages.length-1) + 1 := by
    rw [roots,messages]
    have successor : priorPacket.val.messages.length = (priorPacket.val.messages.length-1)+1 := by omega
    simp only [List.length_cons,Nat.add_sub_cancel]
    rw [successor,phaseCount,← length]
    cases root <;> simp [appendRoot,prior.count]
  have refs : nativeReferences p saved absorbed.roots =
      ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config p) packet.val.messages := by
    rw [messages,phaseReferences_cons,phase,roots]
    cases hphase : rootPhase (((schedule (ParameterBounds.config p))[priorPacket.val.messages.length-1]?).getD .initial) with
    | none =>
      have empty : root = none := by cases root <;> simp_all
      simp [empty,appendRoot,prior.references]
    | some k =>
      have order := production_root_order p ⟨priorPacket.val.messages.length-1,scheduled⟩
      simp only [hphase,Option.all_some,decide_eq_true_eq] at order
      cases root with
      | none => simp [appendRoot,prior.references]
      | some d =>
        have index : state.roots.size = k := prior.count.trans order
        have nonzero : k ≠ 0 := by rw [← order]; omega
        simp [appendRoot,nativeReferences_push,prior.references,index,nativeShape,nonzero,List.cons_append]
  refine ⟨count,refs,?_,?_⟩
  · rw [messages,phaseRoles_cons,prior.admitted,admitted]
    rfl
  · intro opening member
    rw [openingEq] at member
    have earlier := prior.openings opening member
    rw [roots]
    cases root with
    | none => exact earlier
    | some d => rw [appendRoot,nativeReferences_push]; exact List.mem_append_left _ earlier

/-- All phases are derived from the actual native completion trace. -/
theorem trace_rootRoles {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q : Nat}
    {p : ParameterBounds.Profile} (saved : AnchoredHeaderCodec.Record) {proofs : Array PrunedMerklePaths}
    {packet : RawWHIRKeys.Packet ctx Q} {packets : List (RawWHIRKeys.Packet ctx Q)}
    {out : WireState p} {history}
    (chain : Chain ctx Q packet packets)
    (trace : Trace ctx stack Q p saved.shape.lanes proofs packets (initialWireState p saved.root) out history) :
    RootRoles saved packet out := by
  induction chain generalizing out history with
  | initial packet single =>
    cases trace with
    | cons profile step rest =>
      cases rest
      exact roles_initial saved single step
  | next m prior messages statement profile ih =>
    obtain ⟨middle,before,after,hist,first,last⟩ := Trace.append_inv _ _ trace
    cases last with
    | cons finalProfile step rest =>
      cases rest
      exact roles_next saved m messages (trace_completed saved.root prior first) (ih first) step

theorem verifySource_rootRoles (cap : Nat) (boundary : AnchoredPhysicalDriver.Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (saved : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (run : Runs (WHIRSourceChronology.erase
      (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet saved proofs)) observations (some a)) :
    RootRoles saved packet a.wire := by
  obtain ⟨_,_,_,trace,_⟩ := AnchoredPhysicalExecution.verifySource_execution
    cap boundary model ctx stack Q packet saved proofs observations a run
  exact trace_rootRoles saved (completion_chain ctx Q packet) trace

/-- Exact opening references occur in the literal whole Pending role list.
No root-availability or queried-leaf-availability premise occurs here. -/
theorem verifySource_opening_member (cap : Nat) (boundary : AnchoredPhysicalDriver.Boundary)
    (model : WHIRCallerSupport.ProductionLayout) (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (saved : AnchoredHeaderCodec.Record) (proofs : Array PrunedMerklePaths)
    (observations : List Observation) (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (run : Runs (WHIRSourceChronology.erase
      (AnchoredPhysicalDriver.verifySource cap boundary model ctx stack Q packet saved proofs)) observations (some a)) :
    saved.Valid ∧ profileShape packet.val.profile saved.shape ∧
      phaseRolesAdmitted (ParameterBounds.config packet.val.profile) packet.val.messages = true ∧
      ∀ opening ∈ a.wire.openings,
        PCSBCSCapturedIdealNativeAcceptance.openingReference ctx Q packet opening saved.shape.lanes ∈
          ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config packet.val.profile) packet.val.messages := by
  have roles := verifySource_rootRoles cap boundary model ctx stack Q packet saved proofs observations a run
  have profile : profileShape packet.val.profile saved.shape := a.configuration.2
  refine ⟨a.configuration.1,profile,roles.admitted,?_⟩
  intro opening member
  have present := roles.openings opening member
  rw [roles.references] at present
  simpa only [openingRole,nativeShape_opening packet.val.profile saved profile,
    PCSBCSCapturedIdealNativeAcceptance.openingReference] using present

/-- The literal source-table caller decoder is admitted by actual fresh-driver
success. Unlike original claim preparation, this parser fact needs no 2^64
family-cap premise. Only actually queried caller coordinates are transported. -/
theorem mixed_success_fresh_decode (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat) (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet
      saved proofs ctx.iv B limit seed ro).result.value = some a) :
    ∃ claims, AnchoredSourceFreshCaller.decode model.layout saved (RawWHIRKeys.entry ctx packet.val)
      (PCSBCSSourceCallerAnswers.answers
        ((PCSBCSChallengeOracle.EnteredPacket.partition (p := packet.val.profile)
          (Q := B) (iv := ctx.iv)
          (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)).split
            (PublicCompressionCouplingMixed.oracle seed ro))) = some claims := by
  let view := AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet
    saved proofs ctx.iv B limit seed ro
  let answers := PCSBCSSourceCallerAnswers.answers
    ((PCSBCSChallengeOracle.EnteredPacket.partition (p := packet.val.profile)
      (Q := B) (iv := ctx.iv)
      (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length)).split
        (PublicCompressionCouplingMixed.oracle seed ro))
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs
    cap .fresh model ctx stack Q packet saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨⟨before,after,splitTrace,_,queries,parsed⟩,_,_,_,_⟩ :=
    AnchoredPhysicalExecution.verifySource_execution cap .fresh model ctx stack Q packet saved proofs _ a run
  have splitView : view.observations = before ++ after := splitTrace
  have earlier : ∀ wanted ∈ WHIRCallerOutputs.callerOutputs (RawWHIRKeys.entry ctx packet.val),
      WHIRPhysicalCaller.latestAnswers before wanted = some (answers wanted) := by
    intro wanted prior
    have queried : Query.construction wanted (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) ∈
        before.map Observation.query := by
      rw [queries]
      exact List.mem_map.mpr ⟨⟨wanted,prior⟩,List.mem_attach _ _,rfl⟩
    obtain ⟨o,member,equal⟩ := List.mem_map.mp queried
    apply WHIRPhysicalCaller.latestAnswers_consistent before wanted
      (RawWHIRKeys.callerOutput_admissible ctx Q packet wanted prior) _ ⟨o,member,equal⟩
    intro observation member valid same
    have present : observation ∈ view.observations := by
      rw [splitView]
      exact List.mem_append_left _ member
    have construction : (⟨.construction wanted valid,observation.answer⟩ : Observation) ∈ view.observations := by
      cases observation
      cases same
      exact present
    simp only [view,AnchoredMixedIdealSourceAcceptance.mixedView,
      PublicCompressionCouplingMixed.compile_actual] at construction
    obtain ⟨bounded,actual⟩ := PCSBCSIdealConstructionAnswers.construction_observations _ ro ctx.iv _ _ _ _ _
      wanted valid _ construction
    dsimp only [answers]
    rw [PCSBCSNativeIdealCallerOriginal.split_answers seed ro wanted bounded]
    exact actual
  obtain ⟨claims,caller,_,_,_⟩ := AnchoredPhysicalDriver.request_origin .fresh cap packet.val.profile
    model.layout saved (RawWHIRKeys.entry ctx packet.val) (WHIRPhysicalCaller.latestAnswers before) a.request parsed
  refine ⟨claims,?_⟩
  have tokens := WHIRCallerClaims.entryTokens_prior_only (RawWHIRKeys.entry ctx packet.val)
    (fun q => (WHIRPhysicalCaller.latestAnswers before q).getD DuplexRefinement.zeroDigest) answers
    (by intro q member; rw [earlier q member]; rfl)
  simpa only [AnchoredPhysicalDriver.decodeCaller,AnchoredSourceFreshCaller.decode,tokens] using caller

/-- An entered packet at the actual source cap B may be a reindexing of the
native Q packet: only literal entry and Pending equality are required. Parent
packet visitation supplies this packet using the observed path bound, without
Q ≤ B. Caller admission is derived from the actual mixed execution. -/
theorem mixed_success_address_member (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat) (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet
      saved proofs ctx.iv B limit seed ro).result.value = some a)
    (current : PCSBCSChallengeOracle.EnteredPacket packet.val.profile B ctx.iv
      (RawWHIRKeys.entry ctx packet.val).frames.length)
    (entry : current.1.val = RawWHIRKeys.entry ctx packet.val)
    (messages : current.2.messages = packet.val.messages) :
    ∀ opening ∈ a.wire.openings,
      PCSBCSCapturedIdealNativeAcceptance.openingReference ctx Q packet opening saved.shape.lanes ∈
        PCSBCSCapturedSourceTransport.address (.inl current) := by
  obtain ⟨run,_,_⟩ := AnchoredMixedIdealSourceAcceptance.mixedView_runs
    cap .fresh model ctx stack Q packet saved proofs ctx.iv B limit seed ro
  rw [success] at run
  obtain ⟨valid,profile,roles,member⟩ := verifySource_opening_member cap .fresh model ctx stack Q
    packet saved proofs _ a run
  obtain ⟨claims,caller⟩ := mixed_success_fresh_decode cap model ctx stack Q packet saved proofs
    B limit seed ro a success
  have admitted := PCSBCSCapturedSourceTransport.address_packet model.layout saved _ current
    valid profile claims (by simpa only [entry] using caller) (by simpa only [messages] using roles)
  rw [admitted,messages]
  exact member

/-- Conversion endpoint for `packetAtBound`: arbitrary source cap B, same
literal native packet data. No comparison of the native and source caps. -/
theorem mixed_success_reindexed_address (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat) (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)
    (a : AnchoredPhysicalDriver.Accepted ctx Q cap packet saved)
    (success : (AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet
      saved proofs ctx.iv B limit seed ro).result.value = some a)
    (packetB : RawWHIRKeys.Packet ctx B) (same : packetB.val = packet.val) :
    let current := PCSBCSNativePacketBridge.enteredPacketAt ctx stack B packetB
      (congrArg RawWHIRKeys.PacketData.profile same) (congrArg (RawWHIRKeys.entry ctx) same)
    ∀ opening ∈ a.wire.openings,
      PCSBCSCapturedIdealNativeAcceptance.openingReference ctx Q packet opening saved.shape.lanes ∈
        PCSBCSCapturedSourceTransport.address (.inl current) := by
  apply mixed_success_address_member cap model ctx stack Q packet saved proofs B limit seed ro a success
  · exact PCSBCSNativePacketBridge.enteredPacketAt_entry ctx stack B packetB _ _
  · rw [PCSBCSNativePacketBridge.enteredPacketAt_messages]
    exact congrArg RawWHIRKeys.PacketData.messages same

#print axioms production_root_order
#print axioms production_initial_remaining
#print axioms absorbResponse_roles
#print axioms nativeShape_opening
#print axioms RootRoles.roots
#print axioms trace_rootRoles
#print axioms verifySource_opening_member
#print axioms mixed_success_fresh_decode
#print axioms mixed_success_address_member
#print axioms mixed_success_reindexed_address

end Whir.PCSBCSNativeRootRoles
