import Whir.DuplexRawProgram
import Whir.CausalBindingState
import Whir.PublicMerkleLog

/-! Source-owned bookkeeping is returned by the executable interaction, not supplied as a claimed trace or read from simulator-private state. The compiler preserves every public query, answer, result, and complete-path budget. This module does not assert that an arbitrary caller's claims can be recovered from its transcript bytes. -/
namespace Whir.WHIRSourceChronology
open FiatShamirGame DuplexModeGame

inductive Event (cap : Nat) where
  | answer (query : Query) (value : Digest32)
  | commit (root : Digest32)
  | claims (profile : ParameterBounds.Profile) (entry : FramedHistory)
      (request : CausalBindingState.ClaimRequest cap profile)

structure Result (cap : Nat) (R : Type) where
  value : R
  events : List (Event cap)

inductive Source (cap : Nat) (R : Type) where
  | done (value : R)
  | ask (query : Query) (next : Digest32 → Source cap R)
  | commit (root : Digest32) (next : Source cap R)
  | claims (profile : ParameterBounds.Profile) (entry : FramedHistory)
      (request : CausalBindingState.ClaimRequest cap profile) (next : Source cap R)

def prepend (event : Event cap) (result : Result cap R) : Result cap R :=
  ⟨result.value,event :: result.events⟩

def map (f : R → S) : Program R → Program S
  | .done r => .done (f r)
  | .ask q next => .ask q (fun answer => map f (next answer))

def compile : Source cap R → Program (Result cap R)
  | .done r => .done ⟨r,[]⟩
  | .ask q next => .ask q (fun answer => map (prepend (.answer q answer)) (compile (next answer)))
  | .commit root next => map (prepend (.commit root)) (compile next)
  | .claims p entry request next => map (prepend (.claims p entry request)) (compile next)

def erase : Source cap R → Program R
  | .done r => .done r
  | .ask q next => .ask q (fun answer => erase (next answer))
  | .commit _ next => erase next
  | .claims _ _ _ next => erase next

def observations : List (Event cap) → List Observation
  | [] => []
  | .answer q d :: rest => ⟨q,d⟩ :: observations rest
  | .commit _ :: rest => observations rest
  | .claims _ _ _ :: rest => observations rest

def Counts : Nat → Source cap R → Prop
  | _, .done _ => True
  | Q, .ask q next => q.cost ≤ Q ∧ ∀ d, Counts (Q-q.cost) (next d)
  | Q, .commit _ next => Counts Q next
  | Q, .claims _ _ _ next => Counts Q next

theorem map_counted (f : R → S) (p : Program R) (Q : Nat) :
    DuplexModeGame.Counts Q (map f p) ↔ DuplexModeGame.Counts Q p := by
  induction p generalizing Q with
  | done => rfl
  | ask q next ih => simp only [map, DuplexModeGame.Counts, ih]

theorem compile_counted (p : Source cap R) (Q : Nat) :
    DuplexModeGame.Counts Q (compile p) ↔ Counts Q p := by
  induction p generalizing Q with
  | done => rfl
  | ask q next ih => simp only [compile, Counts, DuplexModeGame.Counts, map_counted, ih]
  | commit root next ih => simpa only [compile, Counts, map_counted] using ih Q
  | claims profile entry request next ih => simpa only [compile, Counts, map_counted] using ih Q

theorem erase_counted (p : Source cap R) (Q : Nat) :
    DuplexModeGame.Counts Q (erase p) ↔ Counts Q p := by
  induction p generalizing Q with
  | done => rfl
  | ask q next ih => simp only [erase, Counts, DuplexModeGame.Counts, ih]
  | commit root next ih => exact ih Q
  | claims profile entry request next ih => exact ih Q

def mapExecution (f : R → S) (execution : Execution R) : Execution S :=
  {view := ⟨execution.view.observations,f execution.view.result⟩
   primitiveCost := execution.primitiveCost
   constructionRequests := execution.constructionRequests
   simulatorQueries := execution.simulatorQueries}

theorem map_real (f : R → S) (oracle : PrimitiveOracle) (iv : Digest32) (p : Program R) :
    runReal oracle iv (map f p) = mapExecution f (runReal oracle iv p) := by
  induction p with
  | done => rfl
  | ask q next ih => simp only [map, runReal, ih]; rfl

theorem map_ideal {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (f : R → S)
    (p : Program R) (remaining : Nat) (limit : remaining ≤ Q)
    (counted : DuplexModeGame.Counts remaining p) :
    runIdeal sim ro iv state (map f p) remaining limit ((map_counted f p remaining).mpr counted) =
      mapExecution f (runIdeal sim ro iv state p remaining limit counted) := by
  induction p generalizing state remaining with
  | done => rfl
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      let answer := runRO ro (sim.answer state input)
      exact congrArg (DuplexModeGame.prepend (.primitive purpose input) answer.1.2 answer.2)
        (ih answer.1.2 answer.1.1 (remaining-1) (by omega) (counted.2 answer.1.2))
    | construction coordinate valid =>
      let answer := ro (constructionKey Q iv coordinate (counted.1.trans limit))
      exact congrArg (DuplexModeGame.prepend (.construction coordinate valid) answer 0)
        (ih answer state (remaining-DuplexFraming.pathCost coordinate) (by omega) (counted.2 answer))

theorem real_source_trace (oracle : PrimitiveOracle) (iv : Digest32) (p : Source cap R) :
    observations (runReal oracle iv (compile p)).view.result.events =
      (runReal oracle iv (compile p)).view.observations := by
  induction p with
  | done => rfl
  | ask q next ih => simpa only [compile, runReal, map_real, mapExecution, DuplexModeGame.prepend,
      prepend, observations] using congrArg (List.cons ⟨q,realAnswer oracle iv q⟩) (ih (realAnswer oracle iv q))
  | commit root next ih => simpa only [compile, map_real, mapExecution, prepend, observations] using ih
  | claims profile entry request next ih => simpa only [compile, map_real, mapExecution, prepend, observations] using ih

theorem real_source_erasure (oracle : PrimitiveOracle) (iv : Digest32) (p : Source cap R) :
    mapExecution Result.value (runReal oracle iv (compile p)) = runReal oracle iv (erase p) := by
  induction p with
  | done => rfl
  | ask q next ih =>
    simp only [compile, erase, runReal, map_real]
    rw [← ih (realAnswer oracle iv q)]
    rfl
  | commit root next ih => simpa only [compile, erase, map_real, mapExecution, prepend] using ih
  | claims profile entry request next ih => simpa only [compile, erase, map_real, mapExecution, prepend] using ih

structure Prefix (cap : Nat) (R : Type) where
  events : List (Event cap)
  pending : Option Query
  value : Option R

def prependPrefix (event : Event cap) (seen : Prefix cap R) : Prefix cap R :=
  {seen with events := event :: seen.events}

/-- Stop before the first unanswered public query. Commit and claim instructions before that query are retained, including instructions between two queries. No future reply or simulator seed is an argument. -/
def recover : Source cap R → List Observation → Prefix cap R
  | .done r, _ => ⟨[],none,some r⟩
  | .ask q _, [] => ⟨[],some q,none⟩
  | .ask q next, answer :: rest =>
      prependPrefix (.answer q answer.answer) (recover (next answer.answer) rest)
  | .commit root next, answers => prependPrefix (.commit root) (recover next answers)
  | .claims p entry request next, answers =>
      prependPrefix (.claims p entry request) (recover next answers)

def completedPrefix (result : Result cap R) : Prefix cap R :=
  ⟨result.events,none,some result.value⟩

theorem recover_real (oracle : PrimitiveOracle) (iv : Digest32) (p : Source cap R) :
    recover p (runReal oracle iv (compile p)).view.observations =
      completedPrefix (runReal oracle iv (compile p)).view.result := by
  induction p with
  | done => rfl
  | ask q next ih =>
    simpa only [compile, runReal, map_real, mapExecution, DuplexModeGame.prepend, recover,
      prepend, prependPrefix, completedPrefix] using
      congrArg (prependPrefix (.answer q (realAnswer oracle iv q))) (ih (realAnswer oracle iv q))
  | commit root next ih =>
    simpa only [compile, map_real, mapExecution, recover, prepend, prependPrefix, completedPrefix]
      using congrArg (prependPrefix (.commit root)) ih
  | claims profile entry request next ih =>
    simpa only [compile, map_real, mapExecution, recover, prepend, prependPrefix, completedPrefix]
      using congrArg (prependPrefix (.claims profile entry request)) ih

theorem recover_ideal {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State)
    (p : Source cap R) (remaining : Nat) (limit : remaining ≤ Q) (counted : Counts remaining p) :
    recover p (runIdeal sim ro iv state (compile p) remaining limit
      ((compile_counted p remaining).mpr counted)).view.observations =
      completedPrefix (runIdeal sim ro iv state (compile p) remaining limit
        ((compile_counted p remaining).mpr counted)).view.result := by
  induction p generalizing state remaining with
  | done => rfl
  | ask q next ih =>
    cases q with
    | primitive purpose input =>
      let answer := runRO ro (sim.answer state input)
      have mapped := map_ideal sim ro iv answer.1.1
        (prepend (.answer (.primitive purpose input) answer.1.2))
        (compile (next answer.1.2)) (remaining-1) (by omega)
        ((compile_counted _ _).mpr (counted.2 answer.1.2))
      have inner := ih answer.1.2 answer.1.1 (remaining-1) (by omega) (counted.2 answer.1.2)
      have whole : runIdeal sim ro iv state (compile (.ask (.primitive purpose input) next))
          remaining limit ((compile_counted _ _).mpr counted) = _ :=
        congrArg (DuplexModeGame.prepend (.primitive purpose input) answer.1.2 answer.2) mapped
      rw [whole]
      simpa only [mapExecution, DuplexModeGame.prepend, recover, prepend, prependPrefix,
        completedPrefix] using congrArg (prependPrefix (.answer (.primitive purpose input) answer.1.2)) inner
    | construction coordinate valid =>
      let answer := ro (constructionKey Q iv coordinate (counted.1.trans limit))
      have mapped := map_ideal sim ro iv state
        (prepend (.answer (.construction coordinate valid) answer))
        (compile (next answer)) (remaining-DuplexFraming.pathCost coordinate) (by omega)
        ((compile_counted _ _).mpr (counted.2 answer))
      have inner := ih answer state (remaining-DuplexFraming.pathCost coordinate)
        (by omega) (counted.2 answer)
      have whole : runIdeal sim ro iv state (compile (.ask (.construction coordinate valid) next))
          remaining limit ((compile_counted _ _).mpr counted) = _ :=
        congrArg (DuplexModeGame.prepend (.construction coordinate valid) answer 0) mapped
      rw [whole]
      simpa only [mapExecution, DuplexModeGame.prepend, recover, prepend, prependPrefix,
        completedPrefix] using congrArg (prependPrefix (.answer (.construction coordinate valid) answer)) inner
  | commit root next ih =>
    have mapped := map_ideal sim ro iv state (prepend (.commit root)) (compile next)
      remaining limit ((compile_counted _ _).mpr counted)
    have whole : runIdeal sim ro iv state (compile (.commit root next))
        remaining limit ((compile_counted _ _).mpr counted) = _ := mapped
    rw [whole]
    simpa only [mapExecution, recover, prepend, prependPrefix, completedPrefix]
      using congrArg (prependPrefix (.commit root)) (ih state remaining limit counted)
  | claims profile entry request next ih =>
    have mapped := map_ideal sim ro iv state (prepend (.claims profile entry request)) (compile next)
      remaining limit ((compile_counted _ _).mpr counted)
    have whole : runIdeal sim ro iv state (compile (.claims profile entry request next))
        remaining limit ((compile_counted _ _).mpr counted) = _ := mapped
    rw [whole]
    simpa only [mapExecution, recover, prepend, prependPrefix, completedPrefix]
      using congrArg (prependPrefix (.claims profile entry request)) (ih state remaining limit counted)

def observeRecords (state : CausalBindingState.State cap)
    (records : MerkleTransport.Commitments.Records) : CausalBindingState.State cap :=
  records.foldl (fun state record => CausalBindingState.observe state record.1 record.2) state

theorem observeRecords_extends (state : CausalBindingState.State cap)
    (records : MerkleTransport.Commitments.Records) :
    CausalBindingState.Extends state (observeRecords state records) := by
  induction records generalizing state with
  | nil => exact .refl _
  | cons record rest ih =>
    exact (CausalBindingState.observe_extends state record.1 record.2).trans (ih _)

theorem observeRecords_authentic (hash : MerkleTransport.Primitive)
    (state : CausalBindingState.State cap) (records : MerkleTransport.Commitments.Records)
    (old : CausalBindingState.AuthenticState hash state)
    (new : MerkleTransport.Commitments.Authentic hash records) :
    CausalBindingState.AuthenticState hash (observeRecords state records) := by
  induction records generalizing state with
  | nil => exact old
  | cons record rest ih =>
    apply ih
    · exact CausalBindingState.observe_authentic hash state record.1 record.2 old
        (new _ _ (by simp))
    · intro bytes digest member
      exact new bytes digest (by simp [member])

/-- Ordinary Merkle hashes are recognized from actual public compression inputs and replies, including multiblock and final-first traces. A purported high-level hash record is never an input. -/
def observePublic (state : CausalBindingState.State cap) (input : DuplexFraming.Node)
    (answer : Digest32) : CausalBindingState.State cap :=
  let observed := PublicMerkleLog.observe state.publicLog input answer
  observeRecords {state with publicLog := observed.1} observed.2

theorem observePublic_extends (state : CausalBindingState.State cap)
    (input : DuplexFraming.Node) (answer : Digest32) :
    CausalBindingState.Extends state (observePublic state input answer) := by
  exact (show CausalBindingState.Extends state
      {state with publicLog := (PublicMerkleLog.observe state.publicLog input answer).1} from
    ⟨fun _ _ h => h,fun _ _ h => h,fun _ _ _ => rfl,fun _ _ _ h => h,fun _ _ _ => rfl⟩).trans
      (observeRecords_extends _ _)

theorem observePublic_authentic (oracle : PrimitiveOracle) (state : CausalBindingState.State cap)
    (input : DuplexFraming.Node)
    (old : CausalBindingState.AuthenticState (PublicMerkleLog.hash oracle) state)
    (log : PublicMerkleLog.AuthenticLog oracle state.publicLog) :
    CausalBindingState.AuthenticState (PublicMerkleLog.hash oracle)
      (observePublic state input (oracle input)) :=
  observeRecords_authentic _ _ _ old (PublicMerkleLog.observe_authentic oracle state.publicLog log input)

/-- Missing commitment announcements are explicit bookkeeping errors. Claim metadata checks announcement order only: original claims are recovered by the concrete caller decoder, never installed from this event. -/
def step (state : CausalBindingState.State cap) :
    Event cap → Except Digest32 (CausalBindingState.State cap)
  | .answer (.primitive _ input) answer => .ok (observePublic state input answer)
  | .answer (.construction _ _) _ => .ok state
  | .commit root => .ok (CausalBindingState.registerRoot state root)
  | .claims _ _ request =>
      match MerkleTransport.Commitments.lookup request.root state.registry with
      | none => .error request.root
      | some _ => .ok state

theorem step_extends (state next : CausalBindingState.State cap) (event : Event cap)
    (success : step state event = .ok next) : CausalBindingState.Extends state next := by
  cases event with
  | answer query value =>
    cases query with
    | primitive purpose input =>
      cases success
      exact observePublic_extends _ _ _
    | construction coordinate valid =>
      cases success
      exact .refl _
  | commit root =>
    cases success
    exact CausalBindingState.registerRoot_extends _ _
  | claims profile entry request =>
    unfold step at success
    cases found : MerkleTransport.Commitments.lookup request.root state.registry with
    | none => simp [found] at success
    | some snapshot =>
      simp only [found] at success
      cases success
      exact .refl _

def replay (state : CausalBindingState.State cap) :
    List (Event cap) → Except Digest32 (CausalBindingState.State cap)
  | [] => .ok state
  | event :: rest =>
      match step state event with
      | .error root => .error root
      | .ok next => replay next rest

theorem replay_extends (state next : CausalBindingState.State cap) (events : List (Event cap))
    (success : replay state events = .ok next) : CausalBindingState.Extends state next := by
  induction events generalizing state with
  | nil => cases success; exact .refl _
  | cons event rest ih =>
    unfold replay at success
    cases progress : step state event with
    | error root => simp [progress] at success
    | ok middle =>
      exact (step_extends state middle event progress).trans (ih middle (by simpa [progress] using success))

theorem replay_retains_commitment (state next : CausalBindingState.State cap)
    (events : List (Event cap)) (success : replay state events = .ok next)
    (profile : ParameterBounds.Profile) (root : Digest32) (lanes : Nat)
    (bound : lanes ≤ 2 ^ (ParameterBounds.config profile).folds[0]!)
    (snapshot : MerkleTransport.Commitments.Snapshot)
    (known : MerkleTransport.Commitments.lookup root state.registry = some snapshot) :
    CausalBindingState.capture next profile root lanes bound =
      CausalBindingState.capture state profile root lanes bound :=
  (CausalBindingState.capture_stable (replay_extends state next events success)
    profile root lanes bound snapshot known).symm

/-- Public source metadata is retained only up to the next unanswered query. In particular the current reply and every claim derived after it are excluded. -/
def beforeAnswers : Nat → List (Event cap) → List (Event cap)
  | _, [] => []
  | 0, .answer _ _ :: _ => []
  | n+1, event@(.answer _ _) :: rest => event :: beforeAnswers n rest
  | n, event@(.commit _) :: rest => event :: beforeAnswers n rest
  | n, event@(.claims _ _ _) :: rest => event :: beforeAnswers n rest

theorem beforeAnswers_recover (p : Source cap R) (answers : List Observation) (n : Nat) :
    beforeAnswers n (recover p answers).events = (recover p (answers.take n)).events := by
  induction p generalizing answers n with
  | done => rfl
  | ask q next ih =>
    cases answers with
    | nil => cases n <;> rfl
    | cons answer rest =>
      cases n with
      | zero => rfl
      | succ n =>
        simpa only [recover, prependPrefix, beforeAnswers, List.take_succ_cons] using
          congrArg (List.cons (.answer q answer.answer)) (ih answer.answer rest n)
  | commit root next ih =>
    simpa only [recover, prependPrefix, beforeAnswers] using
      congrArg (List.cons (.commit root)) (ih answers n)
  | claims profile entry request next ih =>
    simpa only [recover, prependPrefix, beforeAnswers] using
      congrArg (List.cons (.claims profile entry request)) (ih answers n)

theorem beforeAnswers_ideal_prefix {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State) (p : Source cap R)
    (remaining : Nat) (limit : remaining ≤ Q) (counted : Counts remaining p)
    (seen : List Observation)
    (prior : seen.IsPrefix (runIdeal sim ro iv state (compile p) remaining limit
      ((compile_counted p remaining).mpr counted)).view.observations) :
    beforeAnswers seen.length (runIdeal sim ro iv state (compile p) remaining limit
      ((compile_counted p remaining).mpr counted)).view.result.events = (recover p seen).events := by
  have take : (runIdeal sim ro iv state (compile p) remaining limit
      ((compile_counted p remaining).mpr counted)).view.observations.take seen.length = seen := by
    obtain ⟨rest,eq⟩ := prior
    rw [← eq]
    simp
  have recovered := congrArg Prefix.events (recover_ideal sim ro iv state p remaining limit counted)
  have cut := beforeAnswers_recover p (runIdeal sim ro iv state (compile p) remaining limit
    ((compile_counted p remaining).mpr counted)).view.observations seen.length
  rw [recovered,take] at cut
  exact cut

end Whir.WHIRSourceChronology
