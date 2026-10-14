import Whir.WHIRSourceRawCache
import Whir.WHIRHeaderRoots
import Whir.WHIRCausalRawROM

namespace Whir.WHIRSourceResolver
open FiatShamirGame DuplexModeGame RawOracleCoupling.Concrete
open WHIRSourceChronology WHIRSourceObserver WHIRCallerRegistry

variable {cap : Nat} {R : Type}

/-- Source observations are recovered from the compiler-owned public result. This discards completion-only queries without inspecting the source program, its coins, or a total oracle. -/
def sourceView (result : Result cap R) : View (Result cap R) :=
  ⟨observations result.events,result⟩

theorem ideal_source_trace {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State)
    (source : Source cap R) (remaining : Nat) (limit : remaining ≤ Q)
    (counted : Counts remaining source) :
    observations (runIdeal sim ro iv state (compile source) remaining limit
      ((compile_counted source remaining).mpr counted)).view.result.events =
      (runIdeal sim ro iv state (compile source) remaining limit
        ((compile_counted source remaining).mpr counted)).view.observations := by
  induction source generalizing state remaining with
  | done => rfl
  | ask query next ih =>
      cases query with
      | primitive purpose input =>
          let answer := runRO ro (sim.answer state input)
          have mapped := map_ideal sim ro iv answer.1.1
            (prepend (.answer (.primitive purpose input) answer.1.2))
            (compile (next answer.1.2)) (remaining-1) (by omega)
            ((compile_counted _ _).mpr (counted.2 answer.1.2))
          have whole : runIdeal sim ro iv state (compile (.ask (.primitive purpose input) next))
              remaining limit ((compile_counted _ _).mpr counted) = _ :=
            congrArg (DuplexModeGame.prepend (.primitive purpose input) answer.1.2 answer.2) mapped
          rw [whole]
          simpa only [mapExecution, DuplexModeGame.prepend, WHIRSourceChronology.prepend, observations] using
            congrArg (List.cons ⟨.primitive purpose input,answer.1.2⟩)
              (ih answer.1.2 answer.1.1 (remaining-1) (by omega) (counted.2 answer.1.2))
      | construction coordinate valid =>
          let answer := ro (constructionKey Q iv coordinate (counted.1.trans limit))
          have mapped := map_ideal sim ro iv state
            (prepend (.answer (.construction coordinate valid) answer))
            (compile (next answer)) (remaining-DuplexFraming.pathCost coordinate) (by omega)
            ((compile_counted _ _).mpr (counted.2 answer))
          have whole : runIdeal sim ro iv state (compile (.ask (.construction coordinate valid) next))
              remaining limit ((compile_counted _ _).mpr counted) = _ :=
            congrArg (DuplexModeGame.prepend (.construction coordinate valid) answer 0) mapped
          rw [whole]
          simpa only [mapExecution, DuplexModeGame.prepend, WHIRSourceChronology.prepend, observations] using
            congrArg (List.cons ⟨.construction coordinate valid,answer⟩)
              (ih answer state (remaining-DuplexFraming.pathCost coordinate) (by omega) (counted.2 answer))
  | commit root next ih =>
      have mapped := map_ideal sim ro iv state (prepend (.commit root)) (compile next)
        remaining limit ((compile_counted _ _).mpr counted)
      have whole : runIdeal sim ro iv state (compile (.commit root next))
          remaining limit ((compile_counted _ _).mpr counted) = _ := mapped
      rw [whole]
      simpa only [mapExecution, WHIRSourceChronology.prepend, observations] using ih state remaining limit counted
  | claims profile entry request next ih =>
      have mapped := map_ideal sim ro iv state (prepend (.claims profile entry request)) (compile next)
        remaining limit ((compile_counted _ _).mpr counted)
      have whole : runIdeal sim ro iv state (compile (.claims profile entry request next))
          remaining limit ((compile_counted _ _).mpr counted) = _ := mapped
      rw [whole]
      simpa only [mapExecution, WHIRSourceChronology.prepend, observations] using ih state remaining limit counted

theorem sourceView_ideal {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State)
    (source : Source cap R) (remaining : Nat) (limit : remaining ≤ Q)
    (counted : Counts remaining source) :
    sourceView (runIdeal sim ro iv state (compile source) remaining limit
      ((compile_counted source remaining).mpr counted)).view.result =
      (runIdeal sim ro iv state (compile source) remaining limit
        ((compile_counted source remaining).mpr counted)).view := by
  unfold sourceView
  rw [ideal_source_trace sim ro iv state source remaining limit counted]

theorem sourceView_real (oracle : PrimitiveOracle) (iv : Digest32) (source : Source cap R) :
    sourceView (runReal oracle iv (compile source)).view.result =
      (runReal oracle iv (compile source)).view := by
  unfold sourceView
  rw [real_source_trace]

/-- A header seen by a direct prequery captures its root before that allocation's answer, even if the native source has not reached its own announcement yet. -/
def publicBefore (registry : Public) (Q : Nat) (result : Result cap R)
    (state : CausalBindingState.State cap) (key : AllocationKey (context registry) Q) :
    WHIRCausalRawROM.Extension state :=
  let prior := publicReplay Q registry.iv (WHIRSourceRawCache.cache Q state) (sourceView result) state
  ⟨CausalBindingState.registerRoots prior (WHIRHeaderRoots.allocationRoots registry Q key),
    (publicReplay_extends ..).trans (CausalBindingState.registerRoots_extends ..)⟩

def privateBefore (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) (key : AllocationKey (context registry) Q) :
    WHIRCausalRawROM.Extension state :=
  let prior := privateReplay Q registry.iv (WHIRSourceRawCache.cache Q state) seed source counted state
  ⟨CausalBindingState.registerRoots prior (WHIRHeaderRoots.allocationRoots registry Q key),
    (privateReplay_extends ..).trans (CausalBindingState.registerRoots_extends ..)⟩

def after (registry : Public) (Q : Nat) (state : CausalBindingState.State cap)
    (key : AllocationKey (context registry) Q) (answer : AllocationAnswer (context registry) Q key) :
    WHIRCausalRawROM.Extension state :=
  ⟨WHIRSourceRawCache.addGroup (context registry) Q state key.1 answer,
    WHIRSourceRawCache.addGroup_extends ..⟩

noncomputable def publicResolver (registry : Public) (Q : Nat) (result : Result cap R) :
    WHIRCausalRawROM.Resolver (context registry) Q cap where
  before := publicBefore registry Q result
  claims _ packet history := packetRequest registry Q cap packet history
  after := after registry Q

noncomputable def privateResolver (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : Counts Q source) :
    WHIRCausalRawROM.Resolver (context registry) Q cap where
  before := privateBefore registry Q seed source counted
  claims _ packet history := packetRequest registry Q cap packet history
  after := after registry Q

theorem publicBefore_actual (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap)
    (agrees : WHIRSourceRawCache.LogAgrees ro (state.rawAnswers Q))
    (key : AllocationKey (context registry) Q) :
    publicBefore registry Q (runIdeal (DuplexPublicSimulator.simulator Q) ro registry.iv
      ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
      ((compile_counted source Q).mpr counted)).view.result state key =
      privateBefore registry Q seed source counted state key := by
  unfold publicBefore privateBefore
  simp only [sourceView_ideal (DuplexPublicSimulator.simulator Q) ro registry.iv
    ((DuplexPublicSimulator.simulator Q).initial seed) source Q (by omega) counted]
  have cacheAgrees := WHIRSourceRawCache.lookup_agrees Q ro (state.rawAnswers Q) agrees
  change DuplexPublicSimulator.CacheAgrees (WHIRSourceRawCache.cache Q state) ro at cacheAgrees
  simp only [publicReplay_actual Q registry.iv _ ro cacheAgrees seed source counted]

@[simp] theorem privateBefore_raw (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) (key : AllocationKey (context registry) Q) :
    (privateBefore registry Q seed source counted state key).state.rawAnswers = state.rawAnswers := by
  simp [privateBefore, privateReplay, WHIRSourceRawCache.registerRoots_raw,
    WHIRSourceRawCache.replayTracked_raw]

@[simp] theorem publicBefore_raw (registry : Public) (Q : Nat) (result : Result cap R)
    (state : CausalBindingState.State cap) (key : AllocationKey (context registry) Q) :
    (publicBefore registry Q result state key).state.rawAnswers = state.rawAnswers := by
  simp [publicBefore, publicReplay, WHIRSourceRawCache.registerRoots_raw,
    WHIRSourceRawCache.replayTracked_raw]

/-- The public resolver cannot inspect an arbitrary returned payload, including a hidden program or coin object: only compiler-owned events affect it. -/
theorem publicResolver_events_only {S : Type} (registry : Public) (Q : Nat)
    (left : Result cap R) (right : Result cap S) (same : left.events = right.events) :
    publicResolver registry Q left = publicResolver registry Q right := by
  cases left
  cases right
  cases same
  rfl

theorem privatePrepare_raw (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap) (key : AllocationKey (context registry) Q) :
    (WHIRCausalRawROM.prepare (context registry) rfl Q cap
      (privateResolver registry Q seed source counted) state key).1.rawAnswers = state.rawAnswers := by
  rcases key with ⟨group,history⟩
  cases group with
  | inl packet =>
      exact (WHIRSourceRawCache.prepareClaims_raw _ _ _ _ _).trans
        (privateBefore_raw registry Q seed source counted state (.inl packet,history))
  | inr raw =>
      exact privateBefore_raw registry Q seed source counted state (.inr raw,history)

theorem prepare_actual (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap)
    (agrees : WHIRSourceRawCache.LogAgrees ro (state.rawAnswers Q))
    (key : AllocationKey (context registry) Q) :
    WHIRCausalRawROM.prepare (context registry) rfl Q cap
      (publicResolver registry Q (runIdeal (DuplexPublicSimulator.simulator Q) ro registry.iv
        ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
        ((compile_counted source Q).mpr counted)).view.result) state key =
    WHIRCausalRawROM.prepare (context registry) rfl Q cap
      (privateResolver registry Q seed source counted) state key := by
  rcases key with ⟨group,history⟩
  cases group <;>
    simp only [WHIRCausalRawROM.prepare, publicResolver, privateResolver,
      publicBefore_actual registry Q ro seed source counted state agrees]

def TraceAgrees (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (trace : List (Sigma (AllocationAnswer (context registry) Q))) : Prop :=
  ∀ item ∈ trace, item.2 = (partition (context registry) Q).split ro item.1.1

private noncomputable def emitted (registry : Public) (Q : Nat)
    (resolver : WHIRCausalRawROM.Resolver (context registry) Q cap)
    (state : CausalBindingState.State cap) (key : AllocationKey (context registry) Q)
    (answer : AllocationAnswer (context registry) Q key) :
    Sigma (@WHIRCausalRawROM.Answer (context registry) rfl Q cap) :=
  ⟨(WHIRCausalRawROM.prepare (context registry) rfl Q cap resolver state key).2,
    (WHIRCausalRawROM.decorator (context registry) rfl Q cap resolver).answer state key answer⟩

private theorem recode_cons (registry : Public) (Q : Nat)
    (resolver : WHIRCausalRawROM.Resolver (context registry) Q cap)
    (state : CausalBindingState.State cap) (key : AllocationKey (context registry) Q)
    (answer : AllocationAnswer (context registry) Q key)
    (rest : List (Sigma (AllocationAnswer (context registry) Q))) :
    (WHIRCausalRawROM.decorator (context registry) rfl Q cap resolver).traceRecode
      state (⟨key,answer⟩ :: rest) =
      let next := (resolver.after
        (WHIRCausalRawROM.prepare (context registry) rfl Q cap resolver state key).1 key answer).state
      let result := (WHIRCausalRawROM.decorator (context registry) rfl Q cap resolver).traceRecode next rest
      (emitted registry Q resolver state key answer :: result.1,result.2) := by
  rcases key with ⟨group,history⟩
  cases group <;> rfl

private theorem emitted_actual (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap)
    (agrees : WHIRSourceRawCache.LogAgrees ro (state.rawAnswers Q))
    (key : AllocationKey (context registry) Q) (answer : AllocationAnswer (context registry) Q key) :
    emitted registry Q
      (publicResolver registry Q (runIdeal (DuplexPublicSimulator.simulator Q) ro registry.iv
        ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
        ((compile_counted source Q).mpr counted)).view.result) state key answer =
    emitted registry Q (privateResolver registry Q seed source counted) state key answer := by
  apply Sigma.ext
  · exact congrArg Prod.snd (prepare_actual registry Q ro seed source counted state agrees key)
  · rcases key with ⟨group,history⟩
    cases group <;> rfl

private theorem publicResolver_after (registry : Public) (Q : Nat) (result : Result cap R) :
    (publicResolver registry Q result).after = after registry Q := rfl

private theorem privateResolver_after (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : Counts Q source) :
    (privateResolver registry Q seed source counted).after = after registry Q := rfl

theorem traceRecode_actual (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (state : CausalBindingState.State cap)
    (agrees : WHIRSourceRawCache.LogAgrees ro (state.rawAnswers Q))
    (trace : List (Sigma (AllocationAnswer (context registry) Q)))
    (answers : TraceAgrees registry Q ro trace) :
    (WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (publicResolver registry Q (runIdeal (DuplexPublicSimulator.simulator Q) ro registry.iv
        ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (by omega)
        ((compile_counted source Q).mpr counted)).view.result)).traceRecode state trace =
    (WHIRCausalRawROM.decorator (context registry) rfl Q cap
      (privateResolver registry Q seed source counted)).traceRecode state trace := by
  induction trace generalizing state with
  | nil => rfl
  | cons item rest ih =>
      rcases item with ⟨key,answer⟩
      have head := answers ⟨key,answer⟩ (by simp)
      change answer = (partition (context registry) Q).split ro key.1 at head
      have tail : TraceAgrees registry Q ro rest :=
        fun item member => answers item (List.mem_cons_of_mem _ member)
      let prepared := (WHIRCausalRawROM.prepare (context registry) rfl Q cap
        (privateResolver registry Q seed source counted) state key).1
      have prior : WHIRSourceRawCache.LogAgrees ro (prepared.rawAnswers Q) := by
        simpa only [prepared,privatePrepare_raw] using agrees
      have next : WHIRSourceRawCache.LogAgrees ro
          ((after registry Q prepared key answer).state.rawAnswers Q) := by
        change WHIRSourceRawCache.LogAgrees ro
          ((WHIRSourceRawCache.addGroup (context registry) Q prepared key.1 answer).rawAnswers Q)
        rw [head]
        exact WHIRSourceRawCache.addGroup_agrees (context registry) Q ro prepared prior key.1
      have recursive := ih (after registry Q prepared key answer).state next tail
      have nextEqual := congrArg
        (fun built => (after registry Q built.1 key answer).state)
        (prepare_actual registry Q ro seed source counted state agrees key)
      simp only [recode_cons, publicResolver_after, privateResolver_after,
        emitted_actual registry Q ro seed source counted state agrees key answer,
        nextEqual]
      exact congrArg
        (fun result => (emitted registry Q (privateResolver registry Q seed source counted)
          state key answer :: result.1,result.2)) recursive

end Whir.WHIRSourceResolver
