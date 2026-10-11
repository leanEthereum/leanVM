import Whir.WHIRRawROM
import Whir.CausalBindingState
import Whir.CausalAllocationLabels

namespace Whir.WHIRCausalRawROM
open Concrete Protocol CausalProbability ParameterBounds
open FiatShamirGame (Digest32 average)
open RawOracleCoupling RawOracleCoupling.Concrete WHIRRawReplay
open Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

structure Extension {cap : Nat} (before : CausalBindingState.State cap) where
  state : CausalBindingState.State cap
  growth : CausalBindingState.Extends before state

/-- The resolver sees only the already accumulated finite state and current
raw-input prefix. It has no total oracle argument. Its claim request is formed
before sampling; immutable registration handles repeats and earlier prequeries. -/
structure Resolver (ctx : RawWHIRKeys.Context) (Q cap : Nat) where
  before : (state : CausalBindingState.State cap) → AllocationKey ctx Q → Extension state
  claims : CausalBindingState.State cap → (packet : RawWHIRKeys.Packet ctx Q) →
    List (Sigma (GroupAnswer ctx Q)) → Option (CausalBindingState.ClaimRequest cap packet.val.profile)
  after : (state : CausalBindingState.State cap) → (key : AllocationKey ctx Q) →
    AllocationAnswer ctx Q key → Extension state

inductive Label (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat) where
  | packet (packet : RawWHIRKeys.Packet ctx Q) (history : List (Sigma (GroupAnswer ctx Q)))
      (binding : CausalBindingState.Label cap packet.val.profile)
      (key : binding.key = localKey (allocationKey ctx stack Q packet history))
      (entry : binding.entry = callerEntry ctx Q packet)
  | garbage (key : (partition ctx Q).Garbage) (history : List (Sigma (GroupAnswer ctx Q)))
      (state : CausalBindingState.State cap)

def Label.allocation {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat} :
    Label ctx stack Q cap → AllocationKey ctx Q
  | .packet pkt history _ _ _ => (.inl pkt,history)
  | .garbage key history _ => (.inr key,history)

def Label.state {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat} :
    Label ctx stack Q cap → CausalBindingState.State cap
  | .packet _ _ binding _ _ => binding.state
  | .garbage _ _ state => state

abbrev Answer {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (label : Label ctx stack Q cap) := AllocationAnswer ctx Q label.allocation

noncomputable def prepare (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (resolver : Resolver ctx Q cap) (state : CausalBindingState.State cap) :
    (key : AllocationKey ctx Q) → CausalBindingState.State cap × Label ctx stack Q cap
  | (.inl packet,history) =>
    let prior := (resolver.before state (.inl packet,history)).state
    let built := CausalBindingState.prepareClaims prior packet.val.profile (callerEntry ctx Q packet)
      (localKey (allocationKey ctx stack Q packet history)) (resolver.claims prior packet history)
    (built.1,.packet packet history built.2
      (CausalBindingState.prepareClaims_key _ _ _ _ _)
      (CausalBindingState.prepareClaims_entry _ _ _ _ _))
  | (.inr key,history) =>
    let prior := (resolver.before state (.inr key,history)).state
    (prior,.garbage key history prior)

@[simp] theorem prepare_allocation (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (state : CausalBindingState.State cap)
    (key : AllocationKey ctx Q) : (prepare ctx stack Q cap resolver state key).2.allocation = key := by
  rcases key with ⟨key,history⟩
  cases key <;> rfl

@[simp] theorem prepare_state (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (state : CausalBindingState.State cap)
    (key : AllocationKey ctx Q) :
    (prepare ctx stack Q cap resolver state key).2.state = (prepare ctx stack Q cap resolver state key).1 := by
  rcases key with ⟨key,history⟩
  cases key with
  | inl packet => exact CausalBindingState.prepareClaims_state _ _ _ _ _
  | inr garbage => rfl

theorem prepare_extends (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (state : CausalBindingState.State cap)
    (key : AllocationKey ctx Q) :
    CausalBindingState.Extends state (prepare ctx stack Q cap resolver state key).1 := by
  rcases key with ⟨key,history⟩
  cases key with
  | inl packet =>
    exact (resolver.before state (.inl packet,history)).growth.trans
      (CausalBindingState.prepareClaims_extends _ _ _ _ _)
  | inr garbage => exact (resolver.before state (.inr garbage,history)).growth

noncomputable def decorator (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (resolver : Resolver ctx Q cap) :
    CausalAllocationLabels.Decorator (CausalBindingState.State cap)
      (AllocationKey ctx Q) (AllocationAnswer ctx Q) (Label ctx stack Q cap) Answer where
  prepare := prepare ctx stack Q cap resolver
  answer state key := by
    rcases key with ⟨key,history⟩
    cases key <;> exact Equiv.refl _
  advance state label answer := (resolver.after state label.allocation answer).state

def Label.bad {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (label : Label ctx stack Q cap) (answer : Answer label) : Prop :=
  WHIRRawROM.bad ctx stack Q cap label.state.catalog (CausalBindingState.roots label.state)
    label.allocation answer

theorem evolution_extends (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap)
    {state final : CausalBindingState.State cap} {raw labeled}
    (evolution : (decorator ctx stack Q cap resolver).Evolves state raw labeled final) :
    CausalBindingState.Extends state final := by
  induction evolution with
  | nil => exact .refl _
  | cons state key answer tail ih =>
    exact (prepare_extends ctx stack Q cap resolver state key).trans
      ((resolver.after _ _ _).growth.trans ih)

theorem emitted_state_extends (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap)
    {state final : CausalBindingState.State cap} {raw labeled}
    (evolution : (decorator ctx stack Q cap resolver).Evolves state raw labeled final)
    (entry : Sigma (@Answer ctx stack Q cap)) (member : entry ∈ labeled) :
    CausalBindingState.Extends entry.1.state final := by
  induction evolution with
  | nil => simp at member
  | cons state key answer tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst entry
      change CausalBindingState.Extends (prepare ctx stack Q cap resolver state key).2.state _
      rw [prepare_state]
      exact (resolver.after _ _ _).growth.trans
        (evolution_extends ctx stack Q cap resolver tail)
    · exact ih member

def eraseEntry {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (entry : Sigma (@Answer ctx stack Q cap)) : Sigma (AllocationAnswer ctx Q) :=
  ⟨entry.1.allocation,entry.2⟩

@[simp] theorem erase_prepared (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (state : CausalBindingState.State cap)
    (key : AllocationKey ctx Q) (answer : AllocationAnswer ctx Q key) :
    eraseEntry ⟨(prepare ctx stack Q cap resolver state key).2,
      (decorator ctx stack Q cap resolver).answer state key answer⟩ = ⟨key,answer⟩ := by
  rcases key with ⟨key,history⟩
  cases key <;> rfl

theorem evolution_erases (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap)
    {state final : CausalBindingState.State cap} {raw labeled}
    (evolution : (decorator ctx stack Q cap resolver).Evolves state raw labeled final) :
    labeled.map eraseEntry = raw := by
  induction evolution with
  | nil => rfl
  | cons state key answer tail ih =>
    rw [List.map_cons,ih]
    congr 1
    exact erase_prepared ctx stack Q cap resolver state key answer

theorem Label.sparse {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (label : Label ctx stack Q cap) :
    average (fun answer => if label.bad answer then 1 else 0) ≤ WHIRRawROM.epsilon cap :=
  WHIRRawROM.sparse ctx stack Q cap label.state.catalog (CausalBindingState.roots label.state) _

theorem Label.bad_final {ctx : RawWHIRKeys.Context} {stack : ctx.mode = .stack} {Q cap : Nat}
    (label : Label ctx stack Q cap) (final : CausalBindingState.State cap)
    (growth : CausalBindingState.Extends label.state final) (answer : Answer label) :
    label.bad answer ↔
      WHIRRawROM.bad ctx stack Q cap final.catalog (CausalBindingState.roots final)
        label.allocation answer := by
  cases label with
  | garbage key history state => rfl
  | packet packet history binding key entry =>
    rcases binding with ⟨state,entered,logical,original,found,prepared⟩
    dsimp only at key entry
    subst logical
    subst entered
    exact CausalBindingState.Label.bad_final
      ⟨state,callerEntry ctx Q packet,localKey (allocationKey ctx stack Q packet history),
        original,found,prepared⟩ final growth (decodePacket ctx stack Q packet answer)

theorem compiler_cover (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q cap : Nat)
    (resolver : Resolver ctx Q cap) (initial : CausalBindingState.State cap) {R : Type} {K : Nat}
    (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K)
    (trace result final)
    (run : TypedOracleCompiler.Sampling.Runs
      ((decorator ctx stack Q cap resolver).decorate (compile ctx Q select program) initial)
      trace (result,final))
    (failed : WHIRRawROM.Failure ctx stack Q cap final.catalog (CausalBindingState.roots final)
      (select result.1) result.2) :
    ∃ entry ∈ trace, entry.1.bad entry.2 := by
  obtain ⟨raw,original,evolution⟩ :=
    (decorator ctx stack Q cap resolver).runs_causal _ initial run
  obtain ⟨allocation,member,bad⟩ := WHIRRawROM.compiler_cover ctx stack Q cap
    final.catalog (CausalBindingState.roots final) select program raw result original failed
  have mapped : allocation ∈ trace.map eraseEntry := by
    rw [evolution_erases ctx stack Q cap resolver evolution]
    exact member
  obtain ⟨entry,inTrace,equal⟩ := List.mem_map.mp mapped
  refine ⟨entry,inTrace,(entry.1.bad_final final
    (emitted_state_extends ctx stack Q cap resolver evolution entry inTrace) entry.2).mpr ?_⟩
  cases equal
  exact bad

/-- Each event uses its retained pre-draw snapshot. Final-state catalogs may
depend on all preceding answers; they are used only for deterministic replay,
never substituted into a fresh-sample probability bound. -/
theorem allocation_list_binding (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (initial : CausalBindingState.State cap)
    {R : Type} {K : Nat} (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K) :
    TypedOracleCompiler.Sampling.failureProbability
      (fun result => WHIRRawROM.Failure ctx stack Q cap result.2.catalog
        (CausalBindingState.roots result.2) (select result.1.1) result.1.2)
      ((decorator ctx stack Q cap resolver).decorate (compile ctx Q select program) initial) ≤
        min 1 (((allocationBudget ctx * (K+1) : Nat) : ℚ) * WHIRRawROM.epsilon cap) := by
  apply le_min
  · apply TypedOracleCompiler.Sampling.expectation_le_one
    intro result
    split <;> norm_num
  · have cover := TypedOracleCompiler.Sampling.failure_le_risk
      (fun label answer => label.bad answer)
      (fun result => WHIRRawROM.Failure ctx stack Q cap result.2.catalog
        (CausalBindingState.roots result.2) (select result.1.1) result.1.2)
      ((decorator ctx stack Q cap resolver).decorate (compile ctx Q select program) initial)
      (by
        intro trace result run failed
        exact compiler_cover ctx stack Q cap resolver initial select program
          trace result.1 result.2 run failed)
    have bounded := TypedFiatShamirGame.risk_bound
      (fun label answer => label.bad answer) (WHIRRawROM.epsilon cap)
      (WHIRRawROM.epsilon_nonneg cap) Label.sparse
      (TypedOracleCompiler.Sampling.erase
        ((decorator ctx stack Q cap resolver).decorate (compile ctx Q select program) initial))
    simpa only [Nat.mul_add,Nat.mul_one] using cover.trans bounded

private theorem expectation_eq_of_runs {Key : Type} {A : Key → Type} {R : Type}
    [∀ key, Fintype (A key)] {n : Nat}
    (program : TypedOracleCompiler.Sampling Key A R n) (left right : R → ℚ)
    (agree : ∀ trace result, TypedOracleCompiler.Sampling.Runs program trace result →
      left result = right result) :
    TypedOracleCompiler.Sampling.expectation left program =
      TypedOracleCompiler.Sampling.expectation right program := by
  induction program with
  | ret result => exact agree [] result (.ret result)
  | draw key next ih =>
    apply congrArg average
    funext answer
    apply ih answer
    intro trace result run
    exact agree (⟨key,answer⟩ :: trace) result (.draw answer run)

/-- Replay recovers the original chronological labels from the immutable
completed cache. The cache is not supplied to label preparation: each step
still sees only the prefix state and its already completed dependencies. -/
noncomputable def stateOfResult (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (initial : CausalBindingState.State cap)
    {R : Type} {K : Nat} (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K)
    (result : R × TypedFiatShamirGame.Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) :
    CausalBindingState.State cap :=
  ((decorator ctx stack Q cap resolver).traceRecode initial
    (TypedOracleCompiler.Sampling.execute (cacheOracle ctx Q result.2)
      (compile ctx Q select program)).2).2

theorem stateOfResult_exact (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (initial : CausalBindingState.State cap)
    {R : Type} {K : Nat} (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K)
    {trace result final}
    (run : TypedOracleCompiler.Sampling.Runs
      ((decorator ctx stack Q cap resolver).decorate (compile ctx Q select program) initial)
      trace (result,final)) :
    stateOfResult ctx stack Q cap resolver initial select program result = final := by
  obtain ⟨raw,original,evolution⟩ :=
    (decorator ctx stack Q cap resolver).runs_causal _ initial run
  unfold stateOfResult
  rw [compile_reconstruct ctx Q select program original]
  exact congrArg Prod.snd evolution.exact

theorem decorated_distribution (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (initial : CausalBindingState.State cap)
    {R : Type} {K : Nat} (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K)
    (payoff : (R × TypedFiatShamirGame.Cache (GroupKey ctx Q) (GroupAnswer ctx Q)) ×
      CausalBindingState.State cap → ℚ) :
    TypedOracleCompiler.Sampling.expectation payoff
      ((decorator ctx stack Q cap resolver).decorate (compile ctx Q select program) initial) =
    TypedOracleCompiler.Sampling.expectation
      (fun result => payoff (result,stateOfResult ctx stack Q cap resolver initial select program result))
      (compile ctx Q select program) := by
  calc
    _ = TypedOracleCompiler.Sampling.expectation
      (fun result => payoff (result.1,stateOfResult ctx stack Q cap resolver initial select program result.1))
      ((decorator ctx stack Q cap resolver).decorate (compile ctx Q select program) initial) := by
        apply expectation_eq_of_runs
        intro trace result run
        rw [stateOfResult_exact ctx stack Q cap resolver initial select program run]
    _ = _ := (decorator ctx stack Q cap resolver).expectation (compile ctx Q select program) initial
      (fun result => payoff (result,stateOfResult ctx stack Q cap resolver initial select program result))

private instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
private noncomputable instance : Fintype UInt64 := Fintype.ofFinite _

theorem raw_table_list_binding (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack)
    (Q cap : Nat) (resolver : Resolver ctx Q cap) (initial : CausalBindingState.State cap)
    {R : Type} {K : Nat} (select : R → Option (RawWHIRKeys.Packet ctx Q))
    (program : TypedOracleCompiler.Sampling (DuplexModeGame.RawKey Q) (fun _ => Digest32) R K) :
    average (fun table : DuplexModeGame.RawKey Q → Digest32 =>
      let result := tableExecution ctx Q select program table
      let final := stateOfResult ctx stack Q cap resolver initial select program result
      if WHIRRawROM.Failure ctx stack Q cap final.catalog (CausalBindingState.roots final)
        (select result.1) result.2 then 1 else 0) ≤
      min 1 (((allocationBudget ctx * (K+1) : Nat) : ℚ) * WHIRRawROM.epsilon cap) := by
  rw [distribution_full ctx Q select program
    (fun result =>
      let final := stateOfResult ctx stack Q cap resolver initial select program result
      if WHIRRawROM.Failure ctx stack Q cap final.catalog (CausalBindingState.roots final)
        (select result.1) result.2 then 1 else 0)]
  rw [← decorated_distribution ctx stack Q cap resolver initial select program
    (fun result => if WHIRRawROM.Failure ctx stack Q cap result.2.catalog
      (CausalBindingState.roots result.2) (select result.1.1) result.1.2 then 1 else 0)]
  exact allocation_list_binding ctx stack Q cap resolver initial select program

end Whir.WHIRCausalRawROM
