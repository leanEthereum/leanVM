import Whir.StackWHIRReplay

/-! Checked ordinary-ROM list binding for actual stacked openings. The initial
allocation is the full gamma, six-map, lambda vector. The commitment-time K
list concerns original family slices and points, not an assumed transformed
statement. The physical compression-mode transfer is deliberately separate. -/
namespace Whir.StackWHIRROM
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open FiatShamirGame (Digest32 average average_const)
open WHIRFiatShamir
open StackWHIRReplay (Key Answer Catalog Roots query projectSample)
open Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev Machine (p : Profile) (B K : Nat) :=
  TypedOracleCompiler.Machine Digest32 WHIRHistory.Pending
    (@StackWHIRReplay.Sample (config p)) B K
abbrev TerminalView (p : Profile) (B : Nat) :=
  TypedOracleCompiler.Terminal (A := @StackWHIRReplay.Sample (config p)) (query p) B

def initialAnswer {c : Config} {q : Coordinate c} (h : q = .initial)
    (x : StackWHIRReplay.Sample q) : RingPCSGame.Prefix × E :=
  cast (congrArg StackWHIRReplay.Sample h) x

theorem initial_average {c : Config} {q : Coordinate c} (h : q = .initial)
    (f : RingPCSGame.Prefix × E → ℚ) :
    average (fun x : StackWHIRReplay.Sample q => f (initialAnswer h x)) = average f := by
  subst q
  rfl

theorem later_average {c : Config} (q : Coordinate c) (h : q ≠ .initial)
    (f : Sample q → ℚ) :
    average (fun x : StackWHIRReplay.Sample q => f (projectSample q x)) = average f := by
  cases q with
  | initial => exact (h rfl).elim
  | fold i j => rfl
  | ood i j => rfl
  | query i => rfl
  | tail j => rfl

theorem seedValue_initial {c : Config} {q : Coordinate c} (h : q = .initial)
    (x : StackWHIRReplay.Sample q) :
    StackWHIRReplay.seedValue ⟨q,x⟩ = some (initialAnswer h x) := by
  subst q
  rfl

/-- A malformed key has no algebraic bad event. Rejection does not bypass its
compiler allocation cost. The initial sample uses the original frozen family. -/
def keyBad (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) (x : Answer p key) : Prop :=
  if h : query p (key.statement,key.messages) = .initial then
    match StackWHIRReplay.decodeInitial p cap catalog key with
    | none => False
    | some data => RingPCSGame.InitialEvent p data.lanes data.root data.family data.points
        (initialAnswer h x)
  else
    match StackWHIRReplay.decode p cap catalog roots key with
    | none => False
    | some replay => allocationBad (WHIRReplay.request (StackWHIRReplay.projectKey key) replay.whir)
        (projectSample _ x)

theorem stackEta_nonneg (p : Profile) (cap : Nat) : 0 ≤ stackEta p cap :=
  add_nonneg (eta_nonneg p) (ringCharge_nonneg cap)

theorem key_sparse (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    (key : Key p) :
    average (fun x => if keyBad p cap catalog roots key x then 1 else 0) ≤ stackEta p cap := by
  by_cases h : query p (key.statement,key.messages) = .initial
  · simp only [keyBad,dite_eq_left h]
    cases decoded : StackWHIRReplay.decodeInitial p cap catalog key with
    | none => simp only [↓reduceIte,average_const]; exact stackEta_nonneg p cap
    | some data =>
      change average (fun x : StackWHIRReplay.Sample (query p (key.statement,key.messages)) =>
        if RingPCSGame.InitialEvent p data.lanes data.root data.family data.points
          (initialAnswer h x) then 1 else 0) ≤ stackEta p cap
      exact (initial_average h (fun z =>
        if RingPCSGame.InitialEvent p data.lanes data.root data.family data.points z then 1 else 0)).trans_le
          (stack_sparse p cap (.initial data))
  · simp only [keyBad,dite_eq_right h]
    cases decoded : StackWHIRReplay.decode p cap catalog roots key with
    | none => simp only [↓reduceIte,average_const]; exact stackEta_nonneg p cap
    | some replay =>
      change average (fun x : StackWHIRReplay.Sample (query p (key.statement,key.messages)) =>
        if allocationBad (WHIRReplay.request (StackWHIRReplay.projectKey key) replay.whir)
          (projectSample (query p (key.statement,key.messages)) x) then 1 else 0) ≤ stackEta p cap
      exact (later_average _ h (fun z =>
        if allocationBad (WHIRReplay.request (StackWHIRReplay.projectKey key) replay.whir) z
          then 1 else 0)).trans_le
            (stack_sparse p cap (.later (WHIRReplay.request (StackWHIRReplay.projectKey key) replay.whir) h))

/-- Failure refers to the actual causal verifier and the original commitment's
fixed K-witness list. The ring-transformed statement is produced by decoding. -/
def FalseOpening {p : Profile} {cap : Nat} (r : StackWHIRReplay.Replay p cap) : Prop :=
  experiment r.whir.statement.input (CausalStrategy.indexedStrategy r.whir.replies) r.whir.tape = true ∧
  ¬ ∃ w ∈ InitialCandidates.witnesses (config p) r.original.lanes r.original.root,
    RingPCSGame.Honest (config p) r.original.lanes r.original.family r.original.points w

def HistoryFailure (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    (statement : Digest32) (messages : List WHIRHistory.Pending)
    (history : List (WHIRHistory.Pending × Sigma (@StackWHIRReplay.Sample (config p)))) : Prop :=
  ∃ head past, ∃ x : StackWHIRReplay.Sample (query p (statement,messages)),
    ∃ replay : StackWHIRReplay.Replay p cap,
      history = (head,⟨query p (statement,messages),x⟩)::past ∧
      messages.length = WHIRHistory.depth (config p) ∧
      StackWHIRReplay.decode p cap catalog roots ⟨statement,messages,past⟩ = some replay ∧
      FalseOpening (StackWHIRReplay.finish ⟨statement,messages,past⟩ replay x)

def TerminalFailure (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    {B : Nat} (result : TerminalView p B) : Prop :=
  HistoryFailure p cap catalog roots result.request.statement result.request.messages
    result.allocation.history

/-- Actual terminal failure is covered by an actual allocated vector. Initial
ring escape and initial lambda escape share one trace entry and one draw. -/
theorem recorded_history_cover (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    (statement : Digest32) (messages : List WHIRHistory.Pending)
    (completed : List (WHIRHistory.Pending × Sigma (@StackWHIRReplay.Sample (config p))))
    (trace : List (Sigma (Answer p)))
    (recorded : TypedOracleCompiler.HistoryRecorded (query p) statement trace messages completed)
    (failed : HistoryFailure p cap catalog roots statement messages completed) :
    ∃ ka ∈ trace, keyBad p cap catalog roots ka.1 ka.2 := by
  obtain ⟨head,past,x,replay,history,length,decoded,failed⟩ := failed
  let key : Key p := ⟨statement,messages,past⟩
  let final := StackWHIRReplay.finish key replay x
  change FalseOpening final at failed
  rw [history] at recorded
  obtain initial | later := StackWHIRReplay.accepted_false_cover catalog roots key replay decoded x
    failed.1 failed.2
  · obtain ⟨m,a,allocated,parsed,seed⟩ := StackWHIRReplay.initial_trace_realization
      catalog roots key replay decoded x head trace recorded
    refine ⟨⟨⟨key.statement,[m],[]⟩,a⟩,allocated,?_⟩
    have phase : query p (key.statement,[m]) = .initial := WHIRReplay.query_singleton _ _ _
    simp only [keyBad,dite_eq_left phase,parsed]
    rw [seedValue_initial phase] at seed
    rw [Option.some.inj seed]
    exact initial
  · obtain ⟨q,notInitial,bad⟩ := later
    let i := messages.length - position q - 1
    have bound : position q < key.messages.length := by
      change position q < messages.length
      rw [length]
      exact WHIRHistory.position_lt_depth q
    have positive : 0 < position q := by
      have initialPos : position (Coordinate.initial (c := config p)) = 0 := by
        simp [CausalProbability.position,visibleCoordinates]
      by_contra h
      have same : position q = position (Coordinate.initial (c := config p)) := by omega
      exact notInitial (CausalPrefix.position_injective (config p) same)
    have size := StackWHIRReplay.decode_ancestor_length catalog roots key replay decoded
    have hi : i < key.ancestors.length := by dsimp [i,key] at *; omega
    obtain ⟨m,tail,ancestors,a,before,_,allocated,parsed,_,_,agree,sample,pos⟩ :=
      StackWHIRReplay.trace_realization catalog roots key replay decoded x head trace recorded i hi
    have qeq : q = query p (key.statement,m::tail) := by
      apply CausalPrefix.position_injective
      rw [pos]
      dsimp [i,key] at bound ⊢
      omega
    subst q
    refine ⟨⟨⟨key.statement,m::tail,ancestors⟩,a⟩,allocated,?_⟩
    simp only [keyBad,dite_eq_right notInitial,parsed]
    change allocationBad (requestOfTape before.whir.statement
      (CausalStrategy.indexedStrategy before.whir.replies)
      (query p (key.statement,m::tail)) before.whir.tape) (projectSample _ a)
    have congr := CausalStrategy.allocationBad_indexed_congr p before.whir.statement
      before.whir.replies final.whir.replies (query p (key.statement,m::tail))
      before.whir.tape final.whir.tape (projectSample _ a) agree.replies agree.tape
    apply congr.mpr
    rw [agree.statement]
    exact Eq.mp (congrArg (fun value : Sample (query p (key.statement,m::tail)) =>
      allocationBad (requestOfTape final.whir.statement (CausalStrategy.indexedStrategy final.whir.replies)
        (query p (key.statement,m::tail)) final.whir.tape) value) sample) bad

/-- Compiler metadata is irrelevant to the history-level accepted-false cover. -/
theorem recorded_terminal_cover (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    {B : Nat} (trace : List (Sigma (Answer p))) (result : TerminalView p B)
    (recorded : TypedOracleCompiler.HistoryRecorded (query p) result.request.statement trace
      result.request.messages result.allocation.history)
    (failed : TerminalFailure p cap catalog roots result) :
    ∃ ka ∈ trace, keyBad p cap catalog roots ka.1 ka.2 :=
  recorded_history_cover p cap catalog roots result.request.statement result.request.messages
    result.allocation.history trace recorded failed

/-- The typed compiler supplies the recorded-history premise operationally. -/
theorem terminal_cover (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    {B K : Nat} (machine : Machine p B K) (trace result)
    (run : TypedOracleCompiler.Sampling.Runs
      (TypedOracleCompiler.compile (query p) machine (fun _ => none)) trace result)
    (failed : TerminalFailure p cap catalog roots result) :
    ∃ ka ∈ trace, keyBad p cap catalog roots ka.1 ka.2 :=
  recorded_terminal_cover p cap catalog roots trace result
    (TypedOracleCompiler.final_history_in_trace (query p) machine run) failed

/-- Conditional ordinary-ROM stacked list binding, with every adversarial
request and the final invisible completion charged. There is no supplied
soundness, parser, trace-cover, or successful-path resource premise. -/
theorem rom_list_binding (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    {B K : Nat} (machine : Machine p B K) :
    TypedOracleCompiler.Sampling.failureProbability (TerminalFailure p cap catalog roots)
      (TypedOracleCompiler.compile (query p) machine (fun _ => none)) ≤
      min 1 (((B*(K+1) : Nat) : ℚ) * stackEta p cap) := by
  apply le_min
  · apply TypedOracleCompiler.Sampling.expectation_le_one
    intro result
    split <;> norm_num
  · exact TypedOracleCompiler.compiler_failure_bound (query p) machine
      (keyBad p cap catalog roots) (TerminalFailure p cap catalog roots)
      (stackEta p cap) (stackEta_nonneg p cap) (key_sparse p cap catalog roots)
      (terminal_cover p cap catalog roots machine)

theorem rom_list_binding_numeric (p : Profile) (cap : Nat) (catalog : Catalog p cap) (roots : Roots)
    {B K : Nat} (machine : Machine p B K) :
    TypedOracleCompiler.Sampling.failureProbability (TerminalFailure p cap catalog roots)
      (TypedOracleCompiler.compile (query p) machine (fun _ => none)) ≤
      min 1 (((B*(K+1) : Nat) : ℚ) * ((1 / 2^79 : ℚ) + ringCharge cap)) := by
  apply (rom_list_binding p cap catalog roots machine).trans
  apply min_le_min_left
  have h : stackEta p cap ≤ (1 / 2^79 : ℚ) + ringCharge cap := by
    simpa only [stackEta,add_comm] using add_le_add_right (eta_le p) (ringCharge cap)
  exact mul_le_mul_of_nonneg_left h (show (0 : ℚ) ≤ ((B*(K+1) : Nat) : ℚ) from Nat.cast_nonneg _)

end Whir.StackWHIRROM
