import Whir.PCSBCSSourceSavedRecordDecoder
import Whir.PCSBCSSourceRootReferences

/-! Saved-record provenance from the actual fresh caller parser. Successful
payload operations consume a prefix of their input; the checked binding consumes
exactly the complete opening. The canonical-history guard then identifies the
literal bytes with the semantic lift of those operations. No literal suffix,
native framing normalization, or parser-success certificate is an extra input.
This is a theorem about the existing source projection, not universal Rust
observer refinement. -/
namespace Whir.PCSBCSSourceSavedRecordProvenance
open Concrete FiatShamirGame WHIRCallerClaims AnchoredHeaderCodec
open WHIRHistory PCSBCSSourceSavedRecordDecoder

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- A parser never creates, reorders, or restores remaining input tokens. -/
def ConsumesPrefix {A : Type} (parser : CallerParser A) : Prop :=
  ∀ tokens value rest, parser tokens = some (value,rest) → List.IsSuffix rest tokens

theorem consumes_pure {A : Type} (value : A) : ConsumesPrefix (pure value) := by
  intro tokens result rest accepted
  change some (value,tokens) = some (result,rest) at accepted
  cases Option.some.inj accepted
  exact ⟨[],rfl⟩

theorem consumes_failure {A : Type} : ConsumesPrefix (fun _ => (none : Option (A × List CallerToken))) := by
  intro tokens value rest accepted
  contradiction

theorem consumes_bind {A B : Type} (parser : CallerParser A) (next : A → CallerParser B)
    (first : ConsumesPrefix parser) (last : ∀ value, ConsumesPrefix (next value)) :
    ConsumesPrefix (parser >>= next) := by
  intro tokens value rest accepted
  obtain ⟨middle,remaining,hfirst,hlast⟩ := parser_bind_inv parser next tokens rest value accepted
  exact (last middle remaining value rest hlast).trans (first tokens middle remaining hfirst)

theorem consumes_forIn {A B : Type} (xs : List A) (initial : B)
    (body : A → B → CallerParser (ForInStep B))
    (step : ∀ x value, ConsumesPrefix (body x value)) :
    ConsumesPrefix (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => exact consumes_pure initial
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply consumes_bind _ _ (step x initial)
    intro out
    cases out with
    | done value => exact consumes_pure value
    | yield value => exact ih value

theorem consumes_mapM {A B : Type} (xs : List A) (f : A → CallerParser B)
    (step : ∀ x, ConsumesPrefix (f x)) : ConsumesPrefix (xs.mapM f) := by
  induction xs with
  | nil => exact consumes_pure []
  | cons x xs ih =>
    rw [List.mapM_cons]
    apply consumes_bind _ _ (step x)
    intro value
    apply consumes_bind _ _ ih
    intro rest
    exact consumes_pure (value :: rest)

theorem consumes_readScalar : ConsumesPrefix readScalar := by
  intro tokens value rest accepted
  cases tokens with
  | nil => cases accepted
  | cons token tail =>
    cases token <;> simp only [readScalar] at accepted <;> try contradiction
    cases Option.some.inj accepted
    exact ⟨[.sent value],rfl⟩

theorem consumes_drawScalar : ConsumesPrefix drawScalar := by
  intro tokens value rest accepted
  cases tokens with
  | nil => cases accepted
  | cons token tail =>
    cases token <;> simp only [drawScalar] at accepted <;> try contradiction
    cases Option.some.inj accepted
    exact ⟨[.draw value],rfl⟩

theorem consumes_check (ok : Bool) : ConsumesPrefix (check ok) := by
  cases ok
  · exact consumes_failure
  · exact consumes_pure ()

theorem consumes_nonce (bits : Nat) : ConsumesPrefix (nonce bits) := by
  intro tokens value rest accepted
  cases tokens with
  | nil => cases accepted
  | cons token tail =>
    cases token with
    | sent => cases accepted
    | draw => cases accepted
    | nonce actual bytes =>
      simp only [nonce] at accepted
      split at accepted
      · cases Option.some.inj accepted
        exact ⟨[.nonce actual bytes],rfl⟩
      · contradiction

theorem consumes_readScalars (n : Nat) : ConsumesPrefix (readScalars n) := by
  induction n with
  | zero => exact consumes_pure []
  | succ n ih =>
    apply consumes_bind _ _ consumes_readScalar
    intro value
    apply consumes_bind _ _ ih
    intro rest
    exact consumes_pure (value :: rest)

theorem consumes_drawScalars (n : Nat) : ConsumesPrefix (drawScalars n) := by
  induction n with
  | zero => exact consumes_pure []
  | succ n ih =>
    apply consumes_bind _ _ consumes_drawScalar
    intro value
    apply consumes_bind _ _ ih
    intro rest
    exact consumes_pure (value :: rest)

/-- Structural closure for the actual source loops and their pure branch code. -/
macro "consume_source" "[" rules:Lean.Parser.Tactic.SolveByElim.arg,* "]" : tactic => `(tactic|
  repeat' first
    | solve_by_elim (config := {maxDepth := 1}) only [$rules,*]
    | exact consumes_pure _
    | exact consumes_failure
    | exact consumes_readScalar
    | exact consumes_drawScalar
    | exact consumes_readScalars _
    | exact consumes_drawScalars _
    | exact consumes_check _
    | exact consumes_nonce _
    | (refine consumes_bind _ _ ?_ (fun value => ?_))
    | (refine consumes_forIn _ _ _ (fun x value => ?_))
    | (refine consumes_mapM _ _ (fun x => ?_))
    | (dsimp +zetaHave only; split)
    | split)

theorem consumes_gkrPoint (mu : Nat) : ConsumesPrefix (gkrPoint mu) := by
  unfold gkrPoint
  consume_source []

theorem consumes_busClaims (layout : BusLayout) : ConsumesPrefix (busClaims layout) := by
  unfold busClaims
  consume_source [consumes_gkrPoint]

theorem consumes_receiveTable (layout : AirLayout) (point : List E) :
    ConsumesPrefix (receiveTable layout point) := by
  unfold receiveTable
  consume_source []

theorem consumes_constraintClaims (layouts : List AirLayout) (point : List E) :
    ConsumesPrefix (constraintClaims layouts point) := by
  unfold constraintClaims
  consume_source [consumes_receiveTable]

theorem consumes_flockClaims (layouts : List FlockLayout) : ConsumesPrefix (flockClaims layouts) := by
  unfold flockClaims
  consume_source []

theorem consumes_settledClaims (tables : List CpuTableLayout) (point : List E) :
    ConsumesPrefix (settledClaims tables point) := by
  unfold settledClaims
  consume_source []

theorem consumes_recPayload (layout : RecLayout) : ConsumesPrefix (recPayload layout) := by
  unfold recPayload
  consume_source [consumes_busClaims,consumes_constraintClaims,consumes_flockClaims]
  exact consumes_busClaims _

theorem consumes_cpuPayload (layout : CpuLayout) : ConsumesPrefix (cpuPayload layout) := by
  unfold cpuPayload
  consume_source [consumes_busClaims,consumes_settledClaims,consumes_constraintClaims,consumes_flockClaims]
  exact consumes_busClaims _

theorem consumes_payload (layout : CallerLayout) : ConsumesPrefix (AnchoredSourceCaller.payload layout) := by
  cases layout with
  | cpu layout => exact consumes_cpuPayload layout
  | recursion layout => exact consumes_recPayload layout

theorem readScalars_prefix (n : Nat) (tokens rest : List CallerToken) (values : List E)
    (accepted : readScalars n tokens = some (values,rest)) :
    tokens = values.map CallerToken.sent ++ rest := by
  induction n generalizing tokens values with
  | zero =>
    change some ([],tokens) = some (values,rest) at accepted
    cases Option.some.inj accepted
    rfl
  | succ n ih =>
    obtain ⟨value,middle,head,tail⟩ := parser_bind_inv _ _ _ _ _ accepted
    obtain ⟨xs,remaining,body,finished⟩ := parser_bind_inv _ _ _ _ _ tail
    change some (value :: xs,remaining) = some (values,rest) at finished
    cases Option.some.inj finished
    cases tokens with
    | nil => cases head
    | cons token tail =>
      cases token <;> simp only [readScalar] at head <;> try contradiction
      cases Option.some.inj head
      simp only [List.map_cons,List.cons_append]
      rw [ih _ _ body]

theorem binding_prefix (saved : Record) (tokens rest : List CallerToken) (value : Unit)
    (accepted : AnchoredSourceCaller.binding saved tokens = some (value,rest)) :
    tokens = (openingScalars saved).map CallerToken.sent ++ rest := by
  obtain ⟨frame,middle,read,checked⟩ := parser_bind_inv _ _ _ _ _ accepted
  have equal : frame = openingScalars saved := by
    by_contra different
    simp [check,different] at checked
  subst frame
  have remaining : middle = rest := by
    simp only [check,beq_self_eq_true,↓reduceIte] at checked
    change some ((),middle) = some (value,rest) at checked
    exact congrArg Prod.snd (Option.some.inj checked)
  rw [← remaining]
  exact readScalars_prefix _ _ _ _ read

/-- Actual payload consumption plus literal binding, not a free success certificate. -/
theorem sourceClaims_suffix (layout : CallerLayout) (saved : Record)
    (tokens : List CallerToken) (claims : AnchoredSourceCaller.Claims)
    (accepted : AnchoredSourceFreshCaller.sourceClaims layout saved tokens = some (claims,[])) :
    ∃ preTokens, tokens = preTokens ++ (openingScalars saved).map CallerToken.sent := by
  obtain ⟨payload,middle,parsed,tail⟩ := parser_bind_inv _ _ _ _ _ accepted
  obtain ⟨bound,remaining,binding,finished⟩ := parser_bind_inv _ _ _ _ _ tail
  change some (_,remaining) = some (claims,[]) at finished
  have empty : remaining = [] := congrArg Prod.snd (Option.some.inj finished)
  have suffix := binding_prefix saved middle remaining bound binding
  rw [empty,List.append_nil] at suffix
  obtain ⟨preTokens,eq⟩ := consumes_payload layout tokens payload middle parsed
  exact ⟨preTokens,by rw [← eq,suffix]⟩

/-- Lift every caller operation, including literal nonce bytes, to the existing
semantic model. The codec inverse is total, so no extra nonce condition occurs. -/
def tokenEvent : CallerToken → WHIRHistory.Event
  | .sent x => .observe [x]
  | .draw _ => .squeeze 24
  | .nonce bits value => .nonce bits (ByteCodec.decodeE value)

theorem tokenEvent_model (m : DuplexRefinement.Model) (token : CallerToken) :
    modelEvent m (tokenEvent token) = WHIRCallerShape.applyOperation m (tokenOperation token) := by
  cases token <;> simp [tokenEvent,modelEvent,tokenOperation,WHIRCallerShape.applyOperation,
    ByteCodec.encodeE_decodeE]

def runSemantic (m : SemanticModel) (tokens : List CallerToken) : SemanticModel :=
  tokens.foldl (fun m token => semanticEvent m (tokenEvent token)) m

theorem runSemantic_encode (m : SemanticModel) (tokens : List CallerToken) :
    encodeModel (runSemantic m tokens) =
      WHIRCallerShape.runOperations (encodeModel m) (tokens.map tokenOperation) := by
  induction tokens generalizing m with
  | nil => rfl
  | cons token tokens ih =>
    simp only [runSemantic,List.foldl_cons,List.map_cons,WHIRCallerShape.runOperations]
    rw [← runSemantic,ih,semanticEvent_encode,tokenEvent_model]
    rfl

/-- The canonical-history guard, rather than a native-normalization assumption,
identifies the final contiguous scalar run. Adjacent earlier sent scalars are
retained as an arbitrary prefix. -/
theorem literalRun_sent_suffix (domain statement : Digest32) (preTokens : List CallerToken)
    (values : List E) (nonempty : values ≠ []) :
    ∃ pre, literalRun (tokenHistory domain statement (preTokens ++ values.map CallerToken.sent)) =
      some (pre ++ values) := by
  let seed : SemanticModel := ⟨⟨domain,statement,[]⟩,[],0,0⟩
  let model := runSemantic seed preTokens
  have lift : WHIRCallerShape.runOperations (WHIRCallerShape.seedModel domain statement)
      (preTokens.map tokenOperation) = encodeModel model := (runSemantic_encode seed preTokens).symm
  have framed : tokenHistory domain statement (preTokens ++ values.map CallerToken.sent) =
      encodeHistory (closeSemantic (semanticEvent model (.observe values))).history := by
    unfold tokenHistory
    rw [List.map_append,runOperations_append,run_sent_tokens,lift]
    change (DuplexRefinement.closeRun (modelEvent (encodeModel model) (.observe values))).history = _
    rw [← semanticEvent_encode,← closeSemantic_encode]
    rfl
  have runNonempty : model.run ++ values ≠ [] := by simp [nonempty]
  rw [framed]
  simp only [literalRun,encodeHistory,frames_roundtrip,Option.map_some,
    semanticEvent,nonempty,↓reduceIte,closeSemantic,runNonempty,List.foldl_append,
    List.foldl_cons,List.foldl_nil,extendRun]
  by_cases hz : (if model.consumed = 0 then model.previous else model.consumed) = 0
  · simp only [hz,↓reduceIte]
    exact ⟨model.history.frames.foldl extendRun [] ++ model.run,by simp only [List.append_assoc]⟩
  · simp only [hz,↓reduceIte]
    exact ⟨model.run,rfl⟩

theorem profileShape_compatible (p : ParameterBounds.Profile) (saved : Record)
    (profile : PCSBCSSourceRootReferences.profileShape p saved.shape) : Compatible p saved := profile

/-- End-to-end exact recovery from successful actual source decoding. Only the
source's existing record validity/profile guards are needed. -/
theorem decode_saved (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (claims : AnchoredSourceCaller.Claims)
    (accepted : AnchoredSourceFreshCaller.decode layout saved entry answers = some claims)
    (valid : saved.Valid) (profile : Compatible p saved) :
    PCSBCSSourceSavedRecordDecoder.decode p entry = some saved := by
  obtain ⟨tokens,parsed,_,source⟩ := AnchoredSourceFreshCaller.decode_exact layout saved entry answers claims accepted
  obtain ⟨preTokens,suffix⟩ := sourceClaims_suffix layout saved tokens claims source
  have history := entryTokens_history entry answers tokens parsed
  rw [suffix] at history
  have nonempty : openingScalars saved ≠ [] := by simp [openingScalars]
  obtain ⟨pre,literal⟩ := literalRun_sent_suffix entry.domain entry.statement preTokens (openingScalars saved) nonempty
  rw [history] at literal
  exact decode_literal_run p entry saved valid profile pre literal

/-- Endpoint using exactly the profile predicate of the source reference parser. -/
theorem decode_saved_profileShape (p : ParameterBounds.Profile) (layout : CallerLayout) (saved : Record)
    (entry : FramedHistory) (answers : Coordinate → Digest32) (claims : AnchoredSourceCaller.Claims)
    (accepted : AnchoredSourceFreshCaller.decode layout saved entry answers = some claims)
    (valid : saved.Valid) (profile : PCSBCSSourceRootReferences.profileShape p saved.shape) :
    PCSBCSSourceSavedRecordDecoder.decode p entry = some saved :=
  decode_saved p layout saved entry answers claims accepted valid (profileShape_compatible p saved profile)

#print axioms consumes_payload
#print axioms sourceClaims_suffix
#print axioms literalRun_sent_suffix
#print axioms decode_saved
#print axioms decode_saved_profileShape
end Whir.PCSBCSSourceSavedRecordProvenance
