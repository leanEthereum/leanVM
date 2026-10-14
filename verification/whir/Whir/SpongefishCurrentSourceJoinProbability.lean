import Whir.SpongefishCurrentOpeningAcceptance

/-! Distributional current #607 source join. The accepted caller path and
native opening of `SpongefishCurrentOpeningAcceptance.accepted_opening_original`
are a deterministic consequence of every real primitive and attacker coin. The
public event below reads only the whole source view: some public construction
key's public original list contains a prepared original with the selected
property. The initialized byte-mode coupling then transfers the real accepted
event to the ideal raw-oracle experiment with loss `min(1,(2Q^2-Q)/2^256)`.

The source program replays one fixed caller tape followed by the opening call
list. Its record-binding message calls are a fixed parameter `messages`; the
real event requires the received record to have exactly these message calls. -/
namespace Whir.SpongefishCurrentSourceJoinProbability
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishCurrentModeQueries
open SpongefishCurrentAcceptedJoin SpongefishCurrentOpeningAcceptance
set_option autoImplicit false

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

abbrev SourceResult := Option SpongefishCurrentInitializedMode.Result

/-- Fixed caller tape followed by the native opening call list. -/
def calls (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (grinding : Fin (cfg).folds.size → Fin 64) : List Call :=
  before ++ headerCalls (AnchoredSourceCaller.shape layout).logN ++ payloadCalls ++ messages ++
    openingCalls grinding

def budget (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (grinding : Fin (cfg).folds.size → Fin 64)
    (A : Nat) : Nat :=
  A + SpongefishCurrentInitializedMode.budget tag instanceBytes
    (calls layout before payloadCalls messages grinding)

def program (iv : Digest32) (tag instanceBytes : List Byte) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call) (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) : Program SourceResult :=
  SpongefishCurrentInitializedMode.afterPrefix iv tag instanceBytes prefixProgram
    (calls layout before payloadCalls messages grinding)

/-- Real native acceptance of the whole current caller path and opening, with
the prepared original used by the opening equations. `Bad` may inspect the
whole source view, for example a failed public extraction. -/
def NativeAcceptedBad (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input)
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop) : Prop :=
  ∃ (r : SpongefishSessionAdapter.Record) (input : PCSBCSCallerBinding.CallerInput p)
    (initial pre received payload next : Cursor),
    SpongefishCurrentObservedSessionEntry.actualSetup (compressionOf C) iv tag instanceBytes
      (runReal C iv prefixProgram).view.result.narg
      (runReal C iv prefixProgram).view.result.hints = some initial ∧
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) initial before = .ok pre ∧
    SpongefishCurrentCommitmentReceive.receive (compressionOf C) pre
      (AnchoredSourceCaller.shape layout) = some (received,r) ∧
    SpongefishCurrentPrimitiveEventCompiler.actualReplay (compressionOf C) received payloadCalls =
      .ok payload ∧
    SpongefishRecordBindingParser.verify (compressionOf C) payload r = some next ∧
    messageCalls r = messages ∧
    Nonempty (Accepted C decode grinding r input next) ∧
    SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout
      (coordinate next.pending (next.pending.consumed / 32)) r instanceBytes = some input ∧
    Bad input (runReal C iv (program iv tag instanceBytes layout before payloadCalls messages
      grinding prefixProgram)).view

/-- Public view event: some construction key's public original list contains
an original with the property. No hidden primitive or coin is read. -/
def PublicBad (Q : Nat) (iv : Digest32) (instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout)
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (view : View SourceResult) : Prop :=
  ∃ (q : FiatShamirGame.Coordinate) (work : pathCost q ≤ Q) (input : PCSBCSCallerBinding.CallerInput p),
    input ∈ SpongefishCurrentSourceCallerOriginal.original p layout iv (constructionKey Q iv q work)
      instanceBytes view.observations ∧ Bad input view

open Classical in
noncomputable def publicObserver (Q : Nat) (iv : Digest32) (instanceBytes : List Byte)
    (layout : WHIRCallerClaims.CallerLayout)
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (view : View SourceResult) : Bool :=
  decide (PublicBad Q iv instanceBytes layout Bad view)

/-- Pointwise join: real native acceptance places its prepared original in a
public original list of the same source view. -/
theorem native_public (C : PrimitiveOracle) (iv : Digest32) (tag instanceBytes : List Byte)
    (nonempty : instanceBytes ≠ []) (layout : WHIRCallerClaims.CallerLayout)
    (before payloadCalls messages : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : Counts A prefixProgram)
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop)
    (native : NativeAcceptedBad C iv tag instanceBytes layout before payloadCalls messages decode
      grinding prefixProgram Bad) :
    PublicBad (budget tag instanceBytes layout before payloadCalls messages grinding A) iv instanceBytes
      layout Bad (runReal C iv (program iv tag instanceBytes layout before payloadCalls messages
        grinding prefixProgram)).view := by
  obtain ⟨r,input,initial,pre,received,payload,next,setup,preRun,receivedEq,payloadRun,bindingEq,
    messagesEq,⟨opened⟩,physical,bad⟩ := native
  have shapeEq := (SpongefishCurrentCommitmentReceive.receive_retains _ pre received _ r receivedEq).1
  have joined := accepted_opening_original C iv layout r tag instanceBytes prefixProgram A attacker
    nonempty before payloadCalls beforeEq payloadEq initial pre received payload next setup preRun
    receivedEq payloadRun bindingEq decode grinding input opened
  obtain ⟨_,_,_,work,_,_,member⟩ := joined
  subst messagesEq
  have sameCalls : calls layout before payloadCalls (messageCalls r) grinding =
      before ++ headerCalls r.shape.logN ++ payloadCalls ++ messageCalls r ++
        openingCalls grinding := by
    rw [calls,shapeEq]
  unfold budget program at *
  rw [sameCalls] at bad ⊢
  exact ⟨_,work,input,member input physical,bad⟩

open Classical in
/-- Distributional source join: the real probability of native acceptance with
the selected property is at most the IDEAL probability of the public join event
plus the initialized current byte-mode coupling loss. -/
theorem native_ideal_bound {Coins : Type} [Fintype Coins] [Nonempty Coins]
    (iv : Digest32) (tag instanceBytes : List Byte) (nonempty : instanceBytes ≠ [])
    (layout : WHIRCallerClaims.CallerLayout) (before payloadCalls messages : List Call)
    (beforeEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.preludeShape layout) = some before)
    (payloadEq : SpongefishCurrentSourceCallerOriginal.shapeCalls
      (SpongefishCurrentSourceCallerOriginal.payloadShape layout) = some payloadCalls)
    (decode : List Nat → Nat → List Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64)
    (prefixProgram : Coins → Program SpongefishCurrentInitializedMode.Input) (A : Nat)
    (attacker : ∀ coin, Counts A (prefixProgram coin))
    (Bad : PCSBCSCallerBinding.CallerInput p → View SourceResult → Prop) :
    let Q := budget tag instanceBytes layout before payloadCalls messages grinding A
    letI := DuplexPublicSimulator.seedFintype
    average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedBad coins.1 iv tag instanceBytes layout before payloadCalls messages decode
        grinding (prefixProgram coins.2) Bad then (1 : ℚ) else 0) ≤
    idealProbability (DuplexPublicSimulator.simulator Q) iv
        (fun coin => program iv tag instanceBytes layout before payloadCalls messages grinding
          (prefixProgram coin))
        (fun coin => SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
          (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))
        (publicObserver Q iv instanceBytes layout Bad) +
      min 1 ((2*(Q : ℚ)^2-(Q : ℚ))/2^256) := by
  intro Q
  let _ := DuplexPublicSimulator.seedFintype
  have subset : average (fun coins : PrimitiveOracle × Coins =>
      if NativeAcceptedBad coins.1 iv tag instanceBytes layout before payloadCalls messages decode
        grinding (prefixProgram coins.2) Bad then (1 : ℚ) else 0) ≤
      realProbability iv (fun coin => program iv tag instanceBytes layout before payloadCalls messages
        grinding (prefixProgram coin)) (publicObserver Q iv instanceBytes layout Bad) := by
    unfold realProbability
    rw [distinguish_average (inferInstance : Fintype (PrimitiveOracle × Coins))]
    apply average_mono
    intro coins
    by_cases native : NativeAcceptedBad coins.1 iv tag instanceBytes layout before payloadCalls
      messages decode grinding (prefixProgram coins.2) Bad
    · have published := decide_eq_true (native_public coins.1 iv tag instanceBytes nonempty layout before
        payloadCalls messages beforeEq payloadEq decode grinding (prefixProgram coins.2) A
        (attacker coins.2) Bad native)
      simp only [native,↓reduceIte]
      change (1 : ℚ) ≤ if publicObserver Q iv instanceBytes layout Bad _ = true then 1 else 0
      have observed : publicObserver Q iv instanceBytes layout Bad (runReal coins.1 iv
          (program iv tag instanceBytes layout before payloadCalls messages grinding
            (prefixProgram coins.2))).view = true := published
      rw [observed]
      norm_num
    · simp only [native,↓reduceIte]
      split <;> norm_num
  have coupling : ModeAdv (DuplexPublicSimulator.simulator Q) iv
      (fun coin => program iv tag instanceBytes layout before payloadCalls messages grinding
        (prefixProgram coin))
      (fun coin => SpongefishCurrentInitializedMode.afterPrefix_counted iv tag instanceBytes
        (prefixProgram coin) (calls layout before payloadCalls messages grinding) A (attacker coin))
      (publicObserver Q iv instanceBytes layout Bad) ≤ min 1 ((2*(Q : ℚ)^2-(Q : ℚ))/2^256) :=
    SpongefishCurrentInitializedMode.afterPrefix_mode_bound iv tag instanceBytes
      prefixProgram (calls layout before payloadCalls messages grinding) A attacker
      (publicObserver Q iv instanceBytes layout Bad)
  unfold ModeAdv at coupling
  have deviation := (abs_le.mp coupling).2
  linarith

#print axioms native_public
#print axioms native_ideal_bound

end Whir.SpongefishCurrentSourceJoinProbability
