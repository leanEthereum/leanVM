import Whir.PCSBCSPublicExtractor
import Whir.CommitmentAnchor

/-! Literal first-capture stability and uniqueness of actual public extractor
outputs. A later public trace cannot replace an already captured Root0. The
anchor separation premise is explicit; its probability must come from causal
preanchor preparation, not an assumed native Fiat-Shamir security result. -/
namespace Whir.PCSBCSPublicExtractorAnchor
open Concrete Protocol CausalGame FiatShamirGame DuplexFraming DuplexModeGame
open PublicMerkleLog PCSBCSSourceRootReferences PCSBCSPublicExtractor
set_option autoImplicit false

private theorem firstPrefix_append {Key Root : Type} {Answer : Key → Type}
    [DecidableEq Root] (address : Key → List Root) (r : Root)
    (past later retained : List (Sigma Answer))
    (found : PCSBCSNativePublicCapture.firstPrefix address r past = some retained) :
    PCSBCSNativePublicCapture.firstPrefix address r (past ++ later) = some retained := by
  induction past generalizing retained with
  | nil => simp [PCSBCSNativePublicCapture.firstPrefix] at found
  | cons event rest ih =>
    by_cases hit : r ∈ address event.1
    · simpa [PCSBCSNativePublicCapture.firstPrefix,hit] using found
    · simp only [PCSBCSNativePublicCapture.firstPrefix,hit,↓reduceIte] at found
      obtain ⟨before,earlier,equal⟩ := Option.map_eq_some_iff.mp found
      subst retained
      simp only [List.cons_append,PCSBCSNativePublicCapture.firstPrefix,hit,↓reduceIte,
        ih before earlier,Option.map_some]

private theorem mixedTrace_append (B : Nat) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (past later : List Observation) :
    PCSBCSNativePublicCapture.mixedTrace B iv log (past ++ later) =
      PCSBCSNativePublicCapture.mixedTrace B iv log past ++
        PCSBCSNativePublicCapture.mixedTrace B iv
          (past.foldl PCSBCSNativePublicCapture.nextLog log) later := by
  induction past generalizing log with
  | nil => simp [PCSBCSNativePublicCapture.mixedTrace]
  | cons event rest ih =>
    simp only [List.cons_append,PCSBCSNativePublicCapture.mixedTrace,List.foldl_cons,
      ih,List.append_assoc]

/-- No later key, answer or acceptance result can change an existing first
capture. The current query's answer was never included in this strict prefix. -/
theorem capturedPrefix_extension {R S : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat) (ref : Reference)
    (before : View R) (after : View S) (later : List Observation)
    (extended : after.observations = before.observations ++ later)
    (retained : List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)))
    (found : capturedPrefix p B iv boundary ref before = some retained) :
    capturedPrefix p B iv boundary ref after = some retained := by
  unfold capturedPrefix at found ⊢
  rw [extended,mixedTrace_append]
  exact firstPrefix_append _ _ _ _ _ found

/-- The actual hash-before-projection Root0 getter remains immutable under any
public continuation once its first address mention has occurred. -/
theorem root_extension {R S : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat) (ref : Reference)
    (before : View R) (after : View S) (later : List Observation)
    (extended : after.observations = before.observations ++ later)
    (retained : List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)))
    (found : capturedPrefix p B iv boundary ref before = some retained) :
    root p B iv boundary ref after = root p B iv boundary ref before := by
  have same := capturedPrefix_extension p B iv boundary ref before after later extended retained found
  simp only [root,PCSBCSPublicExtractor.log,found,same]

/-- An actual returned word is in the selected list of the literal captured
root and retained anchor. This is not a classical-choice implementation. -/
theorem extractAt_selected {R : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat)
    (original : PCSBCSCallerBinding.CallerInput p) (ref : Reference) (view : View R)
    (point : Fin (ParameterBounds.config p).logN → E)
    (pointEq : original.anchorPoint = Array.ofFn point)
    (w : Witness (ParameterBounds.config p) original.lanes)
    (returned : extractAt p B iv boundary original ref view = some w) :
    w ∈ CommitmentAnchor.selected p original.lanes (root p B iv boundary ref view)
      point original.anchorValue := by
  have explains := extractAt_output_explains p B iv boundary original ref view w returned
  apply Finset.mem_filter.mpr
  exact ⟨explains.rootCandidate,by simpa only [pointEq] using explains.anchor⟩

/-- For arbitrary later original claims, an actual returned word equals every
candidate satisfying the same retained anchor of this captured commitment. -/
theorem extractAt_equals_selected {R : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat)
    (original : PCSBCSCallerBinding.CallerInput p) (ref : Reference) (view : View R)
    (point : Fin (ParameterBounds.config p).logN → E)
    (pointEq : original.anchorPoint = Array.ofFn point)
    (clean : ¬ CommitmentAnchor.Ambiguous p original.lanes
      (root p B iv boundary ref view) point)
    (w other : Witness (ParameterBounds.config p) original.lanes)
    (returned : extractAt p B iv boundary original ref view = some w)
    (selected : other ∈ CommitmentAnchor.selected p original.lanes
      (root p B iv boundary ref view) point original.anchorValue) : w = other := by
  exact Finset.card_le_one.mp (CommitmentAnchor.selected_unique p original.lanes
    (root p B iv boundary ref view) point clean original.anchorValue) w
    (extractAt_selected p B iv boundary original ref view point pointEq w returned) other selected

/-- Two successful runs on a public trace and an arbitrary later continuation
return the same word for the immutable anchor. Frozen-root equality is derived
from literal first capture, not supplied as a matching certificate. -/
theorem extractAt_same_word {R S : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat)
    (original : PCSBCSCallerBinding.CallerInput p) (ref : Reference)
    (before : View R) (after : View S) (later : List Observation)
    (extended : after.observations = before.observations ++ later)
    (retained : List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)))
    (found : capturedPrefix p B iv boundary ref before = some retained)
    (point : Fin (ParameterBounds.config p).logN → E)
    (pointEq : original.anchorPoint = Array.ofFn point)
    (clean : ¬ CommitmentAnchor.Ambiguous p original.lanes
      (root p B iv boundary ref before) point)
    (w₁ w₂ : Witness (ParameterBounds.config p) original.lanes)
    (returned₁ : extractAt p B iv boundary original ref before = some w₁)
    (returned₂ : extractAt p B iv boundary original ref after = some w₂) : w₁ = w₂ := by
  have first := extractAt_selected p B iv boundary original ref before point pointEq w₁ returned₁
  have second := extractAt_selected p B iv boundary original ref after point pointEq w₂ returned₂
  rw [root_extension p B iv boundary ref before after later extended retained found] at second
  exact Finset.card_le_one.mp (CommitmentAnchor.selected_unique p original.lanes
    (root p B iv boundary ref before) point clean original.anchorValue) w₁ first w₂ second

private theorem selected_lane_transport (p : ParameterBounds.Profile) {lanes₁ lanes₂ : Nat}
    (same : lanes₂ = lanes₁) (raw : BaseOracle)
    (point : Fin (ParameterBounds.config p).logN → E) (value : E)
    (w : Witness (ParameterBounds.config p) lanes₂)
    (selected : w ∈ CommitmentAnchor.selected p lanes₂ raw point value) :
    (same ▸ w) ∈ CommitmentAnchor.selected p lanes₁ raw point value := by
  cases same
  exact selected

private theorem word_array_transport (p : ParameterBounds.Profile) {lanes₁ lanes₂ : Nat}
    (same : lanes₂ = lanes₁) (w : Witness (ParameterBounds.config p) lanes₂) :
    Array.ofFn (same ▸ w) = Array.ofFn w := by
  cases same
  rfl

/-- All original families and later point claims may change. Only the immutable
commitment metadata is retained. The consumer-visible returned base-word arrays
are equal, without assuming a matching root, claim set or selected witness. -/
theorem extractAt_changed_claims_same_word {R S : Type} (p : ParameterBounds.Profile)
    (B : Nat) (iv : Digest32) (boundary : Nat)
    (original₁ original₂ : PCSBCSCallerBinding.CallerInput p) (ref : Reference)
    (sameLanes : original₂.lanes = original₁.lanes)
    (samePoint : original₂.anchorPoint = original₁.anchorPoint)
    (sameValue : original₂.anchorValue = original₁.anchorValue)
    (before : View R) (after : View S) (later : List Observation)
    (extended : after.observations = before.observations ++ later)
    (retained : List (Sigma (fun _ : PublicCompressionCouplingMixed.Key B => Digest32)))
    (found : capturedPrefix p B iv boundary ref before = some retained)
    (point : Fin (ParameterBounds.config p).logN → E)
    (pointEq : original₁.anchorPoint = Array.ofFn point)
    (clean : ¬ CommitmentAnchor.Ambiguous p original₁.lanes
      (root p B iv boundary ref before) point)
    (w₁ : Witness (ParameterBounds.config p) original₁.lanes)
    (w₂ : Witness (ParameterBounds.config p) original₂.lanes)
    (returned₁ : extractAt p B iv boundary original₁ ref before = some w₁)
    (returned₂ : extractAt p B iv boundary original₂ ref after = some w₂) :
    Array.ofFn w₁ = Array.ofFn w₂ := by
  have selected₂ := extractAt_selected p B iv boundary original₂ ref after point
    (samePoint.trans pointEq) w₂ returned₂
  rw [root_extension p B iv boundary ref before after later extended retained found] at selected₂
  have transported := selected_lane_transport p sameLanes
    (root p B iv boundary ref before) point original₂.anchorValue w₂ selected₂
  rw [sameValue] at transported
  have same := extractAt_equals_selected p B iv boundary original₁ ref before point
    pointEq clean w₁ (sameLanes ▸ w₂) returned₁ transported
  exact (congrArg Array.ofFn same).trans (word_array_transport p sameLanes w₂)

#print axioms extractAt_changed_claims_same_word

#print axioms capturedPrefix_extension
#print axioms root_extension
#print axioms extractAt_selected
#print axioms extractAt_same_word
#print axioms extractAt_equals_selected
end Whir.PCSBCSPublicExtractorAnchor
