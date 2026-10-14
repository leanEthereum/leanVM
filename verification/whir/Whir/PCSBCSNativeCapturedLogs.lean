import Whir.PCSBCSNativeCapturedRows

/-! Literal capture logs are subsets of the ordinary records in the actual
allocation trace. This removes per-reference collision exclusions once a
single whole ordinary trace is clean; no probability bound is assumed here. -/
set_option autoImplicit false
namespace Whir.PCSBCSNativeCapturedLogs
open Concrete FiatShamirGame DuplexFraming DuplexModeGame TypedOracleCompiler TypedFiatShamirGame
open PCSStateRestoration.Latent PCSBCSSourceRootCapture PCSBCSCapturedNativeReplyBridge
open PCSBCSSourceRootReferences PublicMerkleLog

section Prefix
universe u v w z
variable {Key : Type u} {Answer : Key → Type v} {Root : Type w} {R : Type z}
    [DecidableEq Root]

theorem firstMention_trace_prefix (address : Key → List Root) (root : Root)
    {n : Nat} (program : Sampling Key Answer R n) (table : Table Key Answer)
    (before : List (Sigma Answer))
    (found : PCSBCSFirstRootDisclosure.firstMention address root program table = some before) :
    ∃ after, (Sampling.execute table program).2 = before ++ after := by
  induction program generalizing before with
  | ret => simp [PCSBCSFirstRootDisclosure.firstMention] at found
  | draw key next ih =>
    unfold PCSBCSFirstRootDisclosure.firstMention at found
    split at found
    · have empty : before = [] := (Option.some.inj found).symm
      subst before
      exact ⟨(Sampling.execute table (.draw key next)).2,rfl⟩
    · cases tailFound : PCSBCSFirstRootDisclosure.firstMention address root (next (table key)) table with
      | none => simp [tailFound] at found
      | some tail =>
        simp only [tailFound,Option.map_some,Option.some.injEq] at found
        subst before
        obtain ⟨after,equal⟩ := ih (table key) tail tailFound
        exact ⟨after,by simp only [Sampling.execute,equal,List.cons_append]⟩
end Prefix

section Records
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer (p := p) (Q := Q) (iv := iv) (boundary := boundary)

private theorem fold_membership (events : List (Sigma Answers)) (prior : PublicLog)
    (record : Node × Digest32) :
    record ∈ events.foldl (fun log event => ordinaryRecord event ++ log) prior ↔
      (∃ event ∈ events, record ∈ ordinaryRecord event) ∨ record ∈ prior := by
  induction events generalizing prior with
  | nil => simp
  | cons event rest ih =>
    rw [List.foldl_cons,ih,List.mem_append]
    constructor
    · rintro (⟨found,present,recorded⟩ | (current | old))
      · exact Or.inl ⟨found,List.mem_cons_of_mem event present,recorded⟩
      · exact Or.inl ⟨event,List.mem_cons_self,current⟩
      · exact Or.inr old
    · rintro (⟨found,present,recorded⟩ | old)
      · rcases List.mem_cons.mp present with equal | present
        · subst found
          exact Or.inr (Or.inl recorded)
        · exact Or.inl ⟨found,present,recorded⟩
      · exact Or.inr (Or.inr old)

theorem ordinaryPrefix_membership (events : List (Sigma Answers)) (record : Node × Digest32) :
    record ∈ ordinaryPrefix events ↔ ∃ event ∈ events, record ∈ ordinaryRecord event := by
  simpa only [ordinaryPrefix,List.not_mem_nil,or_false] using fold_membership events [] record

theorem sourceLog_subset {R : Type} {n : Nat} (address : Keys → List Reference)
    (ref : Reference) (program : Sampling Keys Answers R n) (table : Table Keys Answers) :
    ∀ record ∈ sourceLog address ref program table,
      record ∈ ordinaryPrefix (Sampling.execute table program).2 := by
  cases found : PCSBCSFirstRootDisclosure.firstMention address ref program table with
  | none => simp [sourceLog,found,ordinaryPrefix]
  | some before =>
    obtain ⟨after,trace⟩ := firstMention_trace_prefix address ref program table before found
    intro record member
    have captured : record ∈ ordinaryPrefix before := by simpa only [sourceLog,found,Option.getD_some] using member
    obtain ⟨event,present,recorded⟩ := (ordinaryPrefix_membership before record).mp captured
    apply (ordinaryPrefix_membership _ record).mpr
    exact ⟨event,trace ▸ List.mem_append_left after present,recorded⟩

theorem sourceLog_collision {R : Type} {n : Nat} (address : Keys → List Reference)
    (ref : Reference) (program : Sampling Keys Answers R n) (table : Table Keys Answers)
    (bad : OutputCollision (sourceLog address ref program table)) :
    OutputCollision (ordinaryPrefix (Sampling.execute table program).2) := by
  obtain ⟨a,b,d,left,right,different⟩ := bad
  exact ⟨a,b,d,sourceLog_subset address ref program table _ left,
    sourceLog_subset address ref program table _ right,different⟩
end Records

section Driver
open MerkleTransport MerkleTransport.Commitments WHIRPhysicalVerifier
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array PrunedMerklePaths) (B : Nat)
    (limit : sourceBudget ctx Q packet ≤ B)
    (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32)

noncomputable def wholeLog : PublicLog :=
  ordinaryPrefix (Sampling.execute
    (PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro)
    (PCSBCSCapturedIdealNativeAcceptance.allocationProgram cap model ctx stack Q packet saved proofs B limit)).2

theorem referenceLog_authentic (ref : Reference) :
    AuthenticLog seed
      (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref) := by
  unfold PCSBCSNativeCapturedRows.referenceLog
  exact PCSBCSMerkleSeedProjection.sourceLog_authentic seed ro _ ref _

theorem referenceLog_collision (ref : Reference)
    (bad : OutputCollision
      (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref)) :
    OutputCollision (wholeLog cap model ctx stack Q packet saved proofs B limit seed ro) := by
  unfold PCSBCSNativeCapturedRows.referenceLog at bad
  exact sourceLog_collision _ ref _ _ bad

theorem referenceLog_clean
    (clean : ¬ OutputCollision (wholeLog cap model ctx stack Q packet saved proofs B limit seed ro))
    (ref : Reference) :
    ¬ OutputCollision
      (PCSBCSNativeCapturedRows.referenceLog cap model ctx stack Q packet saved proofs B limit seed ro ref) :=
  fun bad => clean (referenceLog_collision cap model ctx stack Q packet saved proofs B limit seed ro ref bad)
end Driver

#print axioms firstMention_trace_prefix
#print axioms ordinaryPrefix_membership
#print axioms sourceLog_subset
#print axioms sourceLog_collision
#print axioms referenceLog_authentic
#print axioms referenceLog_collision
#print axioms referenceLog_clean
end Whir.PCSBCSNativeCapturedLogs
