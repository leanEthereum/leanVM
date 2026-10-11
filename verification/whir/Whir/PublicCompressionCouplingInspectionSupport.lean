import Whir.PublicCompressionCouplingPrefixTrace
import Whir.PublicCompressionCouplingClosure
import Whir.PublicCompressionCouplingTargetCache

/-! Actual private-prefix target matches imply actual public primitive records.
This fills the hidden-prefix half of cache/trace correspondence using the
literal public memo cache, not a guessed primitive/RO coupling certificate. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed RawOracleCoupling
open TypedOracleCompiler (Sampling)

 theorem execute_certify_trace {Q n : Nat} {R : Type} {P : R → Prop}
    (table : Key Q → Digest32) (p : Computation Q R n) (every : Sampling.Every P p) :
    (Sampling.execute table (PublicCompressionCouplingMixed.Computation.certify p every)).2 = (Sampling.execute table p).2 := by
  induction p with
  | ret result => rfl
  | draw key next ih =>
    simpa only [PublicCompressionCouplingMixed.Computation.certify,Sampling.execute] using
      congrArg (⟨key,table key⟩ :: ·) (ih (table key) _)

open Classical in
 theorem actual_inspection_target_record {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (quiet : hiddenGuess Q iv p counted (oracle seedTable ro) = false)
    {construction : InspectedConstruction}
    (constructionMember : construction ∈ Sampling.eval (oracle seedTable ro)
      (inspect Q iv (Sampling.eval (oracle seedTable ro)
        (compile Q iv [] p Q (by rfl) counted)).observations))
    {node : Node} {answer : Digest32} (record : (node,answer) ∈ construction.prefixLog)
    (target : answer ∈ publicCVTargets (Sampling.eval (oracle seedTable ro)
      (compile Q iv [] p Q (by rfl) counted)).observations) :
    (node,answer) ∈ finalLog [] (Sampling.eval (oracle seedTable ro)
      (compile Q iv [] p Q (by rfl) counted)).observations := by
  let table := oracle seedTable ro
  have publicValue : (Sampling.eval table (memo (certifiedPublic Q iv p counted)
      (fun _ => none))).1.val = Sampling.eval table (compile Q iv [] p Q (by rfl) counted) := by
    simp only [memo_eval_first,overlay_empty,certifiedPublic,PublicCompressionCouplingMixed.Computation.eval_certify]
  have inspected : (⟨.inl node,answer⟩ : Sigma (fun _ : Key Q => Digest32)) ∈
      (Sampling.execute table (privateInspection Q iv
        (Sampling.eval table (memo (certifiedPublic Q iv p counted) (fun _ => none))).1)).2 := by
    simp only [privateInspection,Sampling.execute_pad]
    rw [publicValue]
    exact inspect_prefix_record Q iv table _ constructionMember record
  have publicStored := PublicCompressionCouplingTargetCache.inspected_seed_target_public
    Q iv p counted table quiet inspected (by simpa only [publicValue] using target)
  have publicTrace := PublicCompressionCouplingTargetCache.memo_empty_trace
    table (certifiedPublic Q iv p counted) publicStored
  simp only [certifiedPublic,execute_certify_trace] at publicTrace
  exact compile_seed_record Q seedTable ro iv [] p Q (by rfl) counted node answer publicTrace

open Classical in
/-- Outside the actual hidden-guess alarm, every inspected seed-tree prefix
whose output is a chosen public CV is an actual body in the final public log.
Late-recognition stability is the separate chronological obligation. -/
 theorem actual_inspection_publicBody {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (quiet : hiddenGuess Q iv p counted (oracle seedTable ro) = false)
    {construction : InspectedConstruction}
    (constructionMember : construction ∈ Sampling.eval (oracle seedTable ro)
      (inspect Q iv (Sampling.eval (oracle seedTable ro)
        (compile Q iv [] p Q (by rfl) counted)).observations))
    (target : evalHistory (compressionOf seedTable) iv construction.coordinate.history ∈
      publicCVTargets (Sampling.eval (oracle seedTable ro)
        (compile Q iv [] p Q (by rfl) counted)).observations) :
    PublicBody (finalLog [] (Sampling.eval (oracle seedTable ro)
      (compile Q iv [] p Q (by rfl) counted)).observations)
      (evalHistory (compressionOf seedTable) iv construction.coordinate.history)
      (traceHistory (compressionOf seedTable) iv construction.coordinate.history).nodes := by
  have tree := (traceHistory_valid (compressionOf seedTable) iv
    construction.coordinate.history construction.valid.1).1
  rw [traceHistory_cv] at tree
  apply Tree.publicBody_of_exposure tree _ _
  · intro node answer member
    exact publicCVTargets_contains _ member
  · intro node member hit
    apply actual_inspection_target_record Q iv p counted seedTable ro quiet constructionMember _ hit
    rw [inspect_construction_nodes Q seedTable ro iv _ constructionMember]
    apply List.mem_map.mpr
    exact ⟨node,by simpa only [List.mem_reverse] using member,rfl⟩
  · exact target

#print axioms actual_inspection_target_record
#print axioms actual_inspection_publicBody
end Whir.PublicCompressionCouplingRecognition
