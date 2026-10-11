import Whir.PublicCompressionCouplingLabels
import Whir.PublicCompressionCouplingRelabelCache

/-! Actual one-query fresh-stream alignment. Public cached returns need no
mixed draw; recognized terminals retain their full raw-coordinate node label.
The cache and log premises are operational source-induction invariants. -/
namespace Whir.PublicCompressionCouplingPrimitiveStream
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open TypedFiatShamirGame
open TypedOracleCompiler (Sampling)
open PublicCompressionCouplingMixed PublicCompressionCouplingJoint
open PublicCompressionCouplingStreams PublicCompressionCouplingRelabelCache
open PublicCompressionCouplingRecognition
set_option backward.isDefEq.respectTransparency false

/-- Every public record is already stored in the actual real primitive cache. -/
def LogCovered (pc : PublicCompressionCouplingJoint.Cache Node) (log : PublicLog) : Prop :=
  ∀ node answer, (node,answer) ∈ log → pc node=some answer

/-- A single consumed coordinate uses exactly the same fresh digest cell on
both sides. Coordinate-label injectivity is required only on consumed cells. -/
theorem matched_draw {A B : Type} [DecidableEq A] [DecidableEq B]
    (label : B → A) (key : B) (pc : PublicCompressionCouplingJoint.Cache A)
    (qc final : PublicCompressionCouplingJoint.Cache B) (stream : List Digest32)
    (answer : Digest32) (updated : PublicCompressionCouplingJoint.Cache B) (remaining : List Digest32)
    (execution : run (.draw key (fun d => .ret (n:=0) d)) qc stream=some (answer,updated,remaining))
    (related : Related label pc qc) (extension : Extends updated final)
    (injective : InjectiveOn label final) :
    ∃ pc', run (.draw (label key) (fun d => .ret (n:=0) d)) pc stream=some (answer,pc',remaining) ∧
      Related label pc' updated ∧ pc' (label key)=some answer ∧ Extends updated final := by
  have initialExtension : Extends qc final := by
    intro k d stored
    exact extension k d (run_extends _ qc stream execution stored)
  cases hit : qc key with
  | some digest =>
    rw [run_hit hit] at execution
    simp only [run,Option.some.injEq,Prod.mk.injEq] at execution
    obtain ⟨answerEq,cacheEq,streamEq⟩ := execution
    subst answer
    subst updated
    subst remaining
    have realHit := related.forward key digest hit
    exact ⟨pc,by rw [run_hit realHit]; rfl,related,realHit,extension⟩
  | none =>
    cases stream with
    | nil => rw [run_miss_nil hit] at execution; cases execution
    | cons digest rest =>
      rw [run_miss_cons hit] at execution
      simp only [run,Option.some.injEq,Prod.mk.injEq] at execution
      obtain ⟨answerEq,cacheEq,streamEq⟩ := execution
      subst answer
      subst updated
      subst remaining
      have present : final key=some digest := extension key digest (put_self _ _ _)
      have realHit : pc (label key)=none := by
        rw [related.lookup initialExtension injective present,hit]
      exact ⟨put pc (label key) digest,by rw [run_miss_cons realHit]; rfl,
        related.put initialExtension injective present,put_self _ _ _,extension⟩

open Classical in
private theorem draw_alignment (Q : Nat) (seedTable : Seed) (iv : Digest32)
    (purpose : Purpose) (input : Node) (log : PublicLog) (key : Key Q)
    (pc : PublicCompressionCouplingJoint.Cache Node) (qc final : PublicCompressionCouplingJoint.Cache (Key Q))
    (stream : List Digest32) (nextLog : PublicLog) (answer : Digest32)
    (updated : PublicCompressionCouplingJoint.Cache (Key Q)) (remaining : List Digest32)
    (label : coordinateLabel seedTable key=input)
    (execution : run (.draw key (fun d => .ret (n:=0) (observe log input d,d))) qc stream=
      some ((nextLog,answer),updated,remaining))
    (related : Related (coordinateLabel seedTable) pc qc)
    (extension : Extends updated final) (injective : InjectiveOn (coordinateLabel seedTable) final) :
    ∃ pc', run (PublicCompressionProgram.queryCalls iv (.primitive purpose input)) pc stream=
      some (answer,pc',remaining) ∧ Related (coordinateLabel seedTable) pc' updated ∧
      pc' input=some answer ∧ Extends updated final ∧ nextLog=observe log input answer := by
  let q : PublicCompressionCouplingMixed.Computation Q Digest32 1 :=
    .draw key (fun d => .ret d)
  let payload := fun d => (DuplexPublicSimulator.observe log input d,d)
  have mapped : (run q qc stream).map (fun result => (payload result.1,result.2.1,result.2.2)) =
      some ((nextLog,answer),updated,remaining) := by
    exact (run_mixed_map payload q qc stream).symm.trans
      (by simpa only [q,payload,PublicCompressionCouplingMixed.Computation.map] using execution)
  have recovered : run q qc stream=some (answer,updated,remaining) ∧
      nextLog=DuplexPublicSimulator.observe log input answer := by
    cases result : run q qc stream with
    | none => simp only [result,Option.map_none] at mapped; cases mapped
    | some triple =>
      rcases triple with ⟨digest,cache,rest⟩
      simp only [result,Option.map_some,Option.some.injEq,Prod.mk.injEq,payload] at mapped
      obtain ⟨⟨logEq,answerEq⟩,cacheEq,streamEq⟩ := mapped
      exact ⟨by simp only [answerEq,cacheEq,streamEq],
        logEq.symm.trans (congrArg (DuplexPublicSimulator.observe log input) answerEq)⟩
  obtain ⟨pc',realRun,newRelated,stored,newExtension⟩ :=
    matched_draw (coordinateLabel seedTable) key pc qc final stream answer updated remaining
      recovered.1 related extension injective
  exact ⟨pc',by simpa only [PublicCompressionProgram.queryCalls,label] using realRun,
    newRelated,by simpa only [label] using stored,newExtension,recovered.2⟩

open Classical in
theorem actual_primitive_stream_alignment (Q : Nat) (seedTable : Seed) (iv : Digest32)
    (purpose : Purpose) (input : Node) (log : PublicLog)
    (pc : PublicCompressionCouplingJoint.Cache Node) (qc final : PublicCompressionCouplingJoint.Cache (Key Q))
    (stream : List Digest32) (nextLog : PublicLog) (answer : Digest32)
    (updated : PublicCompressionCouplingJoint.Cache (Key Q)) (remaining : List Digest32)
    (execution : run (primitiveCalls Q log input) qc stream=some ((nextLog,answer),updated,remaining))
    (related : Related (coordinateLabel seedTable) pc qc)
    (extension : Extends updated final) (injective : InjectiveOn (coordinateLabel seedTable) final)
    (authentic : NonterminalAuthentic seedTable log) (covered : LogCovered pc log) :
    ∃ pc', run (PublicCompressionProgram.queryCalls iv (.primitive purpose input)) pc stream=
      some (answer,pc',remaining) ∧ Related (coordinateLabel seedTable) pc' updated ∧
      LogCovered pc' nextLog ∧ Extends updated final := by
  cases hit : lookup log input with
  | some digest =>
    simp only [primitiveCalls,hit,run,Option.some.injEq,Prod.mk.injEq] at execution
    obtain ⟨⟨logEq,answerEq⟩,cacheEq,streamEq⟩ := execution
    subst nextLog
    subst answer
    subst updated
    subst remaining
    have realHit := covered input digest (lookup_mem hit)
    refine ⟨pc,by simp only [PublicCompressionProgram.queryCalls]; rw [run_hit realHit]; rfl,related,?_,extension⟩
    intro node value member
    simp only [DuplexPublicSimulator.observe,List.mem_cons,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | member
    · exact realHit
    · exact covered node value member
  | none =>
    have draw : ∃ pc', run (PublicCompressionProgram.queryCalls iv (.primitive purpose input)) pc stream=
        some (answer,pc',remaining) ∧ Related (coordinateLabel seedTable) pc' updated ∧
        pc' input=some answer ∧ Extends updated final ∧ nextLog=observe log input answer := by
      cases found : privateKey Q log input with
      | some key =>
        have label : coordinateLabel seedTable (.inr key)=input :=
          terminalLabel_witness (privateKey_coordinateWitness seedTable authentic found)
        exact draw_alignment Q seedTable iv purpose input log (.inr key) pc qc final stream nextLog answer
          updated remaining label (by simpa only [primitiveCalls,hit,found] using execution)
          related extension injective
      | none =>
        exact draw_alignment Q seedTable iv purpose input log (.inl input) pc qc final stream nextLog answer
          updated remaining rfl (by simpa only [primitiveCalls,hit,found] using execution)
          related extension injective
    obtain ⟨pc',realExecution,newRelated,stored,newExtension,logEq⟩ := draw
    refine ⟨pc',realExecution,newRelated,?_,newExtension⟩
    intro node value member
    rw [logEq] at member
    simp only [DuplexPublicSimulator.observe,List.mem_cons,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | member
    · exact stored
    · exact run_extends _ pc stream realExecution (covered node value member)

#print axioms matched_draw
#print axioms actual_primitive_stream_alignment
end Whir.PublicCompressionCouplingPrimitiveStream
