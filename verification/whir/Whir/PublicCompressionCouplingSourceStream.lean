import Whir.PublicCompressionCouplingConstructionStream
import Whir.PublicCompressionCouplingGoodGraph
import Whir.PublicCompressionCouplingActualJoint

/-! Whole adaptive source alignment for the literal fresh-answer joint sampler.
Completed ideal cache tables instantiate every operational invariant. -/
namespace Whir.PublicCompressionCouplingSourceStream
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open TypedFiatShamirGame RawOracleCoupling
open TypedOracleCompiler (Sampling)
open PublicCompressionCouplingMixed PublicCompressionCouplingJoint
open PublicCompressionCouplingStreams PublicCompressionCouplingRelabelCache
open PublicCompressionCouplingRecognition PublicCompressionCouplingPrimitiveStream
open PublicCompressionCouplingConstructionStream
set_option backward.isDefEq.respectTransparency false

 theorem run_bind_split {K R S : Type} [DecidableEq K] {n m : Nat}
    (p : PublicCompressionCouplingJoint.Computation K R n)
    (next : R → PublicCompressionCouplingJoint.Computation K S m)
    (cache : PublicCompressionCouplingJoint.Cache K) (stream : List Digest32)
    {result : S} {final : PublicCompressionCouplingJoint.Cache K} {remaining : List Digest32}
    (execution : run (Sampling.bind p next) cache stream=some (result,final,remaining)) :
    ∃ value updated rest, run p cache stream=some (value,updated,rest) ∧
      run (next value) updated rest=some (result,final,remaining) := by
  rw [run_bind] at execution
  cases found : run p cache stream with
  | none => simp only [found] at execution; cases execution
  | some triple =>
    rcases triple with ⟨value,updated,rest⟩
    exact ⟨value,updated,rest,rfl,by simpa only [found] using execution⟩

open Classical in
 theorem actual_source_stream_alignment {R : Type} (Q : Nat) (seedTable : Seed)
    (ro : RawKey Q → Digest32) (iv : Digest32) (p : Program R)
    (log : PublicLog) (budget : Nat) (cap : budget ≤ Q) (counted : Counts budget p)
    (pc : PublicCompressionCouplingJoint.Cache Node)
    (qc final : PublicCompressionCouplingJoint.Cache (Key Q)) (stream : List Digest32)
    (result : View R × List InspectedConstruction)
    (updated : PublicCompressionCouplingJoint.Cache (Key Q)) (remaining : List Digest32)
    (execution : run (causalCompile Q iv log p budget cap counted) qc stream=
      some (result,updated,remaining))
    (related : Related (coordinateLabel seedTable) pc qc)
    (extension : Extends updated final) (injective : InjectiveOn (coordinateLabel seedTable) final)
    (consistent : ∀ key answer, final key=some answer → oracle seedTable ro key=answer)
    (authentic : NonterminalAuthentic seedTable log) (covered : LogCovered pc log) :
    ∃ realResult pc', run (PublicCompressionProgram.compile iv p budget counted) pc stream=
      some (realResult,pc',remaining) ∧ realResult.view=result.1 ∧
      Related (coordinateLabel seedTable) pc' updated := by
  induction p generalizing log budget pc qc stream result updated remaining with
  | done value =>
    simp only [causalCompile,run,Option.some.injEq,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl,rfl⟩ := execution
    exact ⟨⟨⟨[],value⟩,0,0,0⟩,pc,rfl,rfl,related⟩
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [causalCompile,run_pad] at execution
      obtain ⟨answer,first,rest,firstRun,tail⟩ := run_bind_split _ _ qc stream execution
      obtain ⟨tailResult,tailRun,resultEq⟩ := mixed_map_recover _ _ first rest tail
      have firstExtension : Extends first final := by
        intro key digest stored
        exact extension key digest (run_extends _ first rest tailRun stored)
      obtain ⟨firstReal,realQuery,firstRelated,firstCovered,_⟩ := actual_primitive_stream_alignment
        Q seedTable iv purpose input log pc qc final stream answer.1 answer.2 first rest firstRun
        related firstExtension injective authentic covered
      have evalEq := run_eval _ qc stream firstRun (oracle seedTable ro)
        (fun key digest stored => consistent key digest (firstExtension key digest stored))
      have firstAuthentic : NonterminalAuthentic seedTable answer.1 := by
        rw [← evalEq]
        exact primitiveCalls_authentic Q seedTable ro log authentic input
      obtain ⟨tailReal,lastReal,realTail,viewEq,lastRelated⟩ := ih answer.2 answer.1
        (budget-1) (by omega) (counted.2 _) firstReal first rest tailResult updated remaining
        tailRun firstRelated extension firstAuthentic firstCovered
      refine ⟨prepend (.primitive purpose input) answer.2 0 tailReal,lastReal,?_,?_,lastRelated⟩
      · simp only [PublicCompressionProgram.compile,run_pad,run_bind,realQuery,run_real_map,Query.cost,realTail,Option.map_some]
      · have projected := congrArg (fun pair : View R × List InspectedConstruction => pair.1) resultEq
        simpa only [prepend,DuplexRawProgram.observe,viewEq] using projected
    | construction coordinate valid =>
      simp only [causalCompile,run_pad] at execution
      obtain ⟨construction,first,rest,firstRun,tail⟩ := run_bind_split _ _ qc stream execution
      obtain ⟨tailResult,tailRun,resultEq⟩ := mixed_map_recover _ _ first rest tail
      have firstExtension : Extends first final := by
        intro key digest stored
        exact extension key digest (run_extends _ first rest tailRun stored)
      obtain ⟨firstReal,realQuery,firstRelated,_⟩ := actual_construction_stream_alignment
        Q seedTable ro iv coordinate valid (counted.1.trans cap) pc qc final stream construction
        first rest firstRun related firstExtension injective consistent
      have firstCovered : LogCovered firstReal log := by
        intro node answer member
        exact run_extends _ pc stream realQuery (covered node answer member)
      obtain ⟨tailReal,lastReal,realTail,viewEq,lastRelated⟩ := ih construction.advertised log
        (budget-pathCost coordinate) (by omega) (counted.2 _) firstReal first rest tailResult updated
        remaining tailRun firstRelated extension authentic firstCovered
      refine ⟨prepend (.construction coordinate valid) construction.advertised 0 tailReal,lastReal,?_,?_,lastRelated⟩
      · simp only [PublicCompressionProgram.compile,run_pad,run_bind,realQuery,run_real_map,Query.cost,realTail,Option.map_some]
      · have projected := congrArg (fun pair : View R × List InspectedConstruction => pair.1) resultEq
        simpa only [prepend,DuplexRawProgram.observe,viewEq] using projected

open Classical in
 theorem actual_good_source_stream_alignment {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) (seedTable : Seed) (ro : RawKey Q → Digest32)
    (stream : List Digest32) (result : View R × List InspectedConstruction)
    (final : PublicCompressionCouplingJoint.Cache (Key Q)) (remaining : List Digest32)
    (execution : run (causalCompile Q iv [] p Q (by rfl) counted) (fun _ => none) stream=
      some (result,final,remaining))
    (consistent : ∀ key answer, final key=some answer → oracle seedTable ro key=answer)
    (quiet : causalBad Q iv p counted (oracle seedTable ro)=false) :
    ∃ realResult pc', run (PublicCompressionProgram.compile iv p Q counted) (fun _ => none) stream=
      some (realResult,pc',remaining) ∧ realResult.view=result.1 := by
  have tableEq := run_table _ (fun _ => none) stream execution (oracle seedTable ro) consistent
  have injective := actual_good_cache_label_injective Q iv p counted seedTable ro quiet
  rw [tableEq] at injective
  obtain ⟨realResult,pc',realRun,viewEq,_⟩ := actual_source_stream_alignment Q seedTable ro iv p []
    Q (by rfl) counted (fun _ => none) (fun _ => none) final stream result final remaining execution
    (empty_related _)
    (by intro key answer stored; exact stored) injective consistent
    (by intro node answer impossible; cases impossible) (by intro node answer impossible; cases impossible)
  exact ⟨realResult,pc',realRun,viewEq⟩

open Classical in
 theorem actual_joint_good_view {R : Type} (Q : Nat) (iv : Digest32)
    (p : Program R) (counted : Counts Q p) {trace} {pair}
    (execution : Sampling.Runs (PublicCompressionCouplingActualJoint.actualJoint Q iv p counted) trace pair)
    (table : Key Q → Digest32)
    (quiet : causalBad Q iv p counted (overlay pair.2.2 table)=false) :
    pair.1.1.view=pair.2.1.1 := by
  have shared := runs_draws execution
  rw [PublicCompressionCouplingActualJoint.actualJoint,joint_stream] at shared
  cases realRun : run (PublicCompressionProgram.compile iv p Q counted)
      (fun _ => none) (trace.map (fun entry => entry.2)) with
  | none => simp only [realRun] at shared; cases shared
  | some realTriple =>
    rcases realTriple with ⟨realResult,realCache,realRemaining⟩
    cases idealRun : run (causalCompile Q iv [] p Q (by rfl) counted)
        (fun _ => none) (trace.map (fun entry => entry.2)) with
    | none => simp only [realRun,idealRun] at shared; cases shared
    | some idealTriple =>
      rcases idealTriple with ⟨idealResult,idealCache,idealRemaining⟩
      simp only [realRun,idealRun,Option.some.injEq] at shared
      subst pair
      let completed := overlay idealCache table
      let seedTable : Seed := fun node => completed (.inl node)
      let ro : RawKey Q → Digest32 := fun key => completed (.inr key)
      have split : oracle seedTable ro=completed := by
        funext key
        cases key <;> rfl
      have consistent : ∀ key answer, idealCache key=some answer → oracle seedTable ro key=answer := by
        intro key answer stored
        rw [split]
        simp only [completed,overlay,stored,Option.getD_some]
      have good : causalBad Q iv p counted (oracle seedTable ro)=false := by
        simpa only [split,completed] using quiet
      obtain ⟨alignedResult,alignedCache,alignedRun,viewEq⟩ := actual_good_source_stream_alignment
        Q iv p counted seedTable ro _ idealResult idealCache idealRemaining idealRun consistent good
      have resultEq := realRun.symm.trans alignedRun
      simp only [Option.some.injEq,Prod.mk.injEq] at resultEq
      exact resultEq.1 ▸ viewEq

#print axioms actual_joint_good_view

#print axioms actual_source_stream_alignment
#print axioms actual_good_source_stream_alignment
end Whir.PublicCompressionCouplingSourceStream
