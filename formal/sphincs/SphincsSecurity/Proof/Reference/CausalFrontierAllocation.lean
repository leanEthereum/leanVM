import SphincsSecurity.Proof.Reference.CausalFrontierProgram
import SphincsSecurity.Proof.Reference.QueryAllocation
namespace SphincsSecurity.Concrete.CausalFrontierProgram

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot

def IsHash : OracleWorld.Domain → Prop := (· matches .inr _)

instance : DecidablePred IsHash := fun input => by unfold IsHash; infer_instance

structure TraceCharge (parameter : PublicParameter) where
  selected : OracleWorld.Domain → Prop
  decidable : DecidablePred selected
  cost : SigningBoundaryTrace → Nat
  cost_mul : ∀ first second, cost (first * second) = cost first + cost second
  uniform : ∀ input, ¬selected (.inl input)
  step : ∀ input answer, (if selected input then 1 else 0) ≤ cost (signingBoundaryTrace parameter input answer)

namespace TraceCharge

variable {parameter : PublicParameter} (charge : TraceCharge parameter)

noncomputable instance : DecidablePred charge.selected := charge.decidable

theorem lift_prob_queryBound {Result : Type} (computation : ProbComp Result) :
    (liftM computation : OracleComp OracleWorld Result).IsQueryBoundP charge.selected 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      change ((liftM (OracleWorld.query (.inl input)) >>= fun answer => liftM (next answer)) :
        OracleComp OracleWorld Result).IsQueryBoundP charge.selected 0
      simp only [isQueryBoundP_query_bind_iff, charge.uniform, not_false_eq_true, true_or, ↓reduceIte, true_and]
      exact ih

private theorem withTrace_run {Input Trace : Type} {spec : OracleSpec Input} [Monoid Trace]
    (trace : (input : spec.Domain) → spec.Range input → Trace) (input : spec.Domain) :
    ((QueryImpl.id' spec).withTrace trace input).run =
      (fun answer => (answer, trace input answer)) <$> (liftM (spec.query input) : OracleComp spec _) := by
  simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]

theorem worldTrace_counted_le (input : OracleWorld.Domain)
    (result : (OracleWorld.Range input × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      ((QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter) input).run)) :
    result.2 ≤ charge.cost result.1.2 := by
  rw [withTrace_run, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  rw [QueryCap.counted_query, support_map] at horiginal
  obtain ⟨answer, _, rfl⟩ := horiginal
  exact charge.step input answer

theorem boundary_counted_le {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : (Result × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected (boundaryComputation parameter computation))) :
    result.2 ≤ charge.cost result.1.2 :=
  QueryCap.counted_writer_simulate_le _ charge.cost charge.cost_mul _
    (worldTrace_counted_le charge) computation result hresult

theorem adversaryImpl_counted_le (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (input : (OracleWorld + SigningSpec).Domain)
    (result : ((OracleWorld + SigningSpec).Range input × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      (adversaryImpl parameter root external ftsSecret words frontier input).run)) : result.2 ≤ charge.cost result.1.2 := by
  cases input with
  | inl input => exact worldTrace_counted_le charge input result hresult
  | inr message =>
      rw [adversaryImpl_signing, WriterT.run_mk] at hresult
      have hzero := QueryCap.counted_le_of_queryBound _ _ 0 (lift_prob_queryBound charge _) result hresult
      exact hzero.trans (Nat.zero_le _)

theorem adversaryRun_counted_le {Result : Type} (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (result : ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      (adversaryRun parameter root external ftsSecret words frontier computation))) : result.2 ≤ charge.cost result.1.2 :=
  QueryCap.counted_writer_simulate_le _ charge.cost charge.cost_mul _
    (adversaryImpl_counted_le charge root external ftsSecret words frontier) (OtsPrefix.logged computation) result hresult

theorem gameRest_counted_le (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      (gameRest parameter root external ftsSecret words frontier adversary))) : result.2 ≤ charge.cost result.1.2 := by
  simp only [gameRest, QueryCap.counted_bind, QueryCap.counted_pure, bind_assoc, pure_bind, Nat.add_zero] at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨second, hsecond, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  rw [charge.cost_mul]
  exact Nat.add_le_add (adversaryRun_counted_le charge root external ftsSecret words frontier _ first hfirst)
    (boundary_counted_le charge _ second hsecond)

theorem game_counted_le (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted charge.selected
      (game parameter external ftsSecret words frontier adversary))) : result.2 ≤ charge.cost result.1.2 := by
  rw [game, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  have h := gameRest_counted_le charge _ external ftsSecret words frontier adversary original horiginal
  simp only [charge.cost_mul]
  omega

end TraceCharge

noncomputable def hashTraceCharge (parameter : PublicParameter) : TraceCharge parameter where
  selected := IsHash
  decidable := inferInstance
  cost := SigningBoundaryTrace.hashCalls
  cost_mul := SigningBoundaryTrace.hashCalls_mul
  uniform := by intro input; simp [IsHash]
  step := by
    intro input answer
    cases input <;> simp [IsHash, signingBoundaryTrace_hashCalls_eq]

theorem game_counted_le (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsHash
      (game parameter external ftsSecret words frontier adversary))) : result.2 ≤ result.1.2.hashCalls :=
  TraceCharge.game_counted_le (hashTraceCharge parameter) external ftsSecret words frontier adversary result hresult

end SphincsSecurity.Concrete.CausalFrontierProgram
