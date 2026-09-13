import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.BoundaryMessageCost
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem SigningBoundaryTrace.hashCalls_mul (first second : SigningBoundaryTrace) :
    (first * second).hashCalls = first.hashCalls + second.hashCalls := by
  simp only [SigningBoundaryTrace.hashCalls, FreeMonoid.toList_mul, List.length_append]

theorem signingBoundaryTrace_hashCalls_eq (parameter : PublicParameter)
    (input : OracleWorld.Domain) (output : OracleWorld.Range input) :
    (signingBoundaryTrace parameter input output).hashCalls = if input matches .inr _ then 1 else 0 := by
  cases input <;> rfl

def BoundaryHashAtLeast {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cost : Nat) : Prop :=
  ∀ cache result, result ∈ support (boundaryRun parameter computation cache) → cost ≤ result.1.2.hashCalls

theorem boundaryHashAtLeast_zero {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) : BoundaryHashAtLeast parameter computation 0 := by
  intro _ _ _
  exact Nat.zero_le _

theorem BoundaryHashAtLeast.mono {α : Type} {parameter : PublicParameter}
    {computation : OracleComp OracleWorld α} {a b : Nat}
    (h : BoundaryHashAtLeast parameter computation a) (hba : b ≤ a) :
    BoundaryHashAtLeast parameter computation b := by
  intro cache result hr
  exact hba.trans (h cache result hr)

theorem boundaryHashAtLeast_bind {α β : Type} (parameter : PublicParameter)
    (first : OracleComp OracleWorld α) (second : α → OracleComp OracleWorld β) (a b : Nat)
    (hfirst : BoundaryHashAtLeast parameter first a)
    (hsecond : ∀ value, BoundaryHashAtLeast parameter (second value) b) :
    BoundaryHashAtLeast parameter (first >>= second) (a + b) := by
  intro cache result hr
  rw [boundaryRun_bind, mem_support_bind_iff] at hr
  obtain ⟨middle, hmiddle, hr⟩ := hr
  rw [support_map] at hr
  obtain ⟨last, hlast, rfl⟩ := hr
  exact (Nat.add_le_add (hfirst cache middle hmiddle) (hsecond middle.1.1 middle.2 last hlast)).trans_eq
    (SigningBoundaryTrace.hashCalls_mul _ _).symm

theorem boundaryHashAtLeast_hash (parameter : PublicParameter) (input : HashInput) :
    BoundaryHashAtLeast parameter (oracleHash input) 1 := by
  intro cache result hr
  change result ∈ support (boundaryRun parameter
    (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) cache) at hr
  rw [boundaryRun_query, support_map] at hr
  obtain ⟨source, _, rfl⟩ := hr
  exact le_refl _

theorem boundaryHashAtLeast_tweakableHash (traceParameter parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) :
    BoundaryHashAtLeast traceParameter
      (liftM (tweakableHash parameter domain payload : OracleComp HashSpec Digest)) 1 := by
  change BoundaryHashAtLeast traceParameter
    (oracleHash (tweakableHashInput parameter domain payload) >>= fun output => pure (truncateHash output)) 1
  exact boundaryHashAtLeast_bind traceParameter _ _ 1 0 (boundaryHashAtLeast_hash _ _)
    (fun _ => boundaryHashAtLeast_zero _ _)

theorem boundaryRun_count {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => ((result.1.1, result.1.2.hashCalls), result.2)) <$> boundaryRun parameter computation cache =
      (simulateQ romImpl (countHashQueries computation)).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [boundaryRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        map_pure, countHashQueries_pure]
      rfl
  | query_bind input next ih =>
      rw [boundaryRun_bind, boundaryRun_query, map_bind, bind_map_left,
        countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply bind_congr
      intro reply
      simp only [Functor.map_map, bind_pure_comp, simulateQ_map, StateT.run_map]
      rw [← ih]
      simp only [Functor.map_map, SigningBoundaryTrace.hashCalls_mul,
        signingBoundaryTrace_hashCalls_eq]
      cases input <;> rfl

theorem hashQueryBound_iff_boundaryRun {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat) :
    HashQueryBound computation cache q ↔
      ∀ result ∈ support (boundaryRun parameter computation cache), result.1.2.hashCalls ≤ q := by
  rw [hashQueryBound_iff_run, ← boundaryRun_count parameter computation cache]
  simp only [support_map, Set.forall_mem_image]

theorem boundaryRun_bind_query_bound {α β : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (q : Nat) (cache : QueryCache HashSpec) (hbound : HashQueryBound (computation >>= next) cache q)
    (result : (α × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun parameter computation cache)) :
    result.1.2.hashCalls ≤ q ∧ HashQueryBound (next result.1.1) result.2 (q - result.1.2.hashCalls) := by
  apply hashQueryBound_bind computation next cache q hbound ((result.1.1, result.1.2.hashCalls), result.2)
  rw [← boundaryRun_count parameter computation cache, support_map]
  exact ⟨result, hr, rfl⟩

end SphincsSecurity.Concrete
