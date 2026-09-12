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

theorem boundaryRun_bind_query_bound {α β : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (q : Nat) (hbound : (computation >>= next).IsQueryBoundP (· matches .inr _) q)
    (cache : QueryCache HashSpec) (result : (α × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun parameter computation cache)) :
    result.1.2.hashCalls ≤ q ∧ (next result.1.1).IsQueryBoundP (· matches .inr _) (q - result.1.2.hashCalls) := by
  induction computation using OracleComp.inductionOn generalizing q cache result with
  | pure value =>
      simp only [boundaryRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hr
      subst result
      simpa only [SigningBoundaryTrace.hashCalls, FreeMonoid.toList_one, List.length_nil,
        Nat.sub_zero, pure_bind] using And.intro (Nat.zero_le q) hbound
  | query_bind input continuation ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at hbound
      rw [boundaryRun_bind, boundaryRun_query, mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      rw [support_map] at hmiddle
      obtain ⟨source, _, rfl⟩ := hmiddle
      rw [support_map] at hr
      obtain ⟨last, hlast, rfl⟩ := hr
      have htail := ih source.1 _ (hbound.2 source.1) source.2 last hlast
      rw [SigningBoundaryTrace.hashCalls_mul, signingBoundaryTrace_hashCalls_eq]
      cases input with
      | inl sample => simpa only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, Nat.zero_add] using htail
      | inr input =>
          have hpositive : 0 < q := hbound.1.resolve_left (by simp)
          simp only [↓reduceIte] at htail ⊢
          exact ⟨by omega, by simpa only [Nat.sub_sub] using htail.2⟩

end SphincsSecurity.Concrete
