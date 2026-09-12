import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

/-!
# Charging one query at a time

The tool every strategy's bound instantiates: if an event needs some oracle answer to satisfy a
predicate fixed at its input, and one fresh answer satisfies it with probability at most `eps`, then
a computation making at most `q` hash queries produces such an answer with probability at most
`q * eps`.

The cache is what the statement talks about, since it is the random oracle's own state: a hit is an
entry whose answer satisfies the predicate at its input. A repeated query cannot add a hit, so
counting every query rather than every distinct one only weakens the bound.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

/-- A bound on a bind bounds each continuation. VCVio composes bounds, `n` then `m` giving `n + m`;
what the reduction needs is the other direction, to bound what runs after key generation by what
bounds the whole game. -/
theorem isQueryBoundP_of_bind {α β : Type} {oa : OracleComp OracleWorld α}
    {k : α → OracleComp OracleWorld β} {q : Nat}
    (h : IsQueryBoundP (oa >>= k) (· matches Sum.inr _) q) :
    ∀ x ∈ support oa, IsQueryBoundP (k x) (· matches Sum.inr _) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro x' hx'
      simp only [support_pure, Set.mem_singleton_iff] at hx'
      subst hx'
      simpa using h
  | query_bind t mx ih =>
      intro x hx
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
      obtain ⟨u, hu⟩ := (mem_support_bind_iff _ _ _).mp hx
      exact (ih u (h.2 u) x hu.2).mono (by split_ifs <;> omega)

end SphincsSecurity
