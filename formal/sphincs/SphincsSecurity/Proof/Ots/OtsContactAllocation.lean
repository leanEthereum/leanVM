import SphincsSecurity.Proof.Ots.OtsContactPause
import SphincsSecurity.Proof.Base.QueryPauseTrace
namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts

noncomputable def prefixCalls (segment : OtsPrefix) (trace : Trace) : Nat :=
  QueryCap.calls segment.Selects (trace.toList.map fun entry => (.inr entry.1 : OracleWorld.Domain))

theorem prefixCalls_one (segment : OtsPrefix) : prefixCalls segment 1 = 0 := rfl

theorem prefixCalls_mul (segment : OtsPrefix) (first second : Trace) :
    prefixCalls segment (first * second) = prefixCalls segment first + prefixCalls segment second := by
  simp only [prefixCalls, FreeMonoid.toList_mul, List.map_append, QueryCap.calls, List.countP_append]

theorem prefixCalls_step (segment : OtsPrefix) (input : OracleWorld.Domain) (answer : OracleWorld.Range input) (trace : Trace) :
    prefixCalls segment (hashObservationTrace input answer * trace) = (if segment.Selects input then 1 else 0) + prefixCalls segment trace := by
  cases input with
  | inl input => simp only [hashObservationTrace, one_mul, OtsPrefix.Selects, if_false, Nat.zero_add]
  | inr bytes =>
      simp only [prefixCalls, hashObservationTrace, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
        List.map_cons, QueryCap.calls_cons]

theorem traced_hash_counted {Result : Type} (computation : OracleComp OracleWorld Result) :
    (fun result => (result.1, result.2.toList.length)) <$> QueryPause.traced hashObservationTrace computation =
      QueryCap.counted CausalFrontierProgram.IsHash computation := by
  apply QueryPause.traced_counted hashObservationTrace CausalFrontierProgram.IsHash (fun trace => trace.toList.length) rfl
  intro input answer trace
  cases input <;> simp only [hashObservationTrace, one_mul, CausalFrontierProgram.IsHash, reduceCtorEq, ↓reduceIte,
    Nat.zero_add, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.length_append, List.length_singleton]

private theorem hash_calls_map (entries : List (HashInput × HashOutput)) :
    QueryCap.calls CausalFrontierProgram.IsHash (entries.map fun entry => (.inr entry.1 : OracleWorld.Domain)) = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, QueryCap.calls_cons, CausalFrontierProgram.IsHash, ↓reduceIte, ih, List.length_cons, Nat.add_comm]

theorem prefixCalls_allocation (parameter : PublicParameter) (words : OtsReferenceWords)
    (addresses : Finset OtsPrefix.ChainAddress) (trace : Trace) :
    (∑ address ∈ addresses, prefixCalls (OtsPrefix.atAddress parameter words address) trace) ≤ trace.toList.length := by
  simpa only [prefixCalls, hash_calls_map] using
    OtsPrefix.allocation_le parameter words addresses (trace.toList.map fun entry => (.inr entry.1 : OracleWorld.Domain))

theorem restartCharge_allocation (parameter : PublicParameter) (words : OtsReferenceWords)
    (addresses : Finset OtsPrefix.ChainAddress) (before after : Trace) :
    (∑ address ∈ addresses, (prefixCalls (OtsPrefix.atAddress parameter words address) before +
      2 * prefixCalls (OtsPrefix.atAddress parameter words address) after)) ≤ before.toList.length + 2 * after.toList.length := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add (prefixCalls_allocation parameter words addresses before)
    (Nat.mul_le_mul_left 2 (prefixCalls_allocation parameter words addresses after))

theorem restartCharge_le_budget (parameter : PublicParameter) (words : OtsReferenceWords)
    (addresses : Finset OtsPrefix.ChainAddress) (before after : Trace) (budget : Nat)
    (hbudget : (before * after).toList.length ≤ budget) :
    (∑ address ∈ addresses, (prefixCalls (OtsPrefix.atAddress parameter words address) before +
      2 * prefixCalls (OtsPrefix.atAddress parameter words address) after)) ≤ 2 * budget := by
  apply (restartCharge_allocation parameter words addresses before after).trans
  simp only [FreeMonoid.toList_mul, List.length_append] at hbudget
  omega

theorem traced_game_cost (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Trace)
    (hresult : result ∈ support (QueryPause.traced hashObservationTrace
      (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))) : result.2.toList.length ≤ result.1.2.hashCalls := by
  apply CausalFrontierProgram.game_counted_le parameter external ftsSecret words frontier adversary
    (result.1, result.2.toList.length)
  rw [← traced_hash_counted, support_map]
  exact ⟨result, hresult, rfl⟩

end SphincsSecurity.Concrete.OtsContactTrace
