import SphincsSecurity.Proof.Ots.OtsContactAllocation
namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts

variable (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)

noncomputable def splitRun {Result : Type} (computation : OracleComp OracleWorld Result) :
    OracleComp OracleWorld (Trace × (Result × Trace)) := do
  let middle ← pause parameter words frontier computation
  let tail ← QueryPause.traced hashObservationTrace middle.2
  pure (middle.1, tail)

theorem splitRun_trace {Result : Type} (computation : OracleComp OracleWorld Result) :
    (fun result => (result.2.1, result.1 * result.2.2)) <$> splitRun parameter words frontier computation =
      QueryPause.traced hashObservationTrace computation := by
  have h := QueryPause.trace_resume hashObservationTrace (Stopped parameter words frontier) computation 1
  have hmap : (fun result : Result × Trace => (result.1, 1 * result.2)) <$>
      QueryPause.traced hashObservationTrace computation = QueryPause.traced hashObservationTrace computation := by
    simp only [one_mul]
    change id <$> _ = _
    exact id_map _
  simpa only [splitRun, pause, map_bind, map_pure] using h.trans hmap

theorem splitRun_forget {Result : Type} (computation : OracleComp OracleWorld Result) :
    (fun result => result.2.1) <$> splitRun parameter words frontier computation = computation := by
  have h := congrArg (Functor.map Prod.fst) (splitRun_trace parameter words frontier computation)
  simpa only [Functor.map_map, QueryPause.traced_forget] using h

theorem splitRun_two_contacts {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : Trace × (Result × Trace)) (hresult : result ∈ support (splitRun parameter words frontier computation))
    (htwo : 2 ≤ (contacts parameter words frontier (result.1 * result.2.2)).card) :
    Stopped parameter words frontier result.1 ∧
      ∃ address, address ∉ contacts parameter words frontier result.1 ∧ address ∈ contacts parameter words frontier result.2.2 := by
  simp only [splitRun, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨middle, hmiddle, tail, htail, rfl⟩ := hresult
  refine ⟨?_, pause_new_contact parameter words frontier computation middle hmiddle tail.2 htwo⟩
  rcases pause_stopped_or_finished parameter words frontier computation middle hmiddle with hstop | ⟨value, hvalue⟩
  · exact hstop
  · rw [hvalue, QueryPause.traced_pure, mem_support_pure_iff] at htail
    subst tail
    simp only [mul_one] at htwo
    have hone := pause_card_le_one parameter words frontier computation middle hmiddle
    omega

theorem splitRun_game_cost (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (adversary : Adversary)
    (result : Trace × ((Bool × SigningBoundaryTrace) × Trace))
    (hresult : result ∈ support (splitRun parameter words frontier
      (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))) :
    (result.1 * result.2.2).toList.length ≤ result.2.1.2.hashCalls := by
  apply traced_game_cost parameter external ftsSecret words frontier adversary (result.2.1, result.1 * result.2.2)
  rw [← splitRun_trace parameter words frontier, support_map]
  exact ⟨result, hresult, rfl⟩

end SphincsSecurity.Concrete.OtsContactTrace
