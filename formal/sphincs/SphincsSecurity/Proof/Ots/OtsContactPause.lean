import SphincsSecurity.Proof.Ots.OtsContactTrace
import SphincsSecurity.Proof.Base.QueryPauseInvariant
namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts

variable (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)

def Stopped (trace : Trace) : Prop := (contacts parameter words frontier trace).Nonempty

noncomputable def pause {Result : Type} (computation : OracleComp OracleWorld Result) :=
  QueryPause.run (Stopped parameter words frontier)
    (fun input answer history => history * hashObservationTrace input answer) computation 1

theorem pause_card_le_one {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : Trace × OracleComp OracleWorld Result) (hresult : result ∈ support (pause parameter words frontier computation)) :
    (contacts parameter words frontier result.1).card ≤ 1 := by
  apply QueryPause.run_invariant (Stopped parameter words frontier) _
    (fun trace => (contacts parameter words frontier trace).card ≤ 1) _ computation 1 _ result hresult
  · intro trace _ hstop input answer
    have hempty : contacts parameter words frontier trace = ∅ := Finset.not_nonempty_iff_eq_empty.mp hstop
    have h := contacts_step_card_le parameter words frontier trace input answer
    simpa only [hempty, Finset.card_empty, Nat.zero_add] using h
  · simp only [contacts_one, Finset.card_empty, Nat.zero_le]

theorem pause_stopped_or_finished {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : Trace × OracleComp OracleWorld Result) (hresult : result ∈ support (pause parameter words frontier computation)) :
    Stopped parameter words frontier result.1 ∨ ∃ value, result.2 = pure value :=
  QueryPause.run_stopped_or_finished (Stopped parameter words frontier) _ computation 1 result hresult

theorem pause_new_contact {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : Trace × OracleComp OracleWorld Result) (hresult : result ∈ support (pause parameter words frontier computation))
    (after : Trace) (htwo : 2 ≤ (contacts parameter words frontier (result.1 * after)).card) :
    ∃ address, address ∉ contacts parameter words frontier result.1 ∧ address ∈ contacts parameter words frontier after :=
  new_contact_of_two parameter words frontier result.1 after
    (pause_card_le_one parameter words frontier computation result hresult) htwo

end SphincsSecurity.Concrete.OtsContactTrace
