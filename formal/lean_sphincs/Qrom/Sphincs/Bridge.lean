module

public import Qrom.Sphincs.Hidden

@[expose] public section

/-!
# The verifier on the hidden game's hash

The hash the hidden game answers in side state `s` agrees with the hash that answers every honest
input from the data, off the protected inputs (`Qrom.Sphincs.hidAnswer_eq`). So a verification that
reads no protected input runs as on that hash, with the same trace (`Qrom.Sphincs.eval_congr_trace`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- Two answer functions agreeing on the inputs a computation reads run it alike. -/
theorem eval_congr_trace {α : Type} (f g : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α)
    (H : ∀ l ∈ queriedInputs g oa, f l = g l) :
    evalWithAnswerFn f oa = evalWithAnswerFn g oa ∧ queriedInputs f oa = queriedInputs g oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨rfl, rfl⟩
  | query_bind t k ih =>
    rw [queriedInputs_query_bind] at H
    have ht : f t = g t := H t (List.mem_cons_self ..)
    have ⟨h1, h2⟩ := ih (g t) fun l hl ↦ H l (List.mem_cons_of_mem _ hl)
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_liftM_query, queriedInputs_query_bind, queriedInputs_query_bind]
    change evalWithAnswerFn f (k (f t)) = _ ∧ _
    rw [ht, h1, h2]
    exact ⟨rfl, rfl⟩

/-- The hash of the hidden game in side state `s`, on byte strings. -/
def hidFun (d : Data) (s : Log) (G : Input → HashOutput) : HashInput → HashOutput :=
  extend fun x ↦ (hidGame d).answer s G x

/-- Off the protected inputs, the hidden game's hash is the presampled one. -/
theorem hidAnswer_eq (d : Data) (s : Log) (G : Input → HashOutput) (l : HashInput)
    (hl : ∀ x, embed l = some x → ¬ Prot d s x) :
    hidFun d s G l = ovFun (d none) (hOf d) G l := by
  unfold hidFun ovFun extend
  cases he : embed l with
  | none => rfl
  | some x =>
    simp only
    rw [← show (presGame d).answer s G x = override (proc (d none)) G (hOf d) x from
      presGame_answer (d none) (hOf d) s G x]
    unfold OvGame.answer
    rw [hidGame_ov d s x (hl x he)]

end Qrom.Sphincs
