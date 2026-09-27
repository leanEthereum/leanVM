import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.IdealStatement

/-!
# Evaluating against a fixed answer function

The random oracle's support is characterized by total answer functions: a value comes out of the
lazy oracle exactly when some `f : QueryImpl HashSpec Id` agreeing with the cache evaluates the
computation to it (`exists_agreesWithFn_evalWithAnswerFn_eq_iff_mem_support`). So every structural
fact this development needs is a fact about `evalWithAnswerFn f`, where `f` answers each input the
same way however often it is asked and in whatever order.

That is what makes the shape of the algorithms tractable: under `evalWithAnswerFn f` a family of
independent computations may be assembled in any order, which is false at the level of
computations, `sequenceFin` fixing one.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable {α : Type} (f : QueryImpl HashSpec Id)

/-- Assembling a family commutes with evaluation. -/
@[simp]
theorem evalWithAnswerFn_sequenceFin {n : Nat} (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn f (sequenceFin computation) = fun index => evalWithAnswerFn f (computation index) := by
  induction n with
  | zero => funext index; exact index.elim0
  | succ n ih =>
      funext index
      simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      cases index using Fin.cases <;> rfl

@[simp]
theorem evalWithAnswerFn_sequenceLayers (computation : Layer → OracleComp HashSpec (Option α)) :
    evalWithAnswerFn f (sequenceLayers computation) =
      sequenceFin (m := Option) (fun lay => evalWithAnswerFn f (computation lay)) := by
  simp only [sequenceLayers, evalWithAnswerFn_bind]
  cases hb : evalWithAnswerFn f (computation bottomLayer) <;>
    cases h3 : evalWithAnswerFn f (computation ⟨3, by decide⟩) <;>
    cases h2 : evalWithAnswerFn f (computation ⟨2, by decide⟩) <;>
    cases hm : evalWithAnswerFn f (computation middleLayer) <;>
    cases ht : evalWithAnswerFn f (computation topLayer) <;>
    have hmL := hm <;>
    have htL := ht <;>
    change evalWithAnswerFn f (computation ⟨4, by decide⟩) = _ at hb <;>
    change evalWithAnswerFn f (computation (3 : Fin 5)) = _ at h3 <;>
    change evalWithAnswerFn f (computation (2 : Fin 5)) = _ at h2 <;>
    change evalWithAnswerFn f (computation (1 : Fin 5)) = _ at hm <;>
    change evalWithAnswerFn f (computation (0 : Fin 5)) = _ at ht <;>
    rw [hb] <;>
    change evalWithAnswerFn f (computation (4 : Fin 5)) = _ at hb <;>
    simp only [numLayers, sequenceFin] <;>
    rw [ht] <;>
    simp [evalWithAnswerFn_bind, evalWithAnswerFn_pure, hb, h3, h2, hm, hmL, htL] <;> rfl

end SphincsSecurity.Concrete
