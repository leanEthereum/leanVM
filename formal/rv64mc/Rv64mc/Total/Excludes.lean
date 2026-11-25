/-
  Rv64mc.Total.Excludes

  What `Ascent.Total` rules out, as guards against a later weakening of the judgement: on a
  machine that never accepts, a state that only traps, only goes `wrong`, has no successor, or
  steps to itself forever is total for no obligation and no `Q`.

  ## Main results

  * `Total.not_of_trap`, `Total.not_of_wrong`, `Total.not_of_stuck`, `Total.not_of_loop`
-/

import Rv64mc.Total.Judgement

namespace Lprog.Ascent.Total

variable {σ : Type} {G Q : σ → Prop}

/-- A machine that only traps is total nowhere. -/
theorem not_of_trap (s : σ) : ¬ Total (fun _ o => o = .trap) (fun _ => False) G Q s := by
  intro h
  cases h with
  | done _ ha _ => exact ha
  | next _ ht _ _ _ => exact ht rfl

/-- A machine that only goes `wrong` is total nowhere. -/
theorem not_of_wrong (s : σ) : ¬ Total (fun _ o => o = .wrong) (fun _ => False) G Q s := by
  intro h
  cases h with
  | done _ ha _ => exact ha
  | next _ _ hw _ _ => exact hw rfl

/-- A machine with no step is total nowhere it does not accept. -/
theorem not_of_stuck (s : σ) : ¬ Total (fun _ _ => False) (fun _ => False) G Q s := by
  intro h
  cases h with
  | done _ ha _ => exact ha
  | next _ _ _ hex _ => obtain ⟨_, h⟩ := hex; exact h

/-- A machine that steps to itself forever is not total. -/
theorem not_of_loop {G Q : Unit → Prop} : ¬ Total (fun _ o => o = .ok ()) (fun _ => False) G Q () := by
  intro h
  obtain ⟨_, hi, -⟩ := h.diverge (fun _ => ()) rfl (fun _ => rfl)
  exact hi

end Lprog.Ascent.Total
