import LeanxmssProofs.Bytes

/-!
# From specifications to equations

Aeneas's `step` tactic proves Hoare triples `m ⦃ r => p r ⦄`; these turn one into an equation `m = ok r`.
-/

open Aeneas Aeneas.Std Result WP

namespace leanxmss.Proofs

theorem exists_ok_of_spec {α} {m : Result α} {p : α → Prop} (h : spec m p) : ∃ x, m = ok x ∧ p x := by
  cases m using Result.cases with
  | ret r => exact ⟨r, rfl, (spec_ok r).mp h⟩
  | vis i k => simp at h
  | div => simp at h

theorem eq_ok_of_spec {α} {m : Result α} {v : α} (h : spec m (fun x => x = v)) : m = ok v := by
  obtain ⟨x, hx, rfl⟩ := exists_ok_of_spec h; exact hx

end leanxmss.Proofs
