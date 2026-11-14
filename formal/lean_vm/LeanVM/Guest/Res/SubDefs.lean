/-
  LeanVM.Guest.Res.SubDefs

  The `sub` residuals' families, checked per certificate: a run inside a split, a read inside
  `child_claim_list_any`'s table, a read of the gap walk.
-/

module

public import LeanVM.Guest.EndExecRS
public import LeanVM.Guest.Res.AnyData
public import LeanVM.Guest.Res.MonoDefs
public import LeanVM.Guest.Res.ResGiven

/-!
# The `sub` residuals' families

`subB j x`: residual `x` of function `j` is no `sub` residual, or one of the three families
(`splitB`, `anyResB anyLink`, `monoResB`). `SubOk exc K`: certificate `K` is listed in `exc`, or
each of its residuals passes `subB` at its function's index, decided per certificate (`subOk_of`).
`resOpen_subOk`: given `SubOk resExc` of every certificate and the listed certificates' residuals,
no `sub` residual outside the families is left open.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The `sub` residuals' families.** -/
noncomputable def subB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => splitB j (.sub a bs) || anyResB anyLink j (.sub a bs) || monoResB j (.sub a bs)
  | _ => true

/-- **A certificate's `sub` residuals in the families**: it is listed in `exc`, or each is at its
function's index `j`. -/
def SubOk (exc : List Mode.Cert) (K : Mode.Cert) : Prop :=
  K ∈ exc ∨ ∃ j, j < nFns ∧ (fnOf j).entryPc = K.F.entry ∧ allV (fun l ↦ l.all (subB j)) K.F.res = true

theorem subOk_of {exc : List Mode.Cert} {K : Mode.Cert} {j : ℕ}
    (h : (decide (j < nFns) && (fnOf j).entryPc == K.F.entry && allV (fun l ↦ l.all (subB j)) K.F.res) = true) :
    SubOk exc K := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact Or.inr ⟨j, h.1.1, h.1.2, h.2⟩

theorem subOk_exc {exc : List Mode.Cert} {K : Mode.Cert} (h : K ∈ exc) : SubOk exc K := Or.inl h

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Res
open LeanVM.Guest.B2C (entryOf fn_of_idx)

@[expose] public section

/-- **No `sub` residual outside the families is left open**: each certificate's are in the
families, or the certificate is listed and its residuals given. -/
theorem resOpen_subOk {Ks : List Mode.Cert} {A : String → Bridge.FnAl} (hok : ∀ K ∈ Ks, SubOk resExc K)
    (hexc : ∀ K ∈ resExc, ResCert A K) :
    ResOpen Ks A fun j x ↦ (((∃ a bs, x = .sub a bs) ∧ splitB j x = false) ∧ anyResB anyLink j x = false) ∧
      monoResB j x = false := by
  intro r hr K hK i hi e j t x hx hp hin
  rcases hok K hK with hK' | ⟨j0, hj0, hent, hall⟩
  · exact hexc K hK' r hr i hi e j t x hx hin
  obtain rfl : j = j0 := by
    obtain ⟨_, -, -, -, -, -, -, -, -, hj⟩ := fn_of_idx t.idx
    refine fnOf_entry_inj hj hj0 ?_
    have := t.entry
    simp only [entryOf, t.idx] at this
    rw [this, hent]
  obtain ⟨⟨⟨⟨a, bs, rfl⟩, hs⟩, ha⟩, hm⟩ := hp
  cases hg : K.F.res.get i with
  | none => rw [hg] at hx; cases hx
  | some l =>
    rw [hg, Option.getD_some] at hx
    have hf := List.all_eq_true.mp (allV_get hall hg) _ hx
    simp [subB, hs, ha, hm] at hf

end

end LeanVM.Guest.EndExec
