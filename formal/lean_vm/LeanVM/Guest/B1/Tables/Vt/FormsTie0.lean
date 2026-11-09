/-
  LeanVM.Guest.B1.Tables.Vt.FormsTie0

  Table 0's push and pull flushes are the guest's baked coordinate terms, by kernel evaluation
  of their canonical forms over `K`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsData

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (canon refSideC FormC)

@[expose] public section

/-- The tie of a side's symbolic flushes and baked terms, as a boolean. -/
def vtTieCheck (spec : List (List FormC)) (baked : List (List (List (List ℕ × ℕ)))) : Bool :=
  decide (spec.length = baked.length) &&
    (List.zip spec baked).all fun p ↦ decide (p.1.length = p.2.length) &&
      (List.zip p.1 p.2).all fun q ↦ decide (canon q.1.termsK = canon (vtTermsK q.2))

theorem vtTie00 : vtTieCheck (refSideC 0 .push) vtBTerms00 = true := by decide +kernel

theorem vtTie10 : vtTieCheck (refSideC 0 .pull) vtBTerms10 = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
