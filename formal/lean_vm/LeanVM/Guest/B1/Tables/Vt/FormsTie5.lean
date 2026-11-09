/-
  LeanVM.Guest.B1.Tables.Vt.FormsTie5

  Table 5's push and pull flushes are the guest's baked coordinate terms, by kernel evaluation
  of their canonical forms over `K`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsTie0

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (canon refSideC FormC)

@[expose] public section

theorem vtTie05 : vtTieCheck (refSideC 5 .push) vtBTerms05 = true := by decide +kernel

theorem vtTie15 : vtTieCheck (refSideC 5 .pull) vtBTerms15 = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
