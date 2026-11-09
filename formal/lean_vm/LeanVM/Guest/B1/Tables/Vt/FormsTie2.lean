/-
  LeanVM.Guest.B1.Tables.Vt.FormsTie2

  Table 2's push and pull flushes are the guest's baked coordinate terms, by kernel evaluation
  of their canonical forms over `K`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsTie0

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (canon refSideC FormC)

@[expose] public section

theorem vtTie02 : vtTieCheck (refSideC 2 .push) vtBTerms02 = true := by decide +kernel

theorem vtTie12 : vtTieCheck (refSideC 2 .pull) vtBTerms12 = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
