/-
  LeanVM.Guest.B1.Tables.Vt.FormsTie4

  Table 4's push and pull flushes are the guest's baked coordinate terms, by kernel evaluation
  of their canonical forms over `K`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsTie0

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (canon refSideC FormC)

@[expose] public section

theorem vtTie04 : vtTieCheck (refSideC 4 .push) vtBTerms04 = true := by decide +kernel

theorem vtTie14 : vtTieCheck (refSideC 4 .pull) vtBTerms14 = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
