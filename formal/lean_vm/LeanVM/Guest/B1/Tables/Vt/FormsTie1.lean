/-
  LeanVM.Guest.B1.Tables.Vt.FormsTie1

  Table 1's push and pull flushes are the guest's baked coordinate terms, by kernel evaluation
  of their canonical forms over `K`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsTie0

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (canon refSideC FormC)

@[expose] public section

theorem vtTie01 : vtTieCheck (refSideC 1 .push) vtBTerms01 = true := by decide +kernel

theorem vtTie11 : vtTieCheck (refSideC 1 .pull) vtBTerms11 = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
