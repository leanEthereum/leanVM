/-
  LeanVM.Guest.B1.Opening.QueriesAll

  The deployed specializations of `opening_queries`, their bodies the templates.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody0
public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.B1.Opening.QueriesBody2
public import LeanVM.Guest.B1.Opening.QueriesBody3

/-!
# `opening_queries`, every specialization (TRIAGE G #40)

The 42 deployed shapes' bodies checked against the templates (`QueriesBody0-3`), for `Whir.Sound`;
their soundness is `QueriesAllW`, their placed completeness `QueriesPlacedAll`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

end
end LeanVM.Guest.B1
