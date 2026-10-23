/-
  LeanVM.Guest.B2C.Temps1617

  The temporaries of core functions `16` and `17` by index, from their freshness certificates.
-/

module

public import LeanVM.Guest.Memory.GuestFresh.Fresh16
public import LeanVM.Guest.Memory.GuestFresh.Fresh17

/-!
# The temporaries of the two large functions

Their freshness certificates check their bodies by ranges of statements (`RangeFresh`), each
range's temporaries listed; chained, they give the temporaries' indices, `temps16` and
`temps17`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
/-- Core function `16`'s temporaries, by index. -/
theorem tmps16 : (Stmt.tmpsList Data.core16.body).map V.idx = temps16 := by
  have h730 : RangeFresh (Data.core16.body.drop 730) [] temps16 :=
    rangeFresh_end (by decide +kernel) temps16
  have h514 := rangeFresh_drop fresh16_514 h730
  have h490 := rangeFresh_drop fresh16_490 h514
  have h466 := rangeFresh_drop fresh16_466 h490
  have h230 := rangeFresh_drop fresh16_230 h466
  have h206 := rangeFresh_drop fresh16_206 h230
  have h182 := rangeFresh_drop fresh16_182 h206
  have h0 := rangeFresh_drop fresh16_0 h182
  exact h0.1.trans (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Core function `17`'s temporaries, by index. -/
theorem tmps17 : (Stmt.tmpsList Data.core17.body).map V.idx = temps17 := by
  have h1127 : RangeFresh (Data.core17.body.drop 1127) [] temps17 :=
    rangeFresh_end (by decide +kernel) temps17
  have h809 := rangeFresh_drop fresh17_809 h1127
  have h793 := rangeFresh_drop fresh17_793 h809
  have h777 := rangeFresh_drop fresh17_777 h793
  have h761 := rangeFresh_drop fresh17_761 h777
  have h745 := rangeFresh_drop fresh17_745 h761
  have h0 := rangeFresh_drop fresh17_0 h745
  exact h0.1.trans (by decide +kernel)

end
end LeanVM.Guest.B2C
