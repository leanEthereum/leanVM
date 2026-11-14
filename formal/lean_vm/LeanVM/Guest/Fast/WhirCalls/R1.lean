/-
  LeanVM.Guest.Fast.WhirCalls.R1

  `open_stacked`'s dispatch tables at rate index 1, checked (`Fast/WhirCalls.lean`).
-/

module

public import LeanVM.Guest.Fast.WhirCalls

namespace LeanVM.Guest.Fast

@[expose] public section

theorem callsOK_11 : CallsOK 11 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_12 : CallsOK 12 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_13 : CallsOK 13 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_14 : CallsOK 14 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_15 : CallsOK 15 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_16 : CallsOK 16 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_17 : CallsOK 17 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_18 : CallsOK 18 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_19 : CallsOK 19 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_20 : CallsOK 20 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_21 : CallsOK 21 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

end
end LeanVM.Guest.Fast
