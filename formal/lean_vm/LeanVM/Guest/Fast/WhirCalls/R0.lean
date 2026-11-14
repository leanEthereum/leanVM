/-
  LeanVM.Guest.Fast.WhirCalls.R0

  `open_stacked`'s dispatch tables at rate index 0, checked (`Fast/WhirCalls.lean`).
-/

module

public import LeanVM.Guest.Fast.WhirCalls

namespace LeanVM.Guest.Fast

@[expose] public section

theorem callsOK_0 : CallsOK 0 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_1 : CallsOK 1 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_2 : CallsOK 2 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_3 : CallsOK 3 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_4 : CallsOK 4 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_5 : CallsOK 5 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_6 : CallsOK 6 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_7 : CallsOK 7 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_8 : CallsOK 8 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_9 : CallsOK 9 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

theorem callsOK_10 : CallsOK 10 := CallsOKN.ok (by unfold CallsOKN; decide +kernel)

end
end LeanVM.Guest.Fast
