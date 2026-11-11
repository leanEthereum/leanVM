/-
  LeanVM.Guest.Memory.GuestCntWS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWS.Part00
public import LeanVM.Guest.Memory.GuestCntWS.Part01
public import LeanVM.Guest.Memory.GuestCntWS.Part02
public import LeanVM.Guest.Memory.GuestCntWS.Part03
public import LeanVM.Guest.Memory.GuestCntWS.Part04
public import LeanVM.Guest.Memory.GuestCntWS.Part05
public import LeanVM.Guest.Memory.GuestCntWS.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuschkIdx_all : ∀ j < 1037, kuschkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kusstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kusstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kusstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kusstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kusstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kusstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kusstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kusstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kusstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kusstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kusstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kusstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kusstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kusstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 344
  · exact kusstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 350
  · exact kusstaticRange_344.get (by omega) (by omega)
  by_cases h16 : j < 357
  · exact kusstaticRange_350.get (by omega) (by omega)
  by_cases h17 : j < 387
  · exact kusstaticRange_357.get (by omega) (by omega)
  by_cases h18 : j < 417
  · exact kusstaticRange_387.get (by omega) (by omega)
  by_cases h19 : j < 447
  · exact kusstaticRange_417.get (by omega) (by omega)
  by_cases h20 : j < 477
  · exact kusstaticRange_447.get (by omega) (by omega)
  by_cases h21 : j < 507
  · exact kusstaticRange_477.get (by omega) (by omega)
  by_cases h22 : j < 537
  · exact kusstaticRange_507.get (by omega) (by omega)
  by_cases h23 : j < 567
  · exact kusstaticRange_537.get (by omega) (by omega)
  by_cases h24 : j < 597
  · exact kusstaticRange_567.get (by omega) (by omega)
  by_cases h25 : j < 627
  · exact kusstaticRange_597.get (by omega) (by omega)
  by_cases h26 : j < 657
  · exact kusstaticRange_627.get (by omega) (by omega)
  by_cases h27 : j < 687
  · exact kusstaticRange_657.get (by omega) (by omega)
  by_cases h28 : j < 717
  · exact kusstaticRange_687.get (by omega) (by omega)
  by_cases h29 : j < 747
  · exact kusstaticRange_717.get (by omega) (by omega)
  by_cases h30 : j < 777
  · exact kusstaticRange_747.get (by omega) (by omega)
  by_cases h31 : j < 807
  · exact kusstaticRange_777.get (by omega) (by omega)
  by_cases h32 : j < 837
  · exact kusstaticRange_807.get (by omega) (by omega)
  by_cases h33 : j < 867
  · exact kusstaticRange_837.get (by omega) (by omega)
  by_cases h34 : j < 897
  · exact kusstaticRange_867.get (by omega) (by omega)
  by_cases h35 : j < 927
  · exact kusstaticRange_897.get (by omega) (by omega)
  by_cases h36 : j < 957
  · exact kusstaticRange_927.get (by omega) (by omega)
  by_cases h37 : j < 987
  · exact kusstaticRange_957.get (by omega) (by omega)
  by_cases h38 : j < 1017
  · exact kusstaticRange_987.get (by omega) (by omega)
  exact kusstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
