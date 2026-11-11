/-
  LeanVM.Guest.Memory.GuestCntWD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWD.Part00
public import LeanVM.Guest.Memory.GuestCntWD.Part01
public import LeanVM.Guest.Memory.GuestCntWD.Part02
public import LeanVM.Guest.Memory.GuestCntWD.Part03
public import LeanVM.Guest.Memory.GuestCntWD.Part04
public import LeanVM.Guest.Memory.GuestCntWD.Part05
public import LeanVM.Guest.Memory.GuestCntWD.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kudchkIdx_all : ∀ j < 1037, kudchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kudstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kudstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kudstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kudstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kudstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kudstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kudstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kudstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kudstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kudstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kudstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kudstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kudstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kudstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 344
  · exact kudstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 350
  · exact kudstaticRange_344.get (by omega) (by omega)
  by_cases h16 : j < 357
  · exact kudstaticRange_350.get (by omega) (by omega)
  by_cases h17 : j < 387
  · exact kudstaticRange_357.get (by omega) (by omega)
  by_cases h18 : j < 417
  · exact kudstaticRange_387.get (by omega) (by omega)
  by_cases h19 : j < 447
  · exact kudstaticRange_417.get (by omega) (by omega)
  by_cases h20 : j < 477
  · exact kudstaticRange_447.get (by omega) (by omega)
  by_cases h21 : j < 507
  · exact kudstaticRange_477.get (by omega) (by omega)
  by_cases h22 : j < 537
  · exact kudstaticRange_507.get (by omega) (by omega)
  by_cases h23 : j < 567
  · exact kudstaticRange_537.get (by omega) (by omega)
  by_cases h24 : j < 597
  · exact kudstaticRange_567.get (by omega) (by omega)
  by_cases h25 : j < 627
  · exact kudstaticRange_597.get (by omega) (by omega)
  by_cases h26 : j < 657
  · exact kudstaticRange_627.get (by omega) (by omega)
  by_cases h27 : j < 687
  · exact kudstaticRange_657.get (by omega) (by omega)
  by_cases h28 : j < 717
  · exact kudstaticRange_687.get (by omega) (by omega)
  by_cases h29 : j < 747
  · exact kudstaticRange_717.get (by omega) (by omega)
  by_cases h30 : j < 777
  · exact kudstaticRange_747.get (by omega) (by omega)
  by_cases h31 : j < 807
  · exact kudstaticRange_777.get (by omega) (by omega)
  by_cases h32 : j < 837
  · exact kudstaticRange_807.get (by omega) (by omega)
  by_cases h33 : j < 867
  · exact kudstaticRange_837.get (by omega) (by omega)
  by_cases h34 : j < 897
  · exact kudstaticRange_867.get (by omega) (by omega)
  by_cases h35 : j < 927
  · exact kudstaticRange_897.get (by omega) (by omega)
  by_cases h36 : j < 957
  · exact kudstaticRange_927.get (by omega) (by omega)
  by_cases h37 : j < 987
  · exact kudstaticRange_957.get (by omega) (by omega)
  by_cases h38 : j < 1017
  · exact kudstaticRange_987.get (by omega) (by omega)
  exact kudstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
