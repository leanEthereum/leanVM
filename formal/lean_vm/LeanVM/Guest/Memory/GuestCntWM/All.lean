/-
  LeanVM.Guest.Memory.GuestCntWM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWM.Part00
public import LeanVM.Guest.Memory.GuestCntWM.Part01
public import LeanVM.Guest.Memory.GuestCntWM.Part02
public import LeanVM.Guest.Memory.GuestCntWM.Part03
public import LeanVM.Guest.Memory.GuestCntWM.Part04
public import LeanVM.Guest.Memory.GuestCntWM.Part05
public import LeanVM.Guest.Memory.GuestCntWM.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kumchkIdx_all : ∀ j < 1037, kumchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kumstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kumstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kumstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kumstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kumstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kumstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kumstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kumstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kumstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kumstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kumstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kumstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kumstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kumstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 344
  · exact kumstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 350
  · exact kumstaticRange_344.get (by omega) (by omega)
  by_cases h16 : j < 357
  · exact kumstaticRange_350.get (by omega) (by omega)
  by_cases h17 : j < 387
  · exact kumstaticRange_357.get (by omega) (by omega)
  by_cases h18 : j < 417
  · exact kumstaticRange_387.get (by omega) (by omega)
  by_cases h19 : j < 447
  · exact kumstaticRange_417.get (by omega) (by omega)
  by_cases h20 : j < 477
  · exact kumstaticRange_447.get (by omega) (by omega)
  by_cases h21 : j < 507
  · exact kumstaticRange_477.get (by omega) (by omega)
  by_cases h22 : j < 537
  · exact kumstaticRange_507.get (by omega) (by omega)
  by_cases h23 : j < 567
  · exact kumstaticRange_537.get (by omega) (by omega)
  by_cases h24 : j < 597
  · exact kumstaticRange_567.get (by omega) (by omega)
  by_cases h25 : j < 627
  · exact kumstaticRange_597.get (by omega) (by omega)
  by_cases h26 : j < 657
  · exact kumstaticRange_627.get (by omega) (by omega)
  by_cases h27 : j < 687
  · exact kumstaticRange_657.get (by omega) (by omega)
  by_cases h28 : j < 717
  · exact kumstaticRange_687.get (by omega) (by omega)
  by_cases h29 : j < 747
  · exact kumstaticRange_717.get (by omega) (by omega)
  by_cases h30 : j < 777
  · exact kumstaticRange_747.get (by omega) (by omega)
  by_cases h31 : j < 807
  · exact kumstaticRange_777.get (by omega) (by omega)
  by_cases h32 : j < 837
  · exact kumstaticRange_807.get (by omega) (by omega)
  by_cases h33 : j < 867
  · exact kumstaticRange_837.get (by omega) (by omega)
  by_cases h34 : j < 897
  · exact kumstaticRange_867.get (by omega) (by omega)
  by_cases h35 : j < 927
  · exact kumstaticRange_897.get (by omega) (by omega)
  by_cases h36 : j < 957
  · exact kumstaticRange_927.get (by omega) (by omega)
  by_cases h37 : j < 987
  · exact kumstaticRange_957.get (by omega) (by omega)
  by_cases h38 : j < 1017
  · exact kumstaticRange_987.get (by omega) (by omega)
  exact kumstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
