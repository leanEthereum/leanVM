/-
  LeanVM.Guest.Memory.GuestCntWJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWJ.Part00
public import LeanVM.Guest.Memory.GuestCntWJ.Part01
public import LeanVM.Guest.Memory.GuestCntWJ.Part02
public import LeanVM.Guest.Memory.GuestCntWJ.Part03
public import LeanVM.Guest.Memory.GuestCntWJ.Part04
public import LeanVM.Guest.Memory.GuestCntWJ.Part05
public import LeanVM.Guest.Memory.GuestCntWJ.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kujchkIdx_all : ∀ j < 1037, kujchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kujstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kujstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kujstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kujstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kujstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kujstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kujstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kujstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kujstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kujstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kujstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kujstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kujstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kujstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 344
  · exact kujstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 350
  · exact kujstaticRange_344.get (by omega) (by omega)
  by_cases h16 : j < 357
  · exact kujstaticRange_350.get (by omega) (by omega)
  by_cases h17 : j < 387
  · exact kujstaticRange_357.get (by omega) (by omega)
  by_cases h18 : j < 417
  · exact kujstaticRange_387.get (by omega) (by omega)
  by_cases h19 : j < 447
  · exact kujstaticRange_417.get (by omega) (by omega)
  by_cases h20 : j < 477
  · exact kujstaticRange_447.get (by omega) (by omega)
  by_cases h21 : j < 507
  · exact kujstaticRange_477.get (by omega) (by omega)
  by_cases h22 : j < 537
  · exact kujstaticRange_507.get (by omega) (by omega)
  by_cases h23 : j < 567
  · exact kujstaticRange_537.get (by omega) (by omega)
  by_cases h24 : j < 597
  · exact kujstaticRange_567.get (by omega) (by omega)
  by_cases h25 : j < 627
  · exact kujstaticRange_597.get (by omega) (by omega)
  by_cases h26 : j < 657
  · exact kujstaticRange_627.get (by omega) (by omega)
  by_cases h27 : j < 687
  · exact kujstaticRange_657.get (by omega) (by omega)
  by_cases h28 : j < 717
  · exact kujstaticRange_687.get (by omega) (by omega)
  by_cases h29 : j < 747
  · exact kujstaticRange_717.get (by omega) (by omega)
  by_cases h30 : j < 777
  · exact kujstaticRange_747.get (by omega) (by omega)
  by_cases h31 : j < 807
  · exact kujstaticRange_777.get (by omega) (by omega)
  by_cases h32 : j < 837
  · exact kujstaticRange_807.get (by omega) (by omega)
  by_cases h33 : j < 867
  · exact kujstaticRange_837.get (by omega) (by omega)
  by_cases h34 : j < 897
  · exact kujstaticRange_867.get (by omega) (by omega)
  by_cases h35 : j < 927
  · exact kujstaticRange_897.get (by omega) (by omega)
  by_cases h36 : j < 957
  · exact kujstaticRange_927.get (by omega) (by omega)
  by_cases h37 : j < 987
  · exact kujstaticRange_957.get (by omega) (by omega)
  by_cases h38 : j < 1017
  · exact kujstaticRange_987.get (by omega) (by omega)
  exact kujstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
