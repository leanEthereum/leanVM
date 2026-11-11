/-
  LeanVM.Guest.Memory.GuestCntWX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWX.Part00
public import LeanVM.Guest.Memory.GuestCntWX.Part01
public import LeanVM.Guest.Memory.GuestCntWX.Part02
public import LeanVM.Guest.Memory.GuestCntWX.Part03
public import LeanVM.Guest.Memory.GuestCntWX.Part04
public import LeanVM.Guest.Memory.GuestCntWX.Part05
public import LeanVM.Guest.Memory.GuestCntWX.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuxchkIdx_all : ∀ j < 1037, kuxchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kuxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kuxstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kuxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kuxstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kuxstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kuxstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kuxstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kuxstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kuxstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kuxstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kuxstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kuxstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kuxstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kuxstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 344
  · exact kuxstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 350
  · exact kuxstaticRange_344.get (by omega) (by omega)
  by_cases h16 : j < 357
  · exact kuxstaticRange_350.get (by omega) (by omega)
  by_cases h17 : j < 387
  · exact kuxstaticRange_357.get (by omega) (by omega)
  by_cases h18 : j < 417
  · exact kuxstaticRange_387.get (by omega) (by omega)
  by_cases h19 : j < 447
  · exact kuxstaticRange_417.get (by omega) (by omega)
  by_cases h20 : j < 477
  · exact kuxstaticRange_447.get (by omega) (by omega)
  by_cases h21 : j < 507
  · exact kuxstaticRange_477.get (by omega) (by omega)
  by_cases h22 : j < 537
  · exact kuxstaticRange_507.get (by omega) (by omega)
  by_cases h23 : j < 567
  · exact kuxstaticRange_537.get (by omega) (by omega)
  by_cases h24 : j < 597
  · exact kuxstaticRange_567.get (by omega) (by omega)
  by_cases h25 : j < 627
  · exact kuxstaticRange_597.get (by omega) (by omega)
  by_cases h26 : j < 657
  · exact kuxstaticRange_627.get (by omega) (by omega)
  by_cases h27 : j < 687
  · exact kuxstaticRange_657.get (by omega) (by omega)
  by_cases h28 : j < 717
  · exact kuxstaticRange_687.get (by omega) (by omega)
  by_cases h29 : j < 747
  · exact kuxstaticRange_717.get (by omega) (by omega)
  by_cases h30 : j < 777
  · exact kuxstaticRange_747.get (by omega) (by omega)
  by_cases h31 : j < 807
  · exact kuxstaticRange_777.get (by omega) (by omega)
  by_cases h32 : j < 837
  · exact kuxstaticRange_807.get (by omega) (by omega)
  by_cases h33 : j < 867
  · exact kuxstaticRange_837.get (by omega) (by omega)
  by_cases h34 : j < 897
  · exact kuxstaticRange_867.get (by omega) (by omega)
  by_cases h35 : j < 927
  · exact kuxstaticRange_897.get (by omega) (by omega)
  by_cases h36 : j < 957
  · exact kuxstaticRange_927.get (by omega) (by omega)
  by_cases h37 : j < 987
  · exact kuxstaticRange_957.get (by omega) (by omega)
  by_cases h38 : j < 1017
  · exact kuxstaticRange_987.get (by omega) (by omega)
  exact kuxstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
