/-
  LeanVM.Guest.Memory.GuestCntWK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWK.Part00
public import LeanVM.Guest.Memory.GuestCntWK.Part01
public import LeanVM.Guest.Memory.GuestCntWK.Part02
public import LeanVM.Guest.Memory.GuestCntWK.Part03
public import LeanVM.Guest.Memory.GuestCntWK.Part04
public import LeanVM.Guest.Memory.GuestCntWK.Part05
public import LeanVM.Guest.Memory.GuestCntWK.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 1037, kukchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kukstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kukstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kukstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kukstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kukstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kukstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kukstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kukstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 206
  · exact kukstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kukstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kukstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kukstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kukstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kukstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 344
  · exact kukstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 350
  · exact kukstaticRange_344.get (by omega) (by omega)
  by_cases h16 : j < 357
  · exact kukstaticRange_350.get (by omega) (by omega)
  by_cases h17 : j < 387
  · exact kukstaticRange_357.get (by omega) (by omega)
  by_cases h18 : j < 417
  · exact kukstaticRange_387.get (by omega) (by omega)
  by_cases h19 : j < 447
  · exact kukstaticRange_417.get (by omega) (by omega)
  by_cases h20 : j < 477
  · exact kukstaticRange_447.get (by omega) (by omega)
  by_cases h21 : j < 507
  · exact kukstaticRange_477.get (by omega) (by omega)
  by_cases h22 : j < 537
  · exact kukstaticRange_507.get (by omega) (by omega)
  by_cases h23 : j < 567
  · exact kukstaticRange_537.get (by omega) (by omega)
  by_cases h24 : j < 597
  · exact kukstaticRange_567.get (by omega) (by omega)
  by_cases h25 : j < 627
  · exact kukstaticRange_597.get (by omega) (by omega)
  by_cases h26 : j < 657
  · exact kukstaticRange_627.get (by omega) (by omega)
  by_cases h27 : j < 687
  · exact kukstaticRange_657.get (by omega) (by omega)
  by_cases h28 : j < 717
  · exact kukstaticRange_687.get (by omega) (by omega)
  by_cases h29 : j < 747
  · exact kukstaticRange_717.get (by omega) (by omega)
  by_cases h30 : j < 777
  · exact kukstaticRange_747.get (by omega) (by omega)
  by_cases h31 : j < 807
  · exact kukstaticRange_777.get (by omega) (by omega)
  by_cases h32 : j < 837
  · exact kukstaticRange_807.get (by omega) (by omega)
  by_cases h33 : j < 867
  · exact kukstaticRange_837.get (by omega) (by omega)
  by_cases h34 : j < 897
  · exact kukstaticRange_867.get (by omega) (by omega)
  by_cases h35 : j < 927
  · exact kukstaticRange_897.get (by omega) (by omega)
  by_cases h36 : j < 957
  · exact kukstaticRange_927.get (by omega) (by omega)
  by_cases h37 : j < 987
  · exact kukstaticRange_957.get (by omega) (by omega)
  by_cases h38 : j < 1017
  · exact kukstaticRange_987.get (by omega) (by omega)
  exact kukstaticRange_1017.get (by omega) (by omega)

end
end LeanVM.Guest
