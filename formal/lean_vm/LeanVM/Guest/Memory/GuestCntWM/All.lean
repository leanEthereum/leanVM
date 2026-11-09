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

theorem kumchkIdx_all : ∀ j < 1055, kumchkIdx j = true := by
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
  by_cases h13 : j < 336
  · exact kumstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 342
  · exact kumstaticRange_336.get (by omega) (by omega)
  by_cases h15 : j < 348
  · exact kumstaticRange_342.get (by omega) (by omega)
  by_cases h16 : j < 354
  · exact kumstaticRange_348.get (by omega) (by omega)
  by_cases h17 : j < 384
  · exact kumstaticRange_354.get (by omega) (by omega)
  by_cases h18 : j < 414
  · exact kumstaticRange_384.get (by omega) (by omega)
  by_cases h19 : j < 444
  · exact kumstaticRange_414.get (by omega) (by omega)
  by_cases h20 : j < 474
  · exact kumstaticRange_444.get (by omega) (by omega)
  by_cases h21 : j < 504
  · exact kumstaticRange_474.get (by omega) (by omega)
  by_cases h22 : j < 534
  · exact kumstaticRange_504.get (by omega) (by omega)
  by_cases h23 : j < 564
  · exact kumstaticRange_534.get (by omega) (by omega)
  by_cases h24 : j < 594
  · exact kumstaticRange_564.get (by omega) (by omega)
  by_cases h25 : j < 624
  · exact kumstaticRange_594.get (by omega) (by omega)
  by_cases h26 : j < 654
  · exact kumstaticRange_624.get (by omega) (by omega)
  by_cases h27 : j < 684
  · exact kumstaticRange_654.get (by omega) (by omega)
  by_cases h28 : j < 714
  · exact kumstaticRange_684.get (by omega) (by omega)
  by_cases h29 : j < 744
  · exact kumstaticRange_714.get (by omega) (by omega)
  by_cases h30 : j < 774
  · exact kumstaticRange_744.get (by omega) (by omega)
  by_cases h31 : j < 804
  · exact kumstaticRange_774.get (by omega) (by omega)
  by_cases h32 : j < 834
  · exact kumstaticRange_804.get (by omega) (by omega)
  by_cases h33 : j < 864
  · exact kumstaticRange_834.get (by omega) (by omega)
  by_cases h34 : j < 894
  · exact kumstaticRange_864.get (by omega) (by omega)
  by_cases h35 : j < 924
  · exact kumstaticRange_894.get (by omega) (by omega)
  by_cases h36 : j < 954
  · exact kumstaticRange_924.get (by omega) (by omega)
  by_cases h37 : j < 984
  · exact kumstaticRange_954.get (by omega) (by omega)
  by_cases h38 : j < 1014
  · exact kumstaticRange_984.get (by omega) (by omega)
  by_cases h39 : j < 1044
  · exact kumstaticRange_1014.get (by omega) (by omega)
  exact kumstaticRange_1044.get (by omega) (by omega)

end
end LeanVM.Guest
