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

theorem kuschkIdx_all : ∀ j < 1055, kuschkIdx j = true := by
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
  by_cases h13 : j < 336
  · exact kusstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 342
  · exact kusstaticRange_336.get (by omega) (by omega)
  by_cases h15 : j < 348
  · exact kusstaticRange_342.get (by omega) (by omega)
  by_cases h16 : j < 354
  · exact kusstaticRange_348.get (by omega) (by omega)
  by_cases h17 : j < 384
  · exact kusstaticRange_354.get (by omega) (by omega)
  by_cases h18 : j < 414
  · exact kusstaticRange_384.get (by omega) (by omega)
  by_cases h19 : j < 444
  · exact kusstaticRange_414.get (by omega) (by omega)
  by_cases h20 : j < 474
  · exact kusstaticRange_444.get (by omega) (by omega)
  by_cases h21 : j < 504
  · exact kusstaticRange_474.get (by omega) (by omega)
  by_cases h22 : j < 534
  · exact kusstaticRange_504.get (by omega) (by omega)
  by_cases h23 : j < 564
  · exact kusstaticRange_534.get (by omega) (by omega)
  by_cases h24 : j < 594
  · exact kusstaticRange_564.get (by omega) (by omega)
  by_cases h25 : j < 624
  · exact kusstaticRange_594.get (by omega) (by omega)
  by_cases h26 : j < 654
  · exact kusstaticRange_624.get (by omega) (by omega)
  by_cases h27 : j < 684
  · exact kusstaticRange_654.get (by omega) (by omega)
  by_cases h28 : j < 714
  · exact kusstaticRange_684.get (by omega) (by omega)
  by_cases h29 : j < 744
  · exact kusstaticRange_714.get (by omega) (by omega)
  by_cases h30 : j < 774
  · exact kusstaticRange_744.get (by omega) (by omega)
  by_cases h31 : j < 804
  · exact kusstaticRange_774.get (by omega) (by omega)
  by_cases h32 : j < 834
  · exact kusstaticRange_804.get (by omega) (by omega)
  by_cases h33 : j < 864
  · exact kusstaticRange_834.get (by omega) (by omega)
  by_cases h34 : j < 894
  · exact kusstaticRange_864.get (by omega) (by omega)
  by_cases h35 : j < 924
  · exact kusstaticRange_894.get (by omega) (by omega)
  by_cases h36 : j < 954
  · exact kusstaticRange_924.get (by omega) (by omega)
  by_cases h37 : j < 984
  · exact kusstaticRange_954.get (by omega) (by omega)
  by_cases h38 : j < 1014
  · exact kusstaticRange_984.get (by omega) (by omega)
  by_cases h39 : j < 1044
  · exact kusstaticRange_1014.get (by omega) (by omega)
  exact kusstaticRange_1044.get (by omega) (by omega)

end
end LeanVM.Guest
