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

theorem kudchkIdx_all : ∀ j < 1055, kudchkIdx j = true := by
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
  by_cases h13 : j < 336
  · exact kudstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 342
  · exact kudstaticRange_336.get (by omega) (by omega)
  by_cases h15 : j < 348
  · exact kudstaticRange_342.get (by omega) (by omega)
  by_cases h16 : j < 354
  · exact kudstaticRange_348.get (by omega) (by omega)
  by_cases h17 : j < 384
  · exact kudstaticRange_354.get (by omega) (by omega)
  by_cases h18 : j < 414
  · exact kudstaticRange_384.get (by omega) (by omega)
  by_cases h19 : j < 444
  · exact kudstaticRange_414.get (by omega) (by omega)
  by_cases h20 : j < 474
  · exact kudstaticRange_444.get (by omega) (by omega)
  by_cases h21 : j < 504
  · exact kudstaticRange_474.get (by omega) (by omega)
  by_cases h22 : j < 534
  · exact kudstaticRange_504.get (by omega) (by omega)
  by_cases h23 : j < 564
  · exact kudstaticRange_534.get (by omega) (by omega)
  by_cases h24 : j < 594
  · exact kudstaticRange_564.get (by omega) (by omega)
  by_cases h25 : j < 624
  · exact kudstaticRange_594.get (by omega) (by omega)
  by_cases h26 : j < 654
  · exact kudstaticRange_624.get (by omega) (by omega)
  by_cases h27 : j < 684
  · exact kudstaticRange_654.get (by omega) (by omega)
  by_cases h28 : j < 714
  · exact kudstaticRange_684.get (by omega) (by omega)
  by_cases h29 : j < 744
  · exact kudstaticRange_714.get (by omega) (by omega)
  by_cases h30 : j < 774
  · exact kudstaticRange_744.get (by omega) (by omega)
  by_cases h31 : j < 804
  · exact kudstaticRange_774.get (by omega) (by omega)
  by_cases h32 : j < 834
  · exact kudstaticRange_804.get (by omega) (by omega)
  by_cases h33 : j < 864
  · exact kudstaticRange_834.get (by omega) (by omega)
  by_cases h34 : j < 894
  · exact kudstaticRange_864.get (by omega) (by omega)
  by_cases h35 : j < 924
  · exact kudstaticRange_894.get (by omega) (by omega)
  by_cases h36 : j < 954
  · exact kudstaticRange_924.get (by omega) (by omega)
  by_cases h37 : j < 984
  · exact kudstaticRange_954.get (by omega) (by omega)
  by_cases h38 : j < 1014
  · exact kudstaticRange_984.get (by omega) (by omega)
  by_cases h39 : j < 1044
  · exact kudstaticRange_1014.get (by omega) (by omega)
  exact kudstaticRange_1044.get (by omega) (by omega)

end
end LeanVM.Guest
