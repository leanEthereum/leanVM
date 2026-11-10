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

theorem kujchkIdx_all : ∀ j < 1055, kujchkIdx j = true := by
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
  by_cases h13 : j < 336
  · exact kujstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 342
  · exact kujstaticRange_336.get (by omega) (by omega)
  by_cases h15 : j < 348
  · exact kujstaticRange_342.get (by omega) (by omega)
  by_cases h16 : j < 354
  · exact kujstaticRange_348.get (by omega) (by omega)
  by_cases h17 : j < 384
  · exact kujstaticRange_354.get (by omega) (by omega)
  by_cases h18 : j < 414
  · exact kujstaticRange_384.get (by omega) (by omega)
  by_cases h19 : j < 444
  · exact kujstaticRange_414.get (by omega) (by omega)
  by_cases h20 : j < 474
  · exact kujstaticRange_444.get (by omega) (by omega)
  by_cases h21 : j < 504
  · exact kujstaticRange_474.get (by omega) (by omega)
  by_cases h22 : j < 534
  · exact kujstaticRange_504.get (by omega) (by omega)
  by_cases h23 : j < 564
  · exact kujstaticRange_534.get (by omega) (by omega)
  by_cases h24 : j < 594
  · exact kujstaticRange_564.get (by omega) (by omega)
  by_cases h25 : j < 624
  · exact kujstaticRange_594.get (by omega) (by omega)
  by_cases h26 : j < 654
  · exact kujstaticRange_624.get (by omega) (by omega)
  by_cases h27 : j < 684
  · exact kujstaticRange_654.get (by omega) (by omega)
  by_cases h28 : j < 714
  · exact kujstaticRange_684.get (by omega) (by omega)
  by_cases h29 : j < 744
  · exact kujstaticRange_714.get (by omega) (by omega)
  by_cases h30 : j < 774
  · exact kujstaticRange_744.get (by omega) (by omega)
  by_cases h31 : j < 804
  · exact kujstaticRange_774.get (by omega) (by omega)
  by_cases h32 : j < 834
  · exact kujstaticRange_804.get (by omega) (by omega)
  by_cases h33 : j < 864
  · exact kujstaticRange_834.get (by omega) (by omega)
  by_cases h34 : j < 894
  · exact kujstaticRange_864.get (by omega) (by omega)
  by_cases h35 : j < 924
  · exact kujstaticRange_894.get (by omega) (by omega)
  by_cases h36 : j < 954
  · exact kujstaticRange_924.get (by omega) (by omega)
  by_cases h37 : j < 984
  · exact kujstaticRange_954.get (by omega) (by omega)
  by_cases h38 : j < 1014
  · exact kujstaticRange_984.get (by omega) (by omega)
  by_cases h39 : j < 1044
  · exact kujstaticRange_1014.get (by omega) (by omega)
  exact kujstaticRange_1044.get (by omega) (by omega)

end
end LeanVM.Guest
