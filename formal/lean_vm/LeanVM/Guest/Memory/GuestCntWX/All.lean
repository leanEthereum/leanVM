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

theorem kuxchkIdx_all : ∀ j < 1055, kuxchkIdx j = true := by
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
  by_cases h13 : j < 336
  · exact kuxstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 342
  · exact kuxstaticRange_336.get (by omega) (by omega)
  by_cases h15 : j < 348
  · exact kuxstaticRange_342.get (by omega) (by omega)
  by_cases h16 : j < 354
  · exact kuxstaticRange_348.get (by omega) (by omega)
  by_cases h17 : j < 384
  · exact kuxstaticRange_354.get (by omega) (by omega)
  by_cases h18 : j < 414
  · exact kuxstaticRange_384.get (by omega) (by omega)
  by_cases h19 : j < 444
  · exact kuxstaticRange_414.get (by omega) (by omega)
  by_cases h20 : j < 474
  · exact kuxstaticRange_444.get (by omega) (by omega)
  by_cases h21 : j < 504
  · exact kuxstaticRange_474.get (by omega) (by omega)
  by_cases h22 : j < 534
  · exact kuxstaticRange_504.get (by omega) (by omega)
  by_cases h23 : j < 564
  · exact kuxstaticRange_534.get (by omega) (by omega)
  by_cases h24 : j < 594
  · exact kuxstaticRange_564.get (by omega) (by omega)
  by_cases h25 : j < 624
  · exact kuxstaticRange_594.get (by omega) (by omega)
  by_cases h26 : j < 654
  · exact kuxstaticRange_624.get (by omega) (by omega)
  by_cases h27 : j < 684
  · exact kuxstaticRange_654.get (by omega) (by omega)
  by_cases h28 : j < 714
  · exact kuxstaticRange_684.get (by omega) (by omega)
  by_cases h29 : j < 744
  · exact kuxstaticRange_714.get (by omega) (by omega)
  by_cases h30 : j < 774
  · exact kuxstaticRange_744.get (by omega) (by omega)
  by_cases h31 : j < 804
  · exact kuxstaticRange_774.get (by omega) (by omega)
  by_cases h32 : j < 834
  · exact kuxstaticRange_804.get (by omega) (by omega)
  by_cases h33 : j < 864
  · exact kuxstaticRange_834.get (by omega) (by omega)
  by_cases h34 : j < 894
  · exact kuxstaticRange_864.get (by omega) (by omega)
  by_cases h35 : j < 924
  · exact kuxstaticRange_894.get (by omega) (by omega)
  by_cases h36 : j < 954
  · exact kuxstaticRange_924.get (by omega) (by omega)
  by_cases h37 : j < 984
  · exact kuxstaticRange_954.get (by omega) (by omega)
  by_cases h38 : j < 1014
  · exact kuxstaticRange_984.get (by omega) (by omega)
  by_cases h39 : j < 1044
  · exact kuxstaticRange_1014.get (by omega) (by omega)
  exact kuxstaticRange_1044.get (by omega) (by omega)

end
end LeanVM.Guest
