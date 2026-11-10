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

theorem kukchkIdx_all : ∀ j < 1055, kukchkIdx j = true := by
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
  by_cases h13 : j < 336
  · exact kukstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 342
  · exact kukstaticRange_336.get (by omega) (by omega)
  by_cases h15 : j < 348
  · exact kukstaticRange_342.get (by omega) (by omega)
  by_cases h16 : j < 354
  · exact kukstaticRange_348.get (by omega) (by omega)
  by_cases h17 : j < 384
  · exact kukstaticRange_354.get (by omega) (by omega)
  by_cases h18 : j < 414
  · exact kukstaticRange_384.get (by omega) (by omega)
  by_cases h19 : j < 444
  · exact kukstaticRange_414.get (by omega) (by omega)
  by_cases h20 : j < 474
  · exact kukstaticRange_444.get (by omega) (by omega)
  by_cases h21 : j < 504
  · exact kukstaticRange_474.get (by omega) (by omega)
  by_cases h22 : j < 534
  · exact kukstaticRange_504.get (by omega) (by omega)
  by_cases h23 : j < 564
  · exact kukstaticRange_534.get (by omega) (by omega)
  by_cases h24 : j < 594
  · exact kukstaticRange_564.get (by omega) (by omega)
  by_cases h25 : j < 624
  · exact kukstaticRange_594.get (by omega) (by omega)
  by_cases h26 : j < 654
  · exact kukstaticRange_624.get (by omega) (by omega)
  by_cases h27 : j < 684
  · exact kukstaticRange_654.get (by omega) (by omega)
  by_cases h28 : j < 714
  · exact kukstaticRange_684.get (by omega) (by omega)
  by_cases h29 : j < 744
  · exact kukstaticRange_714.get (by omega) (by omega)
  by_cases h30 : j < 774
  · exact kukstaticRange_744.get (by omega) (by omega)
  by_cases h31 : j < 804
  · exact kukstaticRange_774.get (by omega) (by omega)
  by_cases h32 : j < 834
  · exact kukstaticRange_804.get (by omega) (by omega)
  by_cases h33 : j < 864
  · exact kukstaticRange_834.get (by omega) (by omega)
  by_cases h34 : j < 894
  · exact kukstaticRange_864.get (by omega) (by omega)
  by_cases h35 : j < 924
  · exact kukstaticRange_894.get (by omega) (by omega)
  by_cases h36 : j < 954
  · exact kukstaticRange_924.get (by omega) (by omega)
  by_cases h37 : j < 984
  · exact kukstaticRange_954.get (by omega) (by omega)
  by_cases h38 : j < 1014
  · exact kukstaticRange_984.get (by omega) (by omega)
  by_cases h39 : j < 1044
  · exact kukstaticRange_1014.get (by omega) (by omega)
  exact kukstaticRange_1044.get (by omega) (by omega)

end
end LeanVM.Guest
