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
public import LeanVM.Guest.Memory.GuestCntWD.Part07
public import LeanVM.Guest.Memory.GuestCntWD.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kudchkIdx_all : ∀ j < 1601, kudchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kudstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kudstaticRange_128.get (by omega) (by omega)
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
  by_cases h13 : j < 338
  · exact kudstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 341
  · exact kudstaticRange_338.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kudstaticRange_341.get (by omega) (by omega)
  by_cases h16 : j < 374
  · exact kudstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 404
  · exact kudstaticRange_374.get (by omega) (by omega)
  by_cases h18 : j < 434
  · exact kudstaticRange_404.get (by omega) (by omega)
  by_cases h19 : j < 464
  · exact kudstaticRange_434.get (by omega) (by omega)
  by_cases h20 : j < 494
  · exact kudstaticRange_464.get (by omega) (by omega)
  by_cases h21 : j < 524
  · exact kudstaticRange_494.get (by omega) (by omega)
  by_cases h22 : j < 554
  · exact kudstaticRange_524.get (by omega) (by omega)
  by_cases h23 : j < 584
  · exact kudstaticRange_554.get (by omega) (by omega)
  by_cases h24 : j < 614
  · exact kudstaticRange_584.get (by omega) (by omega)
  by_cases h25 : j < 644
  · exact kudstaticRange_614.get (by omega) (by omega)
  by_cases h26 : j < 674
  · exact kudstaticRange_644.get (by omega) (by omega)
  by_cases h27 : j < 704
  · exact kudstaticRange_674.get (by omega) (by omega)
  by_cases h28 : j < 734
  · exact kudstaticRange_704.get (by omega) (by omega)
  by_cases h29 : j < 764
  · exact kudstaticRange_734.get (by omega) (by omega)
  by_cases h30 : j < 794
  · exact kudstaticRange_764.get (by omega) (by omega)
  by_cases h31 : j < 824
  · exact kudstaticRange_794.get (by omega) (by omega)
  by_cases h32 : j < 854
  · exact kudstaticRange_824.get (by omega) (by omega)
  by_cases h33 : j < 884
  · exact kudstaticRange_854.get (by omega) (by omega)
  by_cases h34 : j < 914
  · exact kudstaticRange_884.get (by omega) (by omega)
  by_cases h35 : j < 944
  · exact kudstaticRange_914.get (by omega) (by omega)
  by_cases h36 : j < 974
  · exact kudstaticRange_944.get (by omega) (by omega)
  by_cases h37 : j < 1004
  · exact kudstaticRange_974.get (by omega) (by omega)
  by_cases h38 : j < 1034
  · exact kudstaticRange_1004.get (by omega) (by omega)
  by_cases h39 : j < 1064
  · exact kudstaticRange_1034.get (by omega) (by omega)
  by_cases h40 : j < 1094
  · exact kudstaticRange_1064.get (by omega) (by omega)
  by_cases h41 : j < 1124
  · exact kudstaticRange_1094.get (by omega) (by omega)
  by_cases h42 : j < 1154
  · exact kudstaticRange_1124.get (by omega) (by omega)
  by_cases h43 : j < 1184
  · exact kudstaticRange_1154.get (by omega) (by omega)
  by_cases h44 : j < 1214
  · exact kudstaticRange_1184.get (by omega) (by omega)
  by_cases h45 : j < 1244
  · exact kudstaticRange_1214.get (by omega) (by omega)
  by_cases h46 : j < 1274
  · exact kudstaticRange_1244.get (by omega) (by omega)
  by_cases h47 : j < 1304
  · exact kudstaticRange_1274.get (by omega) (by omega)
  by_cases h48 : j < 1334
  · exact kudstaticRange_1304.get (by omega) (by omega)
  by_cases h49 : j < 1364
  · exact kudstaticRange_1334.get (by omega) (by omega)
  by_cases h50 : j < 1394
  · exact kudstaticRange_1364.get (by omega) (by omega)
  by_cases h51 : j < 1424
  · exact kudstaticRange_1394.get (by omega) (by omega)
  by_cases h52 : j < 1454
  · exact kudstaticRange_1424.get (by omega) (by omega)
  by_cases h53 : j < 1484
  · exact kudstaticRange_1454.get (by omega) (by omega)
  by_cases h54 : j < 1514
  · exact kudstaticRange_1484.get (by omega) (by omega)
  by_cases h55 : j < 1544
  · exact kudstaticRange_1514.get (by omega) (by omega)
  by_cases h56 : j < 1574
  · exact kudstaticRange_1544.get (by omega) (by omega)
  exact kudstaticRange_1574.get (by omega) (by omega)

end
end LeanVM.Guest
