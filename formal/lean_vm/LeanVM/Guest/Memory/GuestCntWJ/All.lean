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
public import LeanVM.Guest.Memory.GuestCntWJ.Part07
public import LeanVM.Guest.Memory.GuestCntWJ.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kujchkIdx_all : ∀ j < 1601, kujchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kujstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kujstaticRange_128.get (by omega) (by omega)
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
  by_cases h13 : j < 338
  · exact kujstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 341
  · exact kujstaticRange_338.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kujstaticRange_341.get (by omega) (by omega)
  by_cases h16 : j < 374
  · exact kujstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 404
  · exact kujstaticRange_374.get (by omega) (by omega)
  by_cases h18 : j < 434
  · exact kujstaticRange_404.get (by omega) (by omega)
  by_cases h19 : j < 464
  · exact kujstaticRange_434.get (by omega) (by omega)
  by_cases h20 : j < 494
  · exact kujstaticRange_464.get (by omega) (by omega)
  by_cases h21 : j < 524
  · exact kujstaticRange_494.get (by omega) (by omega)
  by_cases h22 : j < 554
  · exact kujstaticRange_524.get (by omega) (by omega)
  by_cases h23 : j < 584
  · exact kujstaticRange_554.get (by omega) (by omega)
  by_cases h24 : j < 614
  · exact kujstaticRange_584.get (by omega) (by omega)
  by_cases h25 : j < 644
  · exact kujstaticRange_614.get (by omega) (by omega)
  by_cases h26 : j < 674
  · exact kujstaticRange_644.get (by omega) (by omega)
  by_cases h27 : j < 704
  · exact kujstaticRange_674.get (by omega) (by omega)
  by_cases h28 : j < 734
  · exact kujstaticRange_704.get (by omega) (by omega)
  by_cases h29 : j < 764
  · exact kujstaticRange_734.get (by omega) (by omega)
  by_cases h30 : j < 794
  · exact kujstaticRange_764.get (by omega) (by omega)
  by_cases h31 : j < 824
  · exact kujstaticRange_794.get (by omega) (by omega)
  by_cases h32 : j < 854
  · exact kujstaticRange_824.get (by omega) (by omega)
  by_cases h33 : j < 884
  · exact kujstaticRange_854.get (by omega) (by omega)
  by_cases h34 : j < 914
  · exact kujstaticRange_884.get (by omega) (by omega)
  by_cases h35 : j < 944
  · exact kujstaticRange_914.get (by omega) (by omega)
  by_cases h36 : j < 974
  · exact kujstaticRange_944.get (by omega) (by omega)
  by_cases h37 : j < 1004
  · exact kujstaticRange_974.get (by omega) (by omega)
  by_cases h38 : j < 1034
  · exact kujstaticRange_1004.get (by omega) (by omega)
  by_cases h39 : j < 1064
  · exact kujstaticRange_1034.get (by omega) (by omega)
  by_cases h40 : j < 1094
  · exact kujstaticRange_1064.get (by omega) (by omega)
  by_cases h41 : j < 1124
  · exact kujstaticRange_1094.get (by omega) (by omega)
  by_cases h42 : j < 1154
  · exact kujstaticRange_1124.get (by omega) (by omega)
  by_cases h43 : j < 1184
  · exact kujstaticRange_1154.get (by omega) (by omega)
  by_cases h44 : j < 1214
  · exact kujstaticRange_1184.get (by omega) (by omega)
  by_cases h45 : j < 1244
  · exact kujstaticRange_1214.get (by omega) (by omega)
  by_cases h46 : j < 1274
  · exact kujstaticRange_1244.get (by omega) (by omega)
  by_cases h47 : j < 1304
  · exact kujstaticRange_1274.get (by omega) (by omega)
  by_cases h48 : j < 1334
  · exact kujstaticRange_1304.get (by omega) (by omega)
  by_cases h49 : j < 1364
  · exact kujstaticRange_1334.get (by omega) (by omega)
  by_cases h50 : j < 1394
  · exact kujstaticRange_1364.get (by omega) (by omega)
  by_cases h51 : j < 1424
  · exact kujstaticRange_1394.get (by omega) (by omega)
  by_cases h52 : j < 1454
  · exact kujstaticRange_1424.get (by omega) (by omega)
  by_cases h53 : j < 1484
  · exact kujstaticRange_1454.get (by omega) (by omega)
  by_cases h54 : j < 1514
  · exact kujstaticRange_1484.get (by omega) (by omega)
  by_cases h55 : j < 1544
  · exact kujstaticRange_1514.get (by omega) (by omega)
  by_cases h56 : j < 1574
  · exact kujstaticRange_1544.get (by omega) (by omega)
  exact kujstaticRange_1574.get (by omega) (by omega)

end
end LeanVM.Guest
