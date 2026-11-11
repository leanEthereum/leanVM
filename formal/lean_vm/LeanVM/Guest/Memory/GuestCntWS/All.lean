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
public import LeanVM.Guest.Memory.GuestCntWS.Part07
public import LeanVM.Guest.Memory.GuestCntWS.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuschkIdx_all : ∀ j < 1601, kuschkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kusstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kusstaticRange_128.get (by omega) (by omega)
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
  by_cases h13 : j < 338
  · exact kusstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 341
  · exact kusstaticRange_338.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kusstaticRange_341.get (by omega) (by omega)
  by_cases h16 : j < 374
  · exact kusstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 404
  · exact kusstaticRange_374.get (by omega) (by omega)
  by_cases h18 : j < 434
  · exact kusstaticRange_404.get (by omega) (by omega)
  by_cases h19 : j < 464
  · exact kusstaticRange_434.get (by omega) (by omega)
  by_cases h20 : j < 494
  · exact kusstaticRange_464.get (by omega) (by omega)
  by_cases h21 : j < 524
  · exact kusstaticRange_494.get (by omega) (by omega)
  by_cases h22 : j < 554
  · exact kusstaticRange_524.get (by omega) (by omega)
  by_cases h23 : j < 584
  · exact kusstaticRange_554.get (by omega) (by omega)
  by_cases h24 : j < 614
  · exact kusstaticRange_584.get (by omega) (by omega)
  by_cases h25 : j < 644
  · exact kusstaticRange_614.get (by omega) (by omega)
  by_cases h26 : j < 674
  · exact kusstaticRange_644.get (by omega) (by omega)
  by_cases h27 : j < 704
  · exact kusstaticRange_674.get (by omega) (by omega)
  by_cases h28 : j < 734
  · exact kusstaticRange_704.get (by omega) (by omega)
  by_cases h29 : j < 764
  · exact kusstaticRange_734.get (by omega) (by omega)
  by_cases h30 : j < 794
  · exact kusstaticRange_764.get (by omega) (by omega)
  by_cases h31 : j < 824
  · exact kusstaticRange_794.get (by omega) (by omega)
  by_cases h32 : j < 854
  · exact kusstaticRange_824.get (by omega) (by omega)
  by_cases h33 : j < 884
  · exact kusstaticRange_854.get (by omega) (by omega)
  by_cases h34 : j < 914
  · exact kusstaticRange_884.get (by omega) (by omega)
  by_cases h35 : j < 944
  · exact kusstaticRange_914.get (by omega) (by omega)
  by_cases h36 : j < 974
  · exact kusstaticRange_944.get (by omega) (by omega)
  by_cases h37 : j < 1004
  · exact kusstaticRange_974.get (by omega) (by omega)
  by_cases h38 : j < 1034
  · exact kusstaticRange_1004.get (by omega) (by omega)
  by_cases h39 : j < 1064
  · exact kusstaticRange_1034.get (by omega) (by omega)
  by_cases h40 : j < 1094
  · exact kusstaticRange_1064.get (by omega) (by omega)
  by_cases h41 : j < 1124
  · exact kusstaticRange_1094.get (by omega) (by omega)
  by_cases h42 : j < 1154
  · exact kusstaticRange_1124.get (by omega) (by omega)
  by_cases h43 : j < 1184
  · exact kusstaticRange_1154.get (by omega) (by omega)
  by_cases h44 : j < 1214
  · exact kusstaticRange_1184.get (by omega) (by omega)
  by_cases h45 : j < 1244
  · exact kusstaticRange_1214.get (by omega) (by omega)
  by_cases h46 : j < 1274
  · exact kusstaticRange_1244.get (by omega) (by omega)
  by_cases h47 : j < 1304
  · exact kusstaticRange_1274.get (by omega) (by omega)
  by_cases h48 : j < 1334
  · exact kusstaticRange_1304.get (by omega) (by omega)
  by_cases h49 : j < 1364
  · exact kusstaticRange_1334.get (by omega) (by omega)
  by_cases h50 : j < 1394
  · exact kusstaticRange_1364.get (by omega) (by omega)
  by_cases h51 : j < 1424
  · exact kusstaticRange_1394.get (by omega) (by omega)
  by_cases h52 : j < 1454
  · exact kusstaticRange_1424.get (by omega) (by omega)
  by_cases h53 : j < 1484
  · exact kusstaticRange_1454.get (by omega) (by omega)
  by_cases h54 : j < 1514
  · exact kusstaticRange_1484.get (by omega) (by omega)
  by_cases h55 : j < 1544
  · exact kusstaticRange_1514.get (by omega) (by omega)
  by_cases h56 : j < 1574
  · exact kusstaticRange_1544.get (by omega) (by omega)
  exact kusstaticRange_1574.get (by omega) (by omega)

end
end LeanVM.Guest
