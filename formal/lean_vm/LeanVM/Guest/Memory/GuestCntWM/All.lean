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
public import LeanVM.Guest.Memory.GuestCntWM.Part07
public import LeanVM.Guest.Memory.GuestCntWM.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kumchkIdx_all : ∀ j < 1601, kumchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kumstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kumstaticRange_128.get (by omega) (by omega)
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
  by_cases h13 : j < 338
  · exact kumstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 341
  · exact kumstaticRange_338.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kumstaticRange_341.get (by omega) (by omega)
  by_cases h16 : j < 374
  · exact kumstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 404
  · exact kumstaticRange_374.get (by omega) (by omega)
  by_cases h18 : j < 434
  · exact kumstaticRange_404.get (by omega) (by omega)
  by_cases h19 : j < 464
  · exact kumstaticRange_434.get (by omega) (by omega)
  by_cases h20 : j < 494
  · exact kumstaticRange_464.get (by omega) (by omega)
  by_cases h21 : j < 524
  · exact kumstaticRange_494.get (by omega) (by omega)
  by_cases h22 : j < 554
  · exact kumstaticRange_524.get (by omega) (by omega)
  by_cases h23 : j < 584
  · exact kumstaticRange_554.get (by omega) (by omega)
  by_cases h24 : j < 614
  · exact kumstaticRange_584.get (by omega) (by omega)
  by_cases h25 : j < 644
  · exact kumstaticRange_614.get (by omega) (by omega)
  by_cases h26 : j < 674
  · exact kumstaticRange_644.get (by omega) (by omega)
  by_cases h27 : j < 704
  · exact kumstaticRange_674.get (by omega) (by omega)
  by_cases h28 : j < 734
  · exact kumstaticRange_704.get (by omega) (by omega)
  by_cases h29 : j < 764
  · exact kumstaticRange_734.get (by omega) (by omega)
  by_cases h30 : j < 794
  · exact kumstaticRange_764.get (by omega) (by omega)
  by_cases h31 : j < 824
  · exact kumstaticRange_794.get (by omega) (by omega)
  by_cases h32 : j < 854
  · exact kumstaticRange_824.get (by omega) (by omega)
  by_cases h33 : j < 884
  · exact kumstaticRange_854.get (by omega) (by omega)
  by_cases h34 : j < 914
  · exact kumstaticRange_884.get (by omega) (by omega)
  by_cases h35 : j < 944
  · exact kumstaticRange_914.get (by omega) (by omega)
  by_cases h36 : j < 974
  · exact kumstaticRange_944.get (by omega) (by omega)
  by_cases h37 : j < 1004
  · exact kumstaticRange_974.get (by omega) (by omega)
  by_cases h38 : j < 1034
  · exact kumstaticRange_1004.get (by omega) (by omega)
  by_cases h39 : j < 1064
  · exact kumstaticRange_1034.get (by omega) (by omega)
  by_cases h40 : j < 1094
  · exact kumstaticRange_1064.get (by omega) (by omega)
  by_cases h41 : j < 1124
  · exact kumstaticRange_1094.get (by omega) (by omega)
  by_cases h42 : j < 1154
  · exact kumstaticRange_1124.get (by omega) (by omega)
  by_cases h43 : j < 1184
  · exact kumstaticRange_1154.get (by omega) (by omega)
  by_cases h44 : j < 1214
  · exact kumstaticRange_1184.get (by omega) (by omega)
  by_cases h45 : j < 1244
  · exact kumstaticRange_1214.get (by omega) (by omega)
  by_cases h46 : j < 1274
  · exact kumstaticRange_1244.get (by omega) (by omega)
  by_cases h47 : j < 1304
  · exact kumstaticRange_1274.get (by omega) (by omega)
  by_cases h48 : j < 1334
  · exact kumstaticRange_1304.get (by omega) (by omega)
  by_cases h49 : j < 1364
  · exact kumstaticRange_1334.get (by omega) (by omega)
  by_cases h50 : j < 1394
  · exact kumstaticRange_1364.get (by omega) (by omega)
  by_cases h51 : j < 1424
  · exact kumstaticRange_1394.get (by omega) (by omega)
  by_cases h52 : j < 1454
  · exact kumstaticRange_1424.get (by omega) (by omega)
  by_cases h53 : j < 1484
  · exact kumstaticRange_1454.get (by omega) (by omega)
  by_cases h54 : j < 1514
  · exact kumstaticRange_1484.get (by omega) (by omega)
  by_cases h55 : j < 1544
  · exact kumstaticRange_1514.get (by omega) (by omega)
  by_cases h56 : j < 1574
  · exact kumstaticRange_1544.get (by omega) (by omega)
  exact kumstaticRange_1574.get (by omega) (by omega)

end
end LeanVM.Guest
