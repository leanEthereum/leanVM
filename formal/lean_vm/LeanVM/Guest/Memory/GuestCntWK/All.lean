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
public import LeanVM.Guest.Memory.GuestCntWK.Part07
public import LeanVM.Guest.Memory.GuestCntWK.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 1601, kukchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kukstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kukstaticRange_128.get (by omega) (by omega)
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
  by_cases h13 : j < 338
  · exact kukstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 341
  · exact kukstaticRange_338.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kukstaticRange_341.get (by omega) (by omega)
  by_cases h16 : j < 374
  · exact kukstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 404
  · exact kukstaticRange_374.get (by omega) (by omega)
  by_cases h18 : j < 434
  · exact kukstaticRange_404.get (by omega) (by omega)
  by_cases h19 : j < 464
  · exact kukstaticRange_434.get (by omega) (by omega)
  by_cases h20 : j < 494
  · exact kukstaticRange_464.get (by omega) (by omega)
  by_cases h21 : j < 524
  · exact kukstaticRange_494.get (by omega) (by omega)
  by_cases h22 : j < 554
  · exact kukstaticRange_524.get (by omega) (by omega)
  by_cases h23 : j < 584
  · exact kukstaticRange_554.get (by omega) (by omega)
  by_cases h24 : j < 614
  · exact kukstaticRange_584.get (by omega) (by omega)
  by_cases h25 : j < 644
  · exact kukstaticRange_614.get (by omega) (by omega)
  by_cases h26 : j < 674
  · exact kukstaticRange_644.get (by omega) (by omega)
  by_cases h27 : j < 704
  · exact kukstaticRange_674.get (by omega) (by omega)
  by_cases h28 : j < 734
  · exact kukstaticRange_704.get (by omega) (by omega)
  by_cases h29 : j < 764
  · exact kukstaticRange_734.get (by omega) (by omega)
  by_cases h30 : j < 794
  · exact kukstaticRange_764.get (by omega) (by omega)
  by_cases h31 : j < 824
  · exact kukstaticRange_794.get (by omega) (by omega)
  by_cases h32 : j < 854
  · exact kukstaticRange_824.get (by omega) (by omega)
  by_cases h33 : j < 884
  · exact kukstaticRange_854.get (by omega) (by omega)
  by_cases h34 : j < 914
  · exact kukstaticRange_884.get (by omega) (by omega)
  by_cases h35 : j < 944
  · exact kukstaticRange_914.get (by omega) (by omega)
  by_cases h36 : j < 974
  · exact kukstaticRange_944.get (by omega) (by omega)
  by_cases h37 : j < 1004
  · exact kukstaticRange_974.get (by omega) (by omega)
  by_cases h38 : j < 1034
  · exact kukstaticRange_1004.get (by omega) (by omega)
  by_cases h39 : j < 1064
  · exact kukstaticRange_1034.get (by omega) (by omega)
  by_cases h40 : j < 1094
  · exact kukstaticRange_1064.get (by omega) (by omega)
  by_cases h41 : j < 1124
  · exact kukstaticRange_1094.get (by omega) (by omega)
  by_cases h42 : j < 1154
  · exact kukstaticRange_1124.get (by omega) (by omega)
  by_cases h43 : j < 1184
  · exact kukstaticRange_1154.get (by omega) (by omega)
  by_cases h44 : j < 1214
  · exact kukstaticRange_1184.get (by omega) (by omega)
  by_cases h45 : j < 1244
  · exact kukstaticRange_1214.get (by omega) (by omega)
  by_cases h46 : j < 1274
  · exact kukstaticRange_1244.get (by omega) (by omega)
  by_cases h47 : j < 1304
  · exact kukstaticRange_1274.get (by omega) (by omega)
  by_cases h48 : j < 1334
  · exact kukstaticRange_1304.get (by omega) (by omega)
  by_cases h49 : j < 1364
  · exact kukstaticRange_1334.get (by omega) (by omega)
  by_cases h50 : j < 1394
  · exact kukstaticRange_1364.get (by omega) (by omega)
  by_cases h51 : j < 1424
  · exact kukstaticRange_1394.get (by omega) (by omega)
  by_cases h52 : j < 1454
  · exact kukstaticRange_1424.get (by omega) (by omega)
  by_cases h53 : j < 1484
  · exact kukstaticRange_1454.get (by omega) (by omega)
  by_cases h54 : j < 1514
  · exact kukstaticRange_1484.get (by omega) (by omega)
  by_cases h55 : j < 1544
  · exact kukstaticRange_1514.get (by omega) (by omega)
  by_cases h56 : j < 1574
  · exact kukstaticRange_1544.get (by omega) (by omega)
  exact kukstaticRange_1574.get (by omega) (by omega)

end
end LeanVM.Guest
