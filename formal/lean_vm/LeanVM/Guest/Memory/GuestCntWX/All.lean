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
public import LeanVM.Guest.Memory.GuestCntWX.Part07
public import LeanVM.Guest.Memory.GuestCntWX.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuxchkIdx_all : ∀ j < 1601, kuxchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kuxstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kuxstaticRange_128.get (by omega) (by omega)
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
  by_cases h13 : j < 338
  · exact kuxstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 341
  · exact kuxstaticRange_338.get (by omega) (by omega)
  by_cases h15 : j < 344
  · exact kuxstaticRange_341.get (by omega) (by omega)
  by_cases h16 : j < 374
  · exact kuxstaticRange_344.get (by omega) (by omega)
  by_cases h17 : j < 404
  · exact kuxstaticRange_374.get (by omega) (by omega)
  by_cases h18 : j < 434
  · exact kuxstaticRange_404.get (by omega) (by omega)
  by_cases h19 : j < 464
  · exact kuxstaticRange_434.get (by omega) (by omega)
  by_cases h20 : j < 494
  · exact kuxstaticRange_464.get (by omega) (by omega)
  by_cases h21 : j < 524
  · exact kuxstaticRange_494.get (by omega) (by omega)
  by_cases h22 : j < 554
  · exact kuxstaticRange_524.get (by omega) (by omega)
  by_cases h23 : j < 584
  · exact kuxstaticRange_554.get (by omega) (by omega)
  by_cases h24 : j < 614
  · exact kuxstaticRange_584.get (by omega) (by omega)
  by_cases h25 : j < 644
  · exact kuxstaticRange_614.get (by omega) (by omega)
  by_cases h26 : j < 674
  · exact kuxstaticRange_644.get (by omega) (by omega)
  by_cases h27 : j < 704
  · exact kuxstaticRange_674.get (by omega) (by omega)
  by_cases h28 : j < 734
  · exact kuxstaticRange_704.get (by omega) (by omega)
  by_cases h29 : j < 764
  · exact kuxstaticRange_734.get (by omega) (by omega)
  by_cases h30 : j < 794
  · exact kuxstaticRange_764.get (by omega) (by omega)
  by_cases h31 : j < 824
  · exact kuxstaticRange_794.get (by omega) (by omega)
  by_cases h32 : j < 854
  · exact kuxstaticRange_824.get (by omega) (by omega)
  by_cases h33 : j < 884
  · exact kuxstaticRange_854.get (by omega) (by omega)
  by_cases h34 : j < 914
  · exact kuxstaticRange_884.get (by omega) (by omega)
  by_cases h35 : j < 944
  · exact kuxstaticRange_914.get (by omega) (by omega)
  by_cases h36 : j < 974
  · exact kuxstaticRange_944.get (by omega) (by omega)
  by_cases h37 : j < 1004
  · exact kuxstaticRange_974.get (by omega) (by omega)
  by_cases h38 : j < 1034
  · exact kuxstaticRange_1004.get (by omega) (by omega)
  by_cases h39 : j < 1064
  · exact kuxstaticRange_1034.get (by omega) (by omega)
  by_cases h40 : j < 1094
  · exact kuxstaticRange_1064.get (by omega) (by omega)
  by_cases h41 : j < 1124
  · exact kuxstaticRange_1094.get (by omega) (by omega)
  by_cases h42 : j < 1154
  · exact kuxstaticRange_1124.get (by omega) (by omega)
  by_cases h43 : j < 1184
  · exact kuxstaticRange_1154.get (by omega) (by omega)
  by_cases h44 : j < 1214
  · exact kuxstaticRange_1184.get (by omega) (by omega)
  by_cases h45 : j < 1244
  · exact kuxstaticRange_1214.get (by omega) (by omega)
  by_cases h46 : j < 1274
  · exact kuxstaticRange_1244.get (by omega) (by omega)
  by_cases h47 : j < 1304
  · exact kuxstaticRange_1274.get (by omega) (by omega)
  by_cases h48 : j < 1334
  · exact kuxstaticRange_1304.get (by omega) (by omega)
  by_cases h49 : j < 1364
  · exact kuxstaticRange_1334.get (by omega) (by omega)
  by_cases h50 : j < 1394
  · exact kuxstaticRange_1364.get (by omega) (by omega)
  by_cases h51 : j < 1424
  · exact kuxstaticRange_1394.get (by omega) (by omega)
  by_cases h52 : j < 1454
  · exact kuxstaticRange_1424.get (by omega) (by omega)
  by_cases h53 : j < 1484
  · exact kuxstaticRange_1454.get (by omega) (by omega)
  by_cases h54 : j < 1514
  · exact kuxstaticRange_1484.get (by omega) (by omega)
  by_cases h55 : j < 1544
  · exact kuxstaticRange_1514.get (by omega) (by omega)
  by_cases h56 : j < 1574
  · exact kuxstaticRange_1544.get (by omega) (by omega)
  exact kuxstaticRange_1574.get (by omega) (by omega)

end
end LeanVM.Guest
