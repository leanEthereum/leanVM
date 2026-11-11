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
public import LeanVM.Guest.Memory.GuestCntWJ.Part09

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kujchkIdx_all : ∀ j < 1752, kujchkIdx j = true := by
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
  by_cases h6 : j < 155
  · exact kujstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kujstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kujstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kujstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 258
  · exact kujstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kujstaticRange_258.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kujstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kujstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kujstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kujstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 351
  · exact kujstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 381
  · exact kujstaticRange_351.get (by omega) (by omega)
  by_cases h18 : j < 411
  · exact kujstaticRange_381.get (by omega) (by omega)
  by_cases h19 : j < 441
  · exact kujstaticRange_411.get (by omega) (by omega)
  by_cases h20 : j < 471
  · exact kujstaticRange_441.get (by omega) (by omega)
  by_cases h21 : j < 501
  · exact kujstaticRange_471.get (by omega) (by omega)
  by_cases h22 : j < 531
  · exact kujstaticRange_501.get (by omega) (by omega)
  by_cases h23 : j < 561
  · exact kujstaticRange_531.get (by omega) (by omega)
  by_cases h24 : j < 591
  · exact kujstaticRange_561.get (by omega) (by omega)
  by_cases h25 : j < 621
  · exact kujstaticRange_591.get (by omega) (by omega)
  by_cases h26 : j < 651
  · exact kujstaticRange_621.get (by omega) (by omega)
  by_cases h27 : j < 681
  · exact kujstaticRange_651.get (by omega) (by omega)
  by_cases h28 : j < 711
  · exact kujstaticRange_681.get (by omega) (by omega)
  by_cases h29 : j < 741
  · exact kujstaticRange_711.get (by omega) (by omega)
  by_cases h30 : j < 771
  · exact kujstaticRange_741.get (by omega) (by omega)
  by_cases h31 : j < 801
  · exact kujstaticRange_771.get (by omega) (by omega)
  by_cases h32 : j < 831
  · exact kujstaticRange_801.get (by omega) (by omega)
  by_cases h33 : j < 861
  · exact kujstaticRange_831.get (by omega) (by omega)
  by_cases h34 : j < 891
  · exact kujstaticRange_861.get (by omega) (by omega)
  by_cases h35 : j < 921
  · exact kujstaticRange_891.get (by omega) (by omega)
  by_cases h36 : j < 951
  · exact kujstaticRange_921.get (by omega) (by omega)
  by_cases h37 : j < 981
  · exact kujstaticRange_951.get (by omega) (by omega)
  by_cases h38 : j < 1011
  · exact kujstaticRange_981.get (by omega) (by omega)
  by_cases h39 : j < 1041
  · exact kujstaticRange_1011.get (by omega) (by omega)
  by_cases h40 : j < 1071
  · exact kujstaticRange_1041.get (by omega) (by omega)
  by_cases h41 : j < 1101
  · exact kujstaticRange_1071.get (by omega) (by omega)
  by_cases h42 : j < 1131
  · exact kujstaticRange_1101.get (by omega) (by omega)
  by_cases h43 : j < 1161
  · exact kujstaticRange_1131.get (by omega) (by omega)
  by_cases h44 : j < 1191
  · exact kujstaticRange_1161.get (by omega) (by omega)
  by_cases h45 : j < 1221
  · exact kujstaticRange_1191.get (by omega) (by omega)
  by_cases h46 : j < 1251
  · exact kujstaticRange_1221.get (by omega) (by omega)
  by_cases h47 : j < 1281
  · exact kujstaticRange_1251.get (by omega) (by omega)
  by_cases h48 : j < 1311
  · exact kujstaticRange_1281.get (by omega) (by omega)
  by_cases h49 : j < 1341
  · exact kujstaticRange_1311.get (by omega) (by omega)
  by_cases h50 : j < 1371
  · exact kujstaticRange_1341.get (by omega) (by omega)
  by_cases h51 : j < 1401
  · exact kujstaticRange_1371.get (by omega) (by omega)
  by_cases h52 : j < 1431
  · exact kujstaticRange_1401.get (by omega) (by omega)
  by_cases h53 : j < 1461
  · exact kujstaticRange_1431.get (by omega) (by omega)
  by_cases h54 : j < 1491
  · exact kujstaticRange_1461.get (by omega) (by omega)
  by_cases h55 : j < 1521
  · exact kujstaticRange_1491.get (by omega) (by omega)
  by_cases h56 : j < 1551
  · exact kujstaticRange_1521.get (by omega) (by omega)
  by_cases h57 : j < 1581
  · exact kujstaticRange_1551.get (by omega) (by omega)
  by_cases h58 : j < 1611
  · exact kujstaticRange_1581.get (by omega) (by omega)
  by_cases h59 : j < 1641
  · exact kujstaticRange_1611.get (by omega) (by omega)
  by_cases h60 : j < 1671
  · exact kujstaticRange_1641.get (by omega) (by omega)
  by_cases h61 : j < 1701
  · exact kujstaticRange_1671.get (by omega) (by omega)
  by_cases h62 : j < 1731
  · exact kujstaticRange_1701.get (by omega) (by omega)
  exact kujstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
