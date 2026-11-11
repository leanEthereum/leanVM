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
public import LeanVM.Guest.Memory.GuestCntWX.Part09

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuxchkIdx_all : ∀ j < 1752, kuxchkIdx j = true := by
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
  by_cases h6 : j < 155
  · exact kuxstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kuxstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kuxstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kuxstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 258
  · exact kuxstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kuxstaticRange_258.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kuxstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kuxstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kuxstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kuxstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 351
  · exact kuxstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 381
  · exact kuxstaticRange_351.get (by omega) (by omega)
  by_cases h18 : j < 411
  · exact kuxstaticRange_381.get (by omega) (by omega)
  by_cases h19 : j < 441
  · exact kuxstaticRange_411.get (by omega) (by omega)
  by_cases h20 : j < 471
  · exact kuxstaticRange_441.get (by omega) (by omega)
  by_cases h21 : j < 501
  · exact kuxstaticRange_471.get (by omega) (by omega)
  by_cases h22 : j < 531
  · exact kuxstaticRange_501.get (by omega) (by omega)
  by_cases h23 : j < 561
  · exact kuxstaticRange_531.get (by omega) (by omega)
  by_cases h24 : j < 591
  · exact kuxstaticRange_561.get (by omega) (by omega)
  by_cases h25 : j < 621
  · exact kuxstaticRange_591.get (by omega) (by omega)
  by_cases h26 : j < 651
  · exact kuxstaticRange_621.get (by omega) (by omega)
  by_cases h27 : j < 681
  · exact kuxstaticRange_651.get (by omega) (by omega)
  by_cases h28 : j < 711
  · exact kuxstaticRange_681.get (by omega) (by omega)
  by_cases h29 : j < 741
  · exact kuxstaticRange_711.get (by omega) (by omega)
  by_cases h30 : j < 771
  · exact kuxstaticRange_741.get (by omega) (by omega)
  by_cases h31 : j < 801
  · exact kuxstaticRange_771.get (by omega) (by omega)
  by_cases h32 : j < 831
  · exact kuxstaticRange_801.get (by omega) (by omega)
  by_cases h33 : j < 861
  · exact kuxstaticRange_831.get (by omega) (by omega)
  by_cases h34 : j < 891
  · exact kuxstaticRange_861.get (by omega) (by omega)
  by_cases h35 : j < 921
  · exact kuxstaticRange_891.get (by omega) (by omega)
  by_cases h36 : j < 951
  · exact kuxstaticRange_921.get (by omega) (by omega)
  by_cases h37 : j < 981
  · exact kuxstaticRange_951.get (by omega) (by omega)
  by_cases h38 : j < 1011
  · exact kuxstaticRange_981.get (by omega) (by omega)
  by_cases h39 : j < 1041
  · exact kuxstaticRange_1011.get (by omega) (by omega)
  by_cases h40 : j < 1071
  · exact kuxstaticRange_1041.get (by omega) (by omega)
  by_cases h41 : j < 1101
  · exact kuxstaticRange_1071.get (by omega) (by omega)
  by_cases h42 : j < 1131
  · exact kuxstaticRange_1101.get (by omega) (by omega)
  by_cases h43 : j < 1161
  · exact kuxstaticRange_1131.get (by omega) (by omega)
  by_cases h44 : j < 1191
  · exact kuxstaticRange_1161.get (by omega) (by omega)
  by_cases h45 : j < 1221
  · exact kuxstaticRange_1191.get (by omega) (by omega)
  by_cases h46 : j < 1251
  · exact kuxstaticRange_1221.get (by omega) (by omega)
  by_cases h47 : j < 1281
  · exact kuxstaticRange_1251.get (by omega) (by omega)
  by_cases h48 : j < 1311
  · exact kuxstaticRange_1281.get (by omega) (by omega)
  by_cases h49 : j < 1341
  · exact kuxstaticRange_1311.get (by omega) (by omega)
  by_cases h50 : j < 1371
  · exact kuxstaticRange_1341.get (by omega) (by omega)
  by_cases h51 : j < 1401
  · exact kuxstaticRange_1371.get (by omega) (by omega)
  by_cases h52 : j < 1431
  · exact kuxstaticRange_1401.get (by omega) (by omega)
  by_cases h53 : j < 1461
  · exact kuxstaticRange_1431.get (by omega) (by omega)
  by_cases h54 : j < 1491
  · exact kuxstaticRange_1461.get (by omega) (by omega)
  by_cases h55 : j < 1521
  · exact kuxstaticRange_1491.get (by omega) (by omega)
  by_cases h56 : j < 1551
  · exact kuxstaticRange_1521.get (by omega) (by omega)
  by_cases h57 : j < 1581
  · exact kuxstaticRange_1551.get (by omega) (by omega)
  by_cases h58 : j < 1611
  · exact kuxstaticRange_1581.get (by omega) (by omega)
  by_cases h59 : j < 1641
  · exact kuxstaticRange_1611.get (by omega) (by omega)
  by_cases h60 : j < 1671
  · exact kuxstaticRange_1641.get (by omega) (by omega)
  by_cases h61 : j < 1701
  · exact kuxstaticRange_1671.get (by omega) (by omega)
  by_cases h62 : j < 1731
  · exact kuxstaticRange_1701.get (by omega) (by omega)
  exact kuxstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
