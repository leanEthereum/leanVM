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
public import LeanVM.Guest.Memory.GuestCntWD.Part09

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kudchkIdx_all : ∀ j < 1752, kudchkIdx j = true := by
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
  by_cases h6 : j < 155
  · exact kudstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kudstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kudstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kudstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 258
  · exact kudstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kudstaticRange_258.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kudstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kudstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kudstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kudstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 351
  · exact kudstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 381
  · exact kudstaticRange_351.get (by omega) (by omega)
  by_cases h18 : j < 411
  · exact kudstaticRange_381.get (by omega) (by omega)
  by_cases h19 : j < 441
  · exact kudstaticRange_411.get (by omega) (by omega)
  by_cases h20 : j < 471
  · exact kudstaticRange_441.get (by omega) (by omega)
  by_cases h21 : j < 501
  · exact kudstaticRange_471.get (by omega) (by omega)
  by_cases h22 : j < 531
  · exact kudstaticRange_501.get (by omega) (by omega)
  by_cases h23 : j < 561
  · exact kudstaticRange_531.get (by omega) (by omega)
  by_cases h24 : j < 591
  · exact kudstaticRange_561.get (by omega) (by omega)
  by_cases h25 : j < 621
  · exact kudstaticRange_591.get (by omega) (by omega)
  by_cases h26 : j < 651
  · exact kudstaticRange_621.get (by omega) (by omega)
  by_cases h27 : j < 681
  · exact kudstaticRange_651.get (by omega) (by omega)
  by_cases h28 : j < 711
  · exact kudstaticRange_681.get (by omega) (by omega)
  by_cases h29 : j < 741
  · exact kudstaticRange_711.get (by omega) (by omega)
  by_cases h30 : j < 771
  · exact kudstaticRange_741.get (by omega) (by omega)
  by_cases h31 : j < 801
  · exact kudstaticRange_771.get (by omega) (by omega)
  by_cases h32 : j < 831
  · exact kudstaticRange_801.get (by omega) (by omega)
  by_cases h33 : j < 861
  · exact kudstaticRange_831.get (by omega) (by omega)
  by_cases h34 : j < 891
  · exact kudstaticRange_861.get (by omega) (by omega)
  by_cases h35 : j < 921
  · exact kudstaticRange_891.get (by omega) (by omega)
  by_cases h36 : j < 951
  · exact kudstaticRange_921.get (by omega) (by omega)
  by_cases h37 : j < 981
  · exact kudstaticRange_951.get (by omega) (by omega)
  by_cases h38 : j < 1011
  · exact kudstaticRange_981.get (by omega) (by omega)
  by_cases h39 : j < 1041
  · exact kudstaticRange_1011.get (by omega) (by omega)
  by_cases h40 : j < 1071
  · exact kudstaticRange_1041.get (by omega) (by omega)
  by_cases h41 : j < 1101
  · exact kudstaticRange_1071.get (by omega) (by omega)
  by_cases h42 : j < 1131
  · exact kudstaticRange_1101.get (by omega) (by omega)
  by_cases h43 : j < 1161
  · exact kudstaticRange_1131.get (by omega) (by omega)
  by_cases h44 : j < 1191
  · exact kudstaticRange_1161.get (by omega) (by omega)
  by_cases h45 : j < 1221
  · exact kudstaticRange_1191.get (by omega) (by omega)
  by_cases h46 : j < 1251
  · exact kudstaticRange_1221.get (by omega) (by omega)
  by_cases h47 : j < 1281
  · exact kudstaticRange_1251.get (by omega) (by omega)
  by_cases h48 : j < 1311
  · exact kudstaticRange_1281.get (by omega) (by omega)
  by_cases h49 : j < 1341
  · exact kudstaticRange_1311.get (by omega) (by omega)
  by_cases h50 : j < 1371
  · exact kudstaticRange_1341.get (by omega) (by omega)
  by_cases h51 : j < 1401
  · exact kudstaticRange_1371.get (by omega) (by omega)
  by_cases h52 : j < 1431
  · exact kudstaticRange_1401.get (by omega) (by omega)
  by_cases h53 : j < 1461
  · exact kudstaticRange_1431.get (by omega) (by omega)
  by_cases h54 : j < 1491
  · exact kudstaticRange_1461.get (by omega) (by omega)
  by_cases h55 : j < 1521
  · exact kudstaticRange_1491.get (by omega) (by omega)
  by_cases h56 : j < 1551
  · exact kudstaticRange_1521.get (by omega) (by omega)
  by_cases h57 : j < 1581
  · exact kudstaticRange_1551.get (by omega) (by omega)
  by_cases h58 : j < 1611
  · exact kudstaticRange_1581.get (by omega) (by omega)
  by_cases h59 : j < 1641
  · exact kudstaticRange_1611.get (by omega) (by omega)
  by_cases h60 : j < 1671
  · exact kudstaticRange_1641.get (by omega) (by omega)
  by_cases h61 : j < 1701
  · exact kudstaticRange_1671.get (by omega) (by omega)
  by_cases h62 : j < 1731
  · exact kudstaticRange_1701.get (by omega) (by omega)
  exact kudstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
